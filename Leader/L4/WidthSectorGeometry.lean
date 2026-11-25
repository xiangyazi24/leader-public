import Leader.L4.WidthWaitDrain
import Leader.L4.ShortLayerGeometry
import Leader.L4.RearGeometry

namespace L4.WidthSectorGeometry
open AllSizeProtocol ShortResetChart ShortLayerGeometry WidthWaitDrain

/-- One whole sector includes its leading root and d interior sites.
The following root is outside the sector. -/
structure Sector {n : Nat} (h : Fin n→Bool) (d : Nat) where
  root : Fin n
  here : h root=true
  gap : Gap h root (d+1)
  room : d+1<n

def site {n d : Nat} {h : Fin n→Bool} (S : Sector h d) (i : Fin (d+1)) : Fin n :=
  nextAt S.root i.val

def inlet {n d : Nat} {h : Fin n→Bool} (S : Sector h d) : Fin n :=
  RearTrace.predecessor S.root

theorem site_injective {n d : Nat} {h : Fin n→Bool} (S : Sector h d)
    {i j : Fin (d+1)} (E : site S i=site S j) : i=j := by
  apply Fin.ext
  have D := S.room
  exact nextAt_injective_under S.root _ _ (Nat.lt_trans i.isLt D)
    (Nat.lt_trans j.isLt D) E

theorem inlet_not_site {n d : Nat} {h : Fin n→Bool} (S : Sector h d) (i : Fin (d+1)) :
    inlet S ≠ site S i := by
  intro E
  have R : rightNeighbor (inlet S)=S.root := RearTrace.right_predecessor _
  rw [E] at R
  have H : nextAt S.root (i.val+1)=nextAt S.root 0 := R
  have D := S.room
  have J := i.isLt
  have V := nextAt_injective_under S.root _ _ (by omega) (by omega) H
  omega

theorem internal_right {n d : Nat} {h : Fin n→Bool} (S : Sector h d) (i : Fin d) :
    rightNeighbor (site S (west i))=site S (east i) := rfl

theorem internal_nonheader {n d : Nat} {h : Fin n→Bool} (S : Sector h d) (i : Fin d) :
    h (site S (east i))=false :=
  S.gap.interior (i.val+1) (by omega) (by have := i.isLt; omega)

theorem outgoing_header {n d : Nat} {h : Fin n→Bool} (S : Sector h d) :
    h (rightNeighbor (site S (last d)))=true := S.gap.atEnd

theorem incoming_header {n d : Nat} {h : Fin n→Bool} (S : Sector h d) :
    h (rightNeighbor (inlet S))=true := by
  rw [inlet,RearTrace.right_predecessor]
  exact S.here

theorem inlet_eq {n d : Nat} {h : Fin n→Bool} (S : Sector h d) :
    rightNeighbor (inlet S)=site S 0 := RearTrace.right_predecessor _

/-- The only edges that can touch the sector are the incoming edge
and edges whose initiator is in the sector. -/
theorem incident {n d : Nat} {h : Fin n→Bool} (S : Sector h d) (e : Fin n)
    (j : Fin (d+1)) (E : rightNeighbor e=site S j) :
    e=inlet S ∨ ∃ k : Fin d, e=site S (west k) := by
  by_cases Z : j.val=0
  · left
    have V : j=0 := Fin.ext Z
    rw [V,←inlet_eq] at E
    exact (RearTrace.predecessor_right e).symm.trans
      ((congrArg RearTrace.predecessor E).trans (RearTrace.predecessor_right _))
  · right
    let k : Fin d := ⟨j.val-1,by have := j.isLt; omega⟩
    have K : east k=j := Fin.ext (by change j.val-1+1=j.val; omega)
    have X : rightNeighbor e=rightNeighbor (site S (west k)) := by
      rw [internal_right,K,E]
    exact ⟨k,(RearTrace.predecessor_right e).symm.trans
      ((congrArg RearTrace.predecessor X).trans (RearTrace.predecessor_right _))⟩

theorem outbound_not_site {n d : Nat} {h : Fin n→Bool} (S : Sector h d) (i : Fin (d+1)) :
    rightNeighbor (site S (last d)) ≠ site S i := by
  intro E
  have P : nextAt S.root (d+1)=nextAt S.root i.val := E
  have D := S.room
  have I := i.isLt
  have X := nextAt_injective_under S.root _ _ D (by omega) P
  omega

end L4.WidthSectorGeometry

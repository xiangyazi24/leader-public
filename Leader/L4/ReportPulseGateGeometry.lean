import Leader.L4.ReportPrelaunchK1Geometry
import Leader.L4.ReportLeaseOwner

namespace L4.ReportPulseGateGeometry
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortLayerGeometry
open ReportPrelaunchK1Geometry ReportLeaseOwner

variable {n : Nat} {h : Fin n→Bool}

/-- true is the outgoing label, hence the retained bit on an old
outgoing-first start. False is the actual incoming edge. -/
def put (b : Owner h×Bool) : Fin n :=
  if b.2 then b.1.val else RearTrace.predecessor b.1.val

theorem predecessor_not_selected (G : GapInput h) (b : Owner h) :
    h (RearTrace.predecessor b.val)=false := by
  cases E : h (RearTrace.predecessor b.val)
  · rfl
  · obtain ⟨a,P,_,S⟩ := G.gaps _ E
    have T := S.interior 1 (by decide) (by omega)
    change h (rightNeighbor (RearTrace.predecessor b.val))=false at T
    rw [RearTrace.right_predecessor,b.property] at T
    contradiction

/-- The pulse gate pairs are disjoint in the actual physical alphabet. -/
theorem put_injective (G : GapInput h) : Function.Injective (put (h:=h)) := by
  intro x y E
  rcases x with ⟨u,a⟩
  rcases y with ⟨v,b⟩
  cases a <;> cases b
  · have V := congrArg rightNeighbor E
    change rightNeighbor (RearTrace.predecessor u.val)=rightNeighbor (RearTrace.predecessor v.val) at V
    rw [RearTrace.right_predecessor,RearTrace.right_predecessor] at V
    exact Prod.ext (Subtype.ext V) rfl
  · have H := predecessor_not_selected G u
    change RearTrace.predecessor u.val=v.val at E
    rw [E,v.property] at H
    contradiction
  · have H := predecessor_not_selected G v
    change u.val=RearTrace.predecessor v.val at E
    rw [←E,u.property] at H
    contradiction
  · exact Prod.ext (Subtype.ext E) rfl

end L4.ReportPulseGateGeometry

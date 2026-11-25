import Leader.L4.ReportLeaseOwner

namespace L4.ReportIngressOwnership
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportPrelaunchK1Geometry ReportPrelaunchAllOwners ReportLeaseOwner
open ReportResetRawHooks ShortChartOwnership ReportResetBarrier

variable {n : Nat} {h : Fin n → Bool}

theorem canonical_centre (G : GapInput h) (r : Owner h) :
    let C := charter G r
    0<C.a ∧ C.a<C.L ∧ h (out C C.a)=true ∧
      C.route.port C.a=1 ∧ C.route.port (C.a-1)=0 := by
  unfold charter ownerChart
  dsimp only
  let a := Classical.choose (G.gaps r.val r.property)
  have A := Classical.choose_spec (G.gaps r.val r.property)
  let b := Classical.choose (G.gaps (nextAt r.val a) A.2.2.atEnd)
  have B := Classical.choose_spec (G.gaps (nextAt r.val a) A.2.2.atEnd)
  let c := Classical.choose (G.gaps (nextAt (nextAt r.val a) b) B.2.2.atEnd)
  have D := Classical.choose_spec (G.gaps (nextAt (nextAt r.val a) b) B.2.2.atEnd)
  change 0<a ∧ a<a+b+c ∧ h (nextAt r.val a)=true ∧
    lane a b a=1 ∧ lane a b (a-1)=0
  have va : 2<a := A.1
  have vb : 2<b := B.1
  exact ⟨by omega,by omega,A.2.2.atEnd,
    (lane1 _ _ _).2 ⟨by omega,by omega⟩,(lane0 _ _ _).2 (by omega)⟩

/-- A physical mark entering a canonical centre has the same unique
lane-0 owner as that centre in lane 1. No packet's bytes or source
phase are needed for this uniqueness statement. -/
theorem ingress_cell (G : GapInput h) (r : Owner h) (e : Fin n)
    (atCentre : rightNeighbor e=out (charter G r) (charter G r).a) :
    let C := charter G r
    C.a-1<C.L ∧ cell C (C.a-1)=(e,0) := by
  let C := charter G r
  obtain ⟨A,B,_,_,D⟩ := canonical_centre G r
  change 0<C.a at A
  change C.a<C.L at B
  have K : (C.a-1)+1=C.a := by omega
  have W : rightNeighbor (out C (C.a-1))=out C C.a := by
    change out C ((C.a-1)+1)=_
    rw [K]
  refine ⟨Nat.lt_of_le_of_lt (Nat.sub_le C.a 1) B,?_⟩
  exact Prod.ext (right_injective (W.trans atCentre.symm)) D

theorem all_ingress_same_owner (hh : ∃ i,h i=true) (G : GapInput h)
    (r q : Owner h) (e : Fin n) (l : Nat)
    (atCentre : rightNeighbor e=out (charter G r) (charter G r).a)
    (L : l<(charter G q).L) (E : cell (charter G q) l=(e,0)) :
    q=r ∧ l=(charter G r).a-1 := by
  obtain ⟨K,H⟩ := ingress_cell G r e atCentre
  obtain ⟨z,k,_,_,U⟩ := unique_cell hh G e 0
  obtain ⟨rq,rl⟩ := U q l L E
  obtain ⟨rr,ra⟩ := U r ((charter G r).a-1) K H
  exact ⟨rq.trans rr.symm,rl.trans ra.symm⟩

end L4.ReportIngressOwnership

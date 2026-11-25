import Leader.L4.RearGeometry

namespace L4.Height.ObserverGeometry
variable {n : Nat}

/-- Physical site of path slot k. At k=n use B at the root, at k<n use A. -/
def pos (r : Fin n) (k : Nat) := liftedSite r (n-k)
def edge (r k : Fin n) := pos r (k.val+1)

theorem first (r : Fin n) : pos r 0=r := by simp [pos,liftedSite_full]
theorem terminal (r : Fin n) : pos r n=r := by simp [pos,liftedSite_zero]
theorem responder (r k : Fin n) : rightNeighbor (edge r k)=pos r k.val := by
  have h := k.isLt
  unfold edge pos
  rw [← liftedSite_succ,show n-(k.val+1)+1=n-k.val by omega]

theorem edge_inj (r k j : Fin n) (h : edge r k=edge r j) : k=j := by
  have K := k.isLt
  have J := j.isLt
  have E := liftedSite_inj r (i:=n-(k.val+1)) (j:=n-(j.val+1)) (by omega) (by omega) h
  apply Fin.ext; omega

theorem edge_onto (r e : Fin n) : ∃ k, edge r k=e := by
  obtain ⟨j,hj,eq⟩ := liftedSite_of_site r e
  refine ⟨⟨n-(j+1),by omega⟩,?_⟩
  change liftedSite r (n-(n-(j+1)+1))=e
  rwa [show n-(n-(j+1)+1)=j by omega]

noncomputable def index (r e : Fin n) := Classical.choose (edge_onto r e)
theorem edge_index (r e : Fin n) : edge r (index r e)=e := Classical.choose_spec (edge_onto r e)
theorem index_edge (r k : Fin n) : index r (edge r k)=k :=
  edge_inj r _ _ (edge_index _ _)

theorem pos_inj (r : Fin n) {i j : Nat} (hi : i<n) (hj : j<n)
    (eq : pos r i=pos r j) : i=j := by
  let k : Fin n := ⟨i,hi⟩
  let l : Fin n := ⟨j,hj⟩
  have E : rightNeighbor (edge r k)=rightNeighbor (edge r l) := by
    rw [responder,responder]; exact eq
  have N := congrArg RearTrace.predecessor E
  simp only [RearTrace.predecessor_right] at N
  exact congrArg Fin.val (edge_inj r k l N)

theorem root_source (r k : Fin n) : pos r k.val=r ↔ k.val=0 := by
  constructor
  · intro h
    exact pos_inj r k.isLt (Nat.zero_lt_of_lt r.isLt) (h.trans (first r).symm)
  · intro h; rw [h,first]

theorem root_dest (r k : Fin n) : edge r k=r ↔ k.val+1=n := by
  have K := k.isLt
  constructor
  · intro h
    apply Classical.byContradiction
    intro falseEq
    have I : k.val+1<n := by omega
    have j := pos_inj r I (Nat.zero_lt_of_lt r.isLt) (h.trans (first r).symm)
    omega
  · intro h; simp [edge,h,terminal]

#print axioms first
#print axioms terminal
#print axioms responder
#print axioms edge_inj
#print axioms edge_onto
#print axioms edge_index
#print axioms index_edge
#print axioms pos_inj
#print axioms root_source
#print axioms root_dest
end L4.Height.ObserverGeometry

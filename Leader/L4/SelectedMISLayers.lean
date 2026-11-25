import Leader.L4.SelectedRingGeometry
import Leader.L4.ShortMISSpacing
import Leader.L4.ProductionShortRoom
import Leader.L4.SelectedNORPhysicalPeriod

namespace L4.SelectedMISLayers
open AllSizeProtocol PhysicalCustody ShortResetChart ShortLayerGeometry
open ShortHopSpacing ReportStaticSpacing SelectedRingGeometry

/-- The canonical cyclic selected ring drives this certificate. The
mask is static, and selection must come from the lower layer. -/
structure Layer {n L U : Nat} {h : Fin n→Bool} (G : GapBounds h L U)
    (sel : Fin n→Bool) : Prop where
  sub : ∀ i,sel i=true → h i=true
  independent : ∀ i : Lower h, sel i.val=true → sel (successor G i).val=false
  dominates : ∀ i : Lower h, sel i.val=false →
    sel (predecessor ⟨i.val,i.property⟩ i).val=true ∨ sel (successor G i).val=true

noncomputable def prevOn {n : Nat} {h : Fin n→Bool} (i : Fin n) : Fin n :=
  if I : h i=true then (predecessor ⟨i,I⟩ ⟨i,I⟩).val else i

theorem layer_gaps {n L U : Nat} {h sel : Fin n→Bool}
    {G : GapBounds h L U} (C : Layer G sel) : GapBounds sel (2*L) (3*U) := by
  apply ShortMISSpacing.physical_gap_bounds (f:=successorWidth G) (prev:=prevOn (h:=h))
    (successorWidth_spec G)
  · intro r R
    let i : Lower h := ⟨r,R⟩
    let j := successor G i
    have E := congrArg Subtype.val (predecessor_successor G ⟨j.val,j.property⟩ i)
    change prevOn j.val=r
    rw [prevOn,dif_pos j.property]
    exact E
  · exact C.sub
  · intro i I
    exact C.independent ⟨i,C.sub i I⟩ I
  · intro i H I
    rw [prevOn,dif_pos H]
    exact C.dominates ⟨i,H⟩ I

theorem layer_nonempty {n L U : Nat} {h sel : Fin n→Bool}
    {G : GapBounds h L U} (C : Layer G sel) (H : ∃ i,h i=true) :
    ∃ i,sel i=true := by
  obtain ⟨i,I⟩ := H
  let j : Lower h := ⟨i,I⟩
  by_cases Q : sel i=true
  · exact ⟨i,Q⟩
  · rcases C.dominates j (Bool.eq_false_iff.mpr Q) with K|K
    · exact ⟨_,K⟩
    · exact ⟨_,K⟩

theorem layer_of_nor {n L U : Nat} {h sel : Fin n→Bool}
    {G : GapBounds h L U} (hh : ∃ i,h i=true) (room : U<n)
    (sub : ∀ i,sel i=true→h i=true)
    (I : ShortNORCover.Independent (ring G hh room) (fun i=>sel i.val))
    (D : ∀ i, ShortNORCover.Dominates (ring G hh room) (fun i=>sel i.val) i) :
    Layer G sel := by
  refine ⟨sub,?_,?_⟩
  · intro i A
    exact Bool.eq_false_iff.mpr (fun B=>I i ⟨A,B⟩)
  · intro i A
    rcases D i with L|E|R
    · exact Or.inl L
    · change sel i.val=true at E
      rw [A] at E
      contradiction
    · exact Or.inr R

theorem ring_no_short_period {n L U : Nat} {h : Fin n→Bool} {G : GapBounds h L U}
    (hh : ∃ i,h i=true) (room : 3*U<n) :
    SelectedNORNondegenerate.LowerNondegenerate (ring G hh (by omega)) := by
  exact SelectedNORPhysicalPeriod.nondegenerate_of_bounded_width (U:=U)
    (ring G hh (by omega)) Subtype.val (fun q=>successorWidth G q.val)
    (fun _=>rfl)
    (fun q=>(successorWidth_spec G q.val q.property).2.2.positive)
    (fun q=>(successorWidth_spec G q.val q.property).2.1) room

def h1 {s n : Nat} (z : Raw s n) : Fin n→Bool := fun i=>(oldHeaders (rows s) (z i)).h1
def h2 {s n : Nat} (z : Raw s n) : Fin n→Bool := fun i=>(oldHeaders (rows s) (z i)).h2
def h3 {s n : Nat} (z : Raw s n) : Fin n→Bool := fun i=>(oldHeaders (rows s) (z i)).h3

theorem h2_mask {s n : Nat} (z : Raw s n) (i : Fin n) :
    h2 z i=(h1 z i && ShortByteReadouts.misSelected (z i).mis1) := rfl

theorem h3_mask {s n : Nat} (z : Raw s n) (i : Fin n) :
    h3 z i=(h2 z i && ShortByteReadouts.misSelected (z i).mis2) := rfl

theorem h4_mask {s n : Nat} (z : Raw s n) (i : Fin n) :
    h4 z i=(h3 z i && ShortByteReadouts.misSelected (z i).mis3) := rfl

theorem h1_gaps {s n : Nat} {z : Raw s n} (A : PhysicalCustody.H1.rawMaximal z) :
    GapBounds (h1 z) 2 3 := by
  intro i I
  obtain ⟨d,D,E,F⟩ := ShortResetChart.gap A i I
  exact ⟨d,by rcases D with D|D <;> omega,by rcases D with D|D <;> omega,
    ⟨by rcases D with D|D <;> omega,E,F⟩⟩

theorem h1_nonempty {s n : Nat} {z : Raw s n} (A : PhysicalCustody.H1.rawMaximal z)
    (N : 0<n) : ∃ i,h1 z i=true := by
  let i : Fin n := ⟨0,N⟩
  rcases A.2 i with L|C|R
  · exact ⟨_,L⟩
  · exact ⟨_,C⟩
  · exact ⟨_,R⟩

theorem h2_gaps {s n : Nat} {z : Raw s n} {G : GapBounds (h1 z) 2 3}
    (C : Layer G (h2 z)) : GapBounds (h2 z) 4 9 := layer_gaps C

theorem h3_gaps {s n : Nat} {z : Raw s n} {G : GapBounds (h2 z) 4 9}
    (C : Layer G (h3 z)) : GapBounds (h3 z) 8 27 := layer_gaps C

theorem h4_gaps {s n : Nat} {z : Raw s n} {G : GapBounds (h3 z) 8 27}
    (C : Layer G (h4 z)) : GapBounds (h4 z) 16 81 := layer_gaps C

theorem charts_of_layers {s n : Nat} {z : Raw s n} (S : 6≤s) (advice : s=ell (ell n))
    (A : PhysicalCustody.H1.rawMaximal z)
    (C1 : Layer (h1_gaps A) (h2 z)) (C2 : Layer (h2_gaps C1) (h3 z)) :
    (∀ i, h1 z i=true → ∃ C : ShortResetCycle.Chart (h1 z), C.root=i ∧ C.L≤9) ∧
    (∀ i, h2 z i=true → ∃ C : ShortResetCycle.Chart (h2 z), C.root=i ∧ C.L≤27) ∧
    (∀ i, h3 z i=true → ∃ C : ShortResetCycle.Chart (h3 z), C.root=i ∧ C.L≤81) := by
  have upper {h : Fin n→Bool} {L U : Nat} (G : GapBounds h L U) :
      ∀ i,h i=true→∃ d≤U,Gap h i d := by
    intro i I
    obtain ⟨d,_,B,K⟩ := G i I
    exact ⟨d,B,K⟩
  exact ⟨ProductionShortRoom.chart_cap_nine S advice (upper (h1_gaps A)),
    ProductionShortRoom.chart_cap_twentySeven S advice (upper (h2_gaps C1)),
    ProductionShortRoom.chart_cap_eightyOne S advice (upper (h3_gaps C2))⟩

/-- Conditional H4 producer for the exact lower mask consumed by the
already checked report-spacing theorem. -/
theorem h4_report_seed {s n : Nat} {z : Raw s n} (N : 0<n)
    (A : PhysicalCustody.H1.rawMaximal z)
    (C1 : Layer (h1_gaps A) (h2 z)) (C2 : Layer (h2_gaps C1) (h3 z))
    (C3 : Layer (h3_gaps C2) (h4 z)) :
    GapBounds (h4 z) 16 81 ∧ (∃ i,h4 z i=true) :=
  ⟨h4_gaps C3,layer_nonempty C3 (layer_nonempty C2 (layer_nonempty C1 (h1_nonempty A N)))⟩

end L4.SelectedMISLayers

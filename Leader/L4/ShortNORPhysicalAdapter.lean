import Leader.L4.PhysicalH1Neighbors
import Leader.L4.ShortNORFrozen

namespace L4.ShortNORPhysicalAdapter
open AllSizeProtocol PhysicalCustody ShortResetChart ReportStaticSpacing
open SelectedMISLayers ShortNORCover CustodyMonitorTargets

private theorem ring_eq_of_maps {J : Type} (r t : Ring J)
    (l : r.left=t.left) (k : r.right=t.right) : r=t := by
  cases r
  cases t
  cases l
  cases k
  rfl

theorem mis1_h1_rings_identical {s n : Nat} {z : Raw s n}
    (A : H1.rawMaximal z) (N : 3<n) :
    PhysicalH1Neighbors.fixedRing A N (h:=h1 z) (fun _=>rfl) =
      SelectedRingGeometry.ring (h1_gaps A) (h1_nonempty A (by omega)) N := by
  let P := PhysicalH1Neighbors.fixedRing A N (h:=h1 z) (fun _=>rfl)
  let R := SelectedRingGeometry.ring (h1_gaps A) (h1_nonempty A (by omega)) N
  change P=R
  have right : P.right=R.right := by
    funext i
    apply Subtype.ext
    have HP : (P.right i).val=nextAt i.val (PhysicalH1Neighbors.rightDist (h1 z) i.val) :=
      PhysicalH1Neighbors.fixedRing_right A N (h:=h1 z) (fun _=>rfl) i
    rw [HP]
    have T := (ShortHopSpacing.successorWidth_spec (h1_gaps A) i.val i.property)
    obtain ⟨d,D,H,C⟩ := ShortResetChart.gap A i.val i.property
    change h1 z (nextAt i.val d)=true at H
    change (∀ k, 0<k → k<d → h1 z (nextAt i.val k)=false) at C
    rw [PhysicalH1Neighbors.rightDist_eq_gap D H C]
    change nextAt i.val d=nextAt i.val (ShortHopSpacing.successorWidth (h1_gaps A) i.val)
    rw [WidthOrdinalSpan.gap_unique T.2.2 ⟨by rcases D with v|v <;> omega,H,C⟩]
  apply ring_eq_of_maps _ _ _ right
  funext i
  have E := P.rl i
  rw [right] at E
  calc
    P.left i = R.left (R.right (P.left i)) := (R.lr _).symm
    _ = R.left i := congrArg R.left E

/-- Re-embed the selected-ring observation into physical positions; bits
outside the frozen lower mask are irrelevant, including arbitrary scratch. -/
def embed {n : Nat} (h : Fin n→Bool) (f : Lower h→Bool) (i : Fin n) : Bool :=
  if I : h i=true then f ⟨i,I⟩ else false

theorem embed_eq_mask {n : Nat} {h : Fin n→Bool} (v : Fin n→Bool) :
    embed h (fun i=>v i.val)=(fun i=>h i && v i) := by
  funext i
  cases I : h i <;> simp [embed,I]

theorem layer_of_observe {n L U : Nat} {h : Fin n→Bool}
    (G : ShortHopSpacing.GapBounds h L U) (hh : ∃ i,h i=true) (room : U<n)
    (v : Lower h→Bool)
    (I : Independent (SelectedRingGeometry.ring G hh room) v)
    (D : ∀ i,Dominates (SelectedRingGeometry.ring G hh room) v i) :
    Layer G (embed h v) := by
  apply layer_of_nor hh room
  · intro j J
    by_cases H : h j=true
    · exact H
    · simp [embed,H] at J
  · have E : (fun i : Lower h=>embed h v i.val)=v := by
      funext i
      exact dif_pos i.property
    rwa [E]
  · have E : (fun i : Lower h=>embed h v i.val)=v := by
      funext i
      exact dif_pos i.property
    rwa [E]

theorem mis1_frozen_layer {s n : Nat} {z : Raw s n} (A : H1.rawMaximal z) (N : 3<n)
    (step : Raw s n→Fin n→Raw s n)
    (classify : Raw s n→Fin n→Option (Lower (h1 z)))
    (Good : Raw s n→Prop)
    (closed : ∀ x e,Good x→Good (step x e))
    (heads : ∀ x,Good x→h1 x=h1 z)
    (auth : ∀ x e,Good x→
      (fun i : Lower (h1 z)=>ShortByteReadouts.misSelected (step x e i.val).mis1) =
      let obs := fun i : Lower (h1 z)=>ShortByteReadouts.misSelected (x i.val).mis1
      match classify x e with
      | none => obs
      | some i => update (PhysicalH1Neighbors.fixedRing A N (h:=h1 z) (fun _=>rfl)) obs i)
    (M : RawMaximal (PhysicalH1Neighbors.fixedRing A N (h:=h1 z) (fun _=>rfl))
      (fun x i=>ShortByteReadouts.misSelected (x i.val).mis1) Good z)
    (w : List (Fin n)) :
    let y := w.foldl step z
    Good y ∧ h1 y=h1 z ∧ h2 y=h2 z ∧ Layer (h1_gaps A) (h2 y) := by
  let R := SelectedRingGeometry.ring (h1_gaps A) (h1_nonempty A (by omega)) N
  let P := PhysicalH1Neighbors.fixedRing A N (h:=h1 z) (fun _=>rfl)
  let observe := fun (x : Raw s n) (i : Lower (h1 z)) =>
    ShortByteReadouts.misSelected (x i.val).mis1
  let y := w.foldl step z
  obtain ⟨Y,Frozen⟩ := ShortNORFrozen.raw_observe_frozen step classify P observe Good closed (by
    intro x e H
    have F := auth x e H
    cases C : classify x e <;> simpa [C,P,observe] using F) z w M
  have E : P=R := mis1_h1_rings_identical A N
  change RawMaximal P observe Good y at Y
  rw [E] at Y
  have H := heads y Y.1
  have mask (x : Raw s n) (H : h1 x=h1 z) : h2 x=embed (h1 z) (observe x) := by
    funext i
    rw [h2_mask,congrFun H i,embed_eq_mask (fun j=>ShortByteReadouts.misSelected (x j).mis1)]
  exact ⟨Y.1,H,(mask y H).trans ((congrArg (embed (h1 z)) Frozen).trans (mask z rfl).symm),
    (mask y H).symm ▸ layer_of_observe (h1_gaps A) (h1_nonempty A (by omega)) N
      (observe y) Y.2.1 Y.2.2⟩

end L4.ShortNORPhysicalAdapter

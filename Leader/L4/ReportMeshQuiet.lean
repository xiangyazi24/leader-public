import Leader.L4.ReportServiceMesh
import Leader.L4.ReportQuietCovers

namespace L4.ReportMeshQuiet
open Height ReportServiceMesh
variable {X J : Type} {n m : Nat}

/-- The publication label at physical coordinate t reads the old state. -/
def tapePublish (step : X→Fin n→X) (classify : X→Fin n→Option J)
    (x : X) (w : List (Fin n)) (t : Nat) (j : J) : Prop :=
  ∃ e,w[t]?=some e ∧ classify (runWord step x (w.take t)) e=some j

private theorem pub_of_split (step : X→Fin n→X) (classify : X→Fin n→Option J)
    (x : X) (w p q : List (Fin n)) (e : Fin n) (j : J)
    (W : w=p++e::q) (H : classify (runWord step x p) e=some j) :
    tapePublish step classify x w p.length j := by
  subst w
  refine ⟨e,?_,?_⟩
  · simp
  · rwa [List.take_append_length]

theorem indexed_receipts (step : X→Fin n→X) (classify : X→Fin n→Option J)
    (writer : Fin m→J) (x : X) (B b : Nat) (bp : 0<b)
    (w : List (Fin n)) (W : w.length=B) (OK : TwoCellCovers step classify writer x B b w)
    (c : Fin (cells B b)) (i : Fin m) :
    let a := 2*c.val*b
    (∃ t,a≤t ∧ t<a+b ∧ tapePublish step classify x w t (writer i)) ∧
    (∃ t,a+b≤t ∧ t<(2*c.val+2)*b ∧ tapePublish step classify x w t (writer i)) := by
  let a := 2*c.val*b
  let p := w.take a
  let u := (w.drop a).take b
  let v := ((w.drop a).drop b).take b
  let q := ((w.drop a).drop b).drop b
  obtain ⟨E,LP,LU,LV⟩ := cell_split B b bp w W c
  change w=p++(u++(v++q)) at E
  change p.length=a at LP
  change u.length=b at LU
  change v.length=b at LV
  obtain ⟨p1,e1,q1,p2,e2,q2,U,V,C1,C2⟩ :=
    chronological_receipts step classify writer x B b w OK c i
  change u=p1++e1::q1 at U
  change v=p2++e2::q2 at V
  change classify (runWord step (runWord step x p) p1) e1=some (writer i) at C1
  change classify (runWord step (runWord step (runWord step x p) u) p2) e2=some (writer i) at C2
  have H1 : p1.length<b := by rw [U,List.length_append,List.length_cons] at LU; omega
  have H2 : p2.length<b := by rw [V,List.length_append,List.length_cons] at LV; omega
  have End : (2*c.val+2)*b=a+b+b := by
    unfold a
    rw [Nat.add_mul,show 2*b=b+b by omega]
    omega
  constructor
  · refine ⟨(p++p1).length,?_,?_,?_⟩
    · rw [List.length_append,LP]; omega
    · rw [List.length_append,LP]; omega
    · apply pub_of_split step classify x w (p++p1) (q1++(v++q)) e1
      · rw [E,U]; simp only [List.append_assoc,List.cons_append]
      · rwa [runWord_append]
  · refine ⟨(p++u++p2).length,?_,?_,?_⟩
    · simp only [List.length_append,LP,LU]; omega
    · rw [End]; simp only [List.length_append,LP,LU]; omega
    · apply pub_of_split step classify x w (p++u++p2) (q2++q) e2
      · rw [E,V]; simp only [List.append_assoc,List.cons_append]
      · rwa [runWord_append,runWord_append]

theorem cell_covers (step : X→Fin n→X) (classify : X→Fin n→Option J)
    (writer : Fin m→J) (ball : J→Prop) (census : ∀ j,ball j→∃ i,writer i=j)
    (x : X) (B b : Nat) (bp : 0<b) (w : List (Fin n)) (W : w.length=B)
    (OK : TwoCellCovers step classify writer x B b w) (c : Fin (cells B b)) :
    ReportQuietCovers.Covers ball (tapePublish step classify x w) (2*c.val*b) ((2*c.val+2)*b) := by
  intro j J
  obtain ⟨i,E⟩ := census j J
  obtain ⟨t,L,R,P⟩ := (indexed_receipts step classify writer x B b bp w W OK c i).2
  rw [E] at P
  exact ⟨t,by omega,R,P⟩

end L4.ReportMeshQuiet

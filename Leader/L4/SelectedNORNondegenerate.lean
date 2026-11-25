import Leader.L4.ShortNORCover
import Init.Omega

namespace L4.SelectedNORNondegenerate
open ShortNORCover

/-- Too-small lower cycles are precisely where the first chosen return
may meet its own root again. Existing `Ring.noLoop` only excludes
period one on the lower layer. -/
structure LowerNondegenerate {Site : Type} (r : Ring Site) : Prop where
  noTwo : ∀ i, r.right (r.right i) ≠ i
  noThree : ∀ i, r.right (r.right (r.right i)) ≠ i

/-- A chosen root on an independent dominating lower-cycle mask
has its first next chosen header two or three hops ahead. The
statement is valid even for a C3 returning to the same root. -/
theorem next_two_or_three {Site : Type} (r : Ring Site)
    (x : Site → Bool) (ind : Independent r x) (dom : ∀ i, Dominates r x i)
    (q : Site) (Q : x q = true) :
    x (r.right q)=false ∧
      (x (r.right (r.right q))=true ∨
        (x (r.right (r.right q))=false ∧ x (r.right (r.right (r.right q)))=true)) := by
  have F : x (r.right q)=false := Bool.eq_false_iff.mpr (fun H=>ind q ⟨Q,H⟩)
  refine ⟨F,?_⟩
  cases D : x (r.right (r.right q))
  · have R := dom (r.right (r.right q))
    unfold Dominates at R
    rw [r.lr,F,D] at R
    exact Or.inr ⟨rfl,by simpa using R⟩
  · exact Or.inl rfl

def nextChosen {Site : Type} (r : Ring Site) (x : Site → Bool)
    (ind : Independent r x) (dom : ∀ i, Dominates r x i)
    (q : {i // x i=true}) : {i // x i=true} :=
  if T : x (r.right (r.right q.val))=true then ⟨r.right (r.right q.val),T⟩
  else ⟨r.right (r.right (r.right q.val)), by
    rcases (next_two_or_three r x ind dom q.val q.property).2 with H|H
    · exact False.elim (T H)
    · exact H.2⟩

theorem nextChosen_noLoop {Site : Type} (r : Ring Site) (nondeg : LowerNondegenerate r)
    (x : Site → Bool) (ind : Independent r x) (dom : ∀ i, Dominates r x i)
    (q : {i // x i=true}) : nextChosen r x ind dom q ≠ q := by
  intro H
  unfold nextChosen at H
  split at H
  · exact nondeg.noTwo q.val (congrArg Subtype.val H)
  · exact nondeg.noThree q.val (congrArg Subtype.val H)

theorem at_least_two {Site : Type} (r : Ring Site) (nondeg : LowerNondegenerate r)
    (x : Site → Bool) (ind : Independent r x) (dom : ∀ i, Dominates r x i)
    (i : Site) : ∃ q t, q ≠ t ∧ x q=true ∧ x t=true := by
  have ex : ∃ j, x j=true := by
    rcases dom i with D|D|D
    · exact ⟨r.left i,D⟩
    · exact ⟨i,D⟩
    · exact ⟨r.right i,D⟩
  obtain ⟨j,J⟩ := ex
  let q : {i // x i=true} := ⟨j,J⟩
  let t := nextChosen r x ind dom q
  exact ⟨t.val,q.val,fun H=>nextChosen_noLoop r nondeg x ind dom q (Subtype.ext H),t.property,q.property⟩

def c3Left (i : Fin 3) : Fin 3 := ⟨(i.val+2)%3,by omega⟩
def c3Right (i : Fin 3) : Fin 3 := ⟨(i.val+1)%3,by omega⟩

def c3 : Ring (Fin 3) where
  left := c3Left
  right := c3Right
  lr := by decide
  rl := by decide
  noLoop := by decide

def singleton (i : Fin 3) : Bool := i==0

theorem c3_ind : Independent c3 singleton := by
  change ∀ i : Fin 3, ¬ (singleton i=true ∧ singleton (c3Right i)=true)
  decide

theorem c3_dom : ∀ i, Dominates c3 singleton i := by
  change ∀ i : Fin 3, singleton (c3Left i)=true ∨ singleton i=true ∨ singleton (c3Right i)=true
  decide

def c3Chosen : {i // singleton i=true} := ⟨0,rfl⟩

/-- Even though C3 passes the lower Ring's noLoop check, its legitimate
singleton MIS cannot supply noLoop for the next selected ring. -/
theorem c3_singleton_mis_fixed_point :
    nextChosen c3 singleton c3_ind c3_dom c3Chosen = c3Chosen := by
  apply Subtype.ext
  rfl

theorem c3_selected_type_singleton (q : {i // singleton i = true}) : q = c3Chosen := by
  apply Subtype.ext
  exact of_decide_eq_true q.property

theorem c3_selected_no_ring : ¬ Nonempty (Ring {i // singleton i=true}) := by
  rintro ⟨r⟩
  exact r.noLoop c3Chosen (c3_selected_type_singleton (r.right c3Chosen))

#print axioms next_two_or_three
#print axioms nextChosen_noLoop
#print axioms at_least_two
#print axioms c3_ind
#print axioms c3_dom
#print axioms c3_singleton_mis_fixed_point
#print axioms c3_selected_no_ring
end L4.SelectedNORNondegenerate

import Leader.L4.BStarSeparatorControl

/-! A genuine selected terminal is allowed to hold an arbitrary tour.
Its old F then remains the pointed front. This adapter never counts a
parked FENCE terminal as a completed turn or a covered service event. -/
namespace L4.BStarSeparatorParked
open BStarLongToken BStarSeparatingRail BStarResetMarkAdapter BStarSeparatorControl

theorem forward_not_empty : ¬ anyTag.F .empty := by rintro ⟨_,h⟩; cases h
theorem forward_not_trail : ¬ anyTag.F .trail := by rintro ⟨_,h⟩; cases h
theorem disjoint_class (t : Token) : anyTag.D t → ¬ anyTag.F t := by
  rintro ⟨v,h⟩ ⟨u,k⟩
  rw [h] at k
  cases k

def turns (term : Prop) (len : Nat) (x y : BStarSeparatingRail.Rail) : Prop :=
  term ∧ (anyTag.F (x len) → anyTag.D (y len))

/-- The hypothesis term is the physical footprint; turns is terminal
service. For a held F, only forward-class preservation remains as an
idle law. The existing cursor induction then applies unchanged. -/
def parked_mark {len : Nat} {x y : BStarSeparatingRail.Rail}
    {link : Nat → Prop} {term : Prop}
    (bounds : ∀ j, link j → j<len)
    (apart : ∀ j, link j → ¬link (j+1))
    (apart_term : ∀ j, link j → j+1=len → ¬term)
    (quiet : Quiet anyTag len x y link term)
    (fx : ∀ j, link j → anyTag.F (x j) →
      anyTag.F (y j) ∨ (y j=.trail ∧ anyTag.F (y (j+1))))
    (td : ∀ j, link j → x j=.trail → anyTag.D (x (j+1)) →
      anyTag.D (y j) ∧ y (j+1)=.empty)
    (term_f : term → anyTag.F (x len) → anyTag.F (y len) ∨ anyTag.D (y len)) :
    Mark anyTag len x y := by
  classical
  refine { link := link
           terminal := turns term len x y
           bound := bounds
           disjoint := apart
           terminal_disjoint := fun j J E T => apart_term j J E T.1
           idle := ?_
           tt := quiet.tt
           ee := quiet.ee
           tf := quiet.tf
           fx := fx
           td := td
           de := quiet.de
           termF := fun T => T.2
           termD := fun T => quiet.termD T.1
           termE := fun T => quiet.termE T.1 }
  intro j hJ notL notR notTurn
  by_cases real : j=len ∧ term
  · obtain ⟨rfl,T⟩ := real
    have F : anyTag.F (x j) := by
      apply Classical.byContradiction
      intro NF
      exact notTurn rfl ⟨T,fun f => (NF f).elim⟩
    have D : ¬ anyTag.D (y j) := fun A => notTurn rfl ⟨T,fun _ => A⟩
    have Y := (term_f T F).resolve_right D
    refine ⟨?_,?_,fun _ => Y,?_⟩
    · intro E
      exact (forward_not_trail (E ▸ F)).elim
    · intro E
      exact (forward_not_empty (E ▸ F)).elim
    · intro A
      exact (disjoint_class _ A F).elim
  · exact quiet.idle j hJ notL notR (fun E T => real ⟨E,T⟩)

#print axioms parked_mark
end L4.BStarSeparatorParked

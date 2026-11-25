import Leader.L4.SelectedNORNondegenerate
import Leader.L4.ShortResetChart

namespace L4.SelectedNORPhysicalPeriod
open ShortNORCover ShortResetChart SelectedNORNondegenerate

/-- Positive bounded physical gaps rule out small periods directly,
including for a candidate successor before building the selected Ring. -/
theorem no_return_in_three {Site : Type} {n U : Nat} (step : Site → Site)
    (physical : Site → Fin n) (width : Site → Nat)
    (go : ∀ i, physical (step i)=nextAt (physical i) (width i))
    (positive : ∀ i, 0<width i) (bounded : ∀ i, width i≤U)
    (large : 3*U<n) (i : Site) :
    step i≠i ∧ step (step i)≠i ∧ step (step (step i))≠i := by
  have R2 : physical (step (step i)) = nextAt (physical i) (width i+width (step i)) := by
    rw [go,go i,nextAt_add]
  have R3 : physical (step (step (step i))) =
      nextAt (physical i) (width i+width (step i)+width (step (step i))) := by
    rw [go (step (step i)),R2,nextAt_add (physical i) (width i+width (step i))]
  have noReturn {d : Nat} (P : 0<d) (B : d<n) :
      nextAt (physical i) d ≠ physical i := by
    intro E
    have T := nextAt_injective_under (physical i) d 0 B (by omega) E
    omega
  have W0 := positive i
  have U0 := bounded i
  have U1 := bounded (step i)
  have U2 := bounded (step (step i))
  refine ⟨?_,?_,?_⟩
  · intro E
    have K := congrArg physical E
    rw [go] at K
    exact noReturn W0 (by omega) K
  · intro E
    have K := congrArg physical E
    rw [R2] at K
    exact noReturn (by omega) (by omega) K
  · intro E
    have K := congrArg physical E
    rw [R3] at K
    exact noReturn (by omega) (by omega) K

theorem nondegenerate_of_bounded_width {Site : Type} {n U : Nat} (r : Ring Site)
    (physical : Site → Fin n) (width : Site → Nat)
    (go : ∀ i, physical (r.right i)=nextAt (physical i) (width i))
    (positive : ∀ i, 0<width i) (bounded : ∀ i, width i≤U)
    (large : 3*U<n) : LowerNondegenerate r where
  noTwo i := (no_return_in_three r.right physical width go positive bounded large i).2.1
  noThree i := (no_return_in_three r.right physical width go positive bounded large i).2.2

end L4.SelectedNORPhysicalPeriod

import Leader.Wu.Birth.SmallRingPhaseBound
import Leader.Wu.Birth.ShortDoneParameterChoice

set_option autoImplicit false

namespace BirthSmallRingWrapperN2

open Q11497FeasibilityAudit

/-- The actual global parameter tuple selected at n = 2. -/
theorem n2_actual_parameters :
    scale 2 = 1 ∧
    psiChoice 2 = 1 ∧
    widthChoice = 2 ∧
    kappaChoice 2 = 2 ∧
    tauChoice 2 = 32 := by
  decide

/-- The literal width premise required by both the terminal consumer and
`SmallRingBirthPhaseBound` is false at the actual n = 2 choices. -/
theorem n2_width_not_admissible :
    ¬ widthChoice ≤ psiChoice 2 := by
  decide

/-- Hence there is no term that can be supplied as the actual n = 2 `hle`
argument to `BirthShortDoneTerminalConsumer.step`. -/
theorem n2_actual_hle_elim
    (hle : widthChoice ≤ psiChoice 2) : False := by
  exact n2_width_not_admissible hle

/-- Package the exact signature-level obstruction. -/
theorem n2_actual_consumer_typing_impossible :
    ¬ (0 < psiChoice 2 ∧
       0 < widthChoice ∧
       widthChoice ≤ psiChoice 2) := by
  decide

/-- The requested cheap smoke tuple is a legal *different* parameterization.
This theorem deliberately makes no claim that its legacy P_partial closed
class is closed for the current terminal consumer. -/
theorem smoke_tuple_typing :
    0 < (1 : Nat) ∧ 0 < (1 : Nat) ∧ (1 : Nat) ≤ 1 := by
  decide

/-- At n = 3 the protocol's actual width is legal, and width two fits in the
three-site ring.  The separate Local3 premise 4 ≤ n is still unavailable. -/
theorem n3_actual_parameters :
    scale 3 = 1 ∧
    psiChoice 3 = 2 ∧
    widthChoice = 2 ∧
    kappaChoice 3 = 2 ∧
    tauChoice 3 = 32 ∧
    widthChoice ≤ psiChoice 3 ∧
    widthChoice < 3 := by
  decide

end BirthSmallRingWrapperN2

#print axioms BirthSmallRingWrapperN2.n2_actual_parameters
#print axioms BirthSmallRingWrapperN2.n2_width_not_admissible
#print axioms BirthSmallRingWrapperN2.n2_actual_hle_elim
#print axioms BirthSmallRingWrapperN2.n2_actual_consumer_typing_impossible
#print axioms BirthSmallRingWrapperN2.smoke_tuple_typing
#print axioms BirthSmallRingWrapperN2.n3_actual_parameters

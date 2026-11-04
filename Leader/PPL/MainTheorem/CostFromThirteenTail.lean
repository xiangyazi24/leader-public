import Leader.PPL.MainTheorem.CostFromThirteen

/-!
P_PL Theorem 1 cleanup, phase 2: the declarations of this file that served only the old
psi <= log2 n + 1 route to `theorem1Statement_proved` moved to
`Leader/Superseded/Theorem1LogWindow/Theorem1CostFrom13Tail.lean`, namespace `PPL.Superseded.LogWindow`: `q20292_sum_if_count`, `q20292_countP_take_pad`, `theorem1From13_tailJointSelection_of_l18FirstHit`.
-/

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/--
The H17 failure predicate, lifted to an H5(ii)-length suffix by reading
only its first H17 letters.
-/
def theorem1From13_tailL17Bad
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (p phase : DetSchedule n) : Bool :=
  theorem1L17PhaseBad
    ring C0 p
    (phase.take (theorem1H17 n))

/--
The three local tail failures that must be avoided simultaneously after
the selected first-C_mid prefix:
  * L5(ii) Construct-window failure, coefficient 4;
  * L17 literal-one failure, coefficient 1;
  * L18 rooted-prime failure, coefficient 1.
-/
def theorem1From13_tailJointBad
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (p phase : DetSchedule n) : Bool :=
  theorem1L5iiFirstHitPhaseBad ring C0 p phase ||
    (theorem1From13_tailL17Bad ring C0 p phase ||
      theorem1L18FirstHitPhaseBad ring C0 p phase)

end PPL

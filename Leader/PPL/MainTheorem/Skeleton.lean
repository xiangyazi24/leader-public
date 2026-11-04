import Leader.PPL.ReachCPB.WordBound
import Leader.PPL.Modes.ConstructionMode
import Leader.PPL.Elim.OneLeaderBound
import Leader.PPL.SPLEntry.ForcingWord
import Leader.PPL.Safety.SPL
import Leader.Wu.Elimination.ArbitraryInputExpectedCost


namespace PPL


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


/-!
# Shared vocabulary of the P_PL Theorem 1 statement

The absolute constant `theorem1C17 = 862592`, the psi-window bound
`theorem1K n = log2 n + 1`, the prefix-hitting test `theorem1ReachesSPL`, and
the exact failure and truncated-cost numerators over the `n^T` scheduler
words.  The statement itself, its clock constant `theorem1C1`, clock
`theorem1Kappa` and horizon `theorem1Horizon` are in `Leader/PPL/MainTheorem/Kappa.lean`
and `Leader/PPL/MainTheorem/Statement.lean`.  The first frozen statement (clock
`(32*C17 + 352)*psi`, horizon `H16 + H5(i) + H17 + H18`) is superseded and
kept in `Leader/PPL/SequentialClock/Statement.lean`.
-/


def theorem1C17 : Nat :=
  862592


def theorem1K (n : Nat) : Nat :=
  Nat.log2 n + 1


/-- Exact prefix-hitting test for the paper target S_PL. -/
def theorem1ReachesSPL
    {n psi kappa : Nat}
    (ring : DirectedRing n) :
    Config n psi kappa → DetSchedule n → Bool
  | C, [] =>
      decide (SPL ring C)
  | C, e :: rest =>
      decide (SPL ring C) ||
        theorem1ReachesSPL ring
          (PopulationProtocol.step
            (protocol psi kappa) ring C e)
          rest


/--
Exact finite uniform-scheduler failure numerator.
The denominator is literally n^T because allSchedules n T has that size.
-/
def theorem1FailureNumerator
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (T : Nat) : Nat :=
  (allSchedules n T).countP
    (fun word => !(theorem1ReachesSPL ring C word))


/--
Exact truncated first-hit cost numerator, summed over the same n^T physical
scheduler words.  The stopping predicate is S_PL itself.
-/
noncomputable def theorem1CostNumerator
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (T : Nat) : Nat :=
  K2ArbitraryElimination.FiniteAccounting.costNumerator
    (fun D e =>
      PopulationProtocol.step
        (protocol psi kappa) ring D e)
    (SPL ring)
    C T


/--
Small non-leaf glue: the existing rooted S_PL safety theorem lifts directly
to the existential-root predicate used by Theorem1Statement.
-/
theorem theorem1SPL_isSafe_of_local
    (hlocal : PPL.Safety.SPL.SPLLocalStepProp)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hSPL : SPL ring C) :
    PopulationProtocol.IsSafe
      (protocol psi kappa)
      ring C PPL.Safety.SPL.output := by
  unfold SPL at hSPL
  rcases hSPL with ⟨root, hroot⟩
  exact
    PPL.Safety.SPL.splAt_isSafe
      hlocal hn3 hpsi ring root C hroot


end PPL


#print axioms PPL.theorem1SPL_isSafe_of_local

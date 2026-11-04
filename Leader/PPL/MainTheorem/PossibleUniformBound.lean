import Leader.PPL.SPLEntry.ForcingWordClosed
import Init.Omega
import Leader.PPL.MainTheorem.GeneralExhaustive
import Leader.AAFJ.GlobalFairness
import Leader.PPL.Predicates

/-!
The declarations of this file that served only the old psi <= log2 n + 1 route to `theorem1Statement_proved`
(`Theorem1PossibleConvergenceUpto12` and its consumers) were removed with that superseded route.

Step 6e: `theorem1ReachesSPL_endpoint_prefix` and
`theorem1PossibleUniformBound_of_exhaustive` are the `S_PL` cases of
`Leader/PPL/MainTheorem/GeneralExhaustive.lean` (statements unchanged).
-/

/-!
# C.4 (n ≤ 12): the tiny producer from pointwise possible convergence

`Theorem1TinyProducerUpto12` asks, for each admissible pair with `n ≤ 12`,
for one length `L` such that from every configuration outside `SPL` some
schedule of length at most `L` ends in `SPL`.  Nothing is required along the
way: `BoundedSafeScheduleProducer` only constrains the endpoint.

This file reduces it to the pointwise statement
`Theorem1PossibleConvergenceUpto12`: from every configuration some schedule
visits `SPL` (a prefix hit in the sense of `theorem1ReachesSPL`).  The three
bookkeeping steps are

* finiteness: `theorem1ConfigStates` enumerates `Config n psi kappa`, so a
  finite maximum of the pointwise witness lengths is a uniform bound;
* truncation: a prefix hit becomes an endpoint witness by cutting the word at
  the first `SPL` configuration;
* rings: `DirectedRing n` has a single proof field, so the bound found for one
  ring serves every ring.
-/

namespace PPL

/--
Explicit exhaustive configuration certificate.

Config n psi kappa is definitionally Fin n -> PPLv2.State psi kappa.
-/
def theorem1ConfigStates
    (n psi kappa : Nat) :
    ExhaustiveList (Config n psi kappa) :=
  ExhaustiveList.finFunctions (PPLv2.states psi kappa) n


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPLLResearchFormulation

/-- A prefix hit yields an endpoint witness no longer than the word: cut the
word at the first configuration in `SPL`. -/
theorem theorem1ReachesSPL_endpoint_prefix
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (hhit : theorem1ReachesSPL ring C word = true) :
    ∃ pre : DetSchedule n,
      pre.length ≤ word.length ∧
      SPL ring
        (runLocalSchedule ring (PPL.protocol psi kappa).transition C pre) := by
  rw [PPL.Theorem1General.theorem1ReachesSPL_eq] at hhit
  obtain ⟨pre, hlen, h⟩ :=
    PPL.Theorem1General.theorem1ReachesB_endpoint_prefix ring _ C word hhit
  exact ⟨pre, hlen, by simpa using h⟩

/-- Finite maximum: pointwise prefix hits over an exhaustive configuration list
give one uniform length bound. -/
theorem theorem1PossibleUniformBound_of_exhaustive
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (e : ExhaustiveList (Config n psi kappa))
    (hpoint :
      ∀ C : Config n psi kappa,
        ∃ word : DetSchedule n, theorem1ReachesSPL ring C word = true) :
    ∃ L : Nat,
      ∀ C : Config n psi kappa,
        ∃ word : DetSchedule n,
          word.length ≤ L ∧ theorem1ReachesSPL ring C word = true :=
  PPL.Theorem1General.theorem1UniformBound_of_exhaustive e
    (theorem1ReachesSPL ring) hpoint

end PPL

#print axioms PPL.theorem1ReachesSPL_endpoint_prefix
#print axioms PPL.theorem1PossibleUniformBound_of_exhaustive

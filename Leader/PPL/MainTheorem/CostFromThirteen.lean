import Leader.PPL.MainTheorem.LocalStepProtocolStep
import Leader.PPL.MainTheorem.WindowSPLEntryDynamicPadding
import Init.Omega

/-!
P_PL Theorem 1 cleanup, phase 2: the declarations of this file that served only the old
psi <= log2 n + 1 route to `theorem1Statement_proved` moved to
`Leader/Superseded/Theorem1LogWindow/Theorem1CostFrom13.lean`, namespace `PPL.Superseded.LogWindow`: `Theorem1TinyProducerFrom13`, `theorem1From13_coeff4_lt`, `theorem1From13_coeff1_lt`, `theorem1From27_globalFiveCoeff_lt`.
-/

namespace PPL

open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail
open PPLLResearchFormulation
open PPLLTraceConvergence
open PPLLSchedulerBlocks
open PPLLClosedDomainSchedulerAmplificationSol

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

theorem theorem1From13_coeff12_lt
    {n : Nat}
    (hn13 : 13 ≤ n) :
    12 < n := by
  omega

theorem theorem1From13_coeff8_lt
    {n : Nat}
    (hn13 : 13 ≤ n) :
    8 < n := by
  omega

theorem theorem1From13_quietTailCoeff_lt
    {n : Nat}
    (hn13 : 13 ≤ n) :
    4 + 1 + 1 < n := by
  omega

/--
If not every element of a finite list is bad, extract an explicit
good element.  This is intentionally proved by list induction, with no
classical contradiction step.
-/
private theorem q20289_exists_false_of_countP_lt
    {A : Type}
    (xs : List A)
    (bad : A → Bool)
    (hcount : xs.countP bad < xs.length) :
    ∃ x : A,
      x ∈ xs ∧
        bad x = false := by
  induction xs with
  | nil =>
      simp at hcount
  | cons a rest ih =>
      cases ha : bad a with
      | false =>
          exact
            ⟨a,
              List.mem_cons.mpr (Or.inl rfl),
              ha⟩
      | true =>
          have hrest :
              rest.countP bad < rest.length := by
            simpa [List.countP_cons, ha]
              using hcount
          obtain ⟨x, hx, hbad⟩ := ih hrest
          exact
            ⟨x,
              List.mem_cons.mpr (Or.inr hx),
              hbad⟩

/--
Generic one-phase count-to-existence selector.

A phase bad-count bound with coefficient c < n cannot cover all n^H
scheduler words.  Hence an actual length-H scheduler word with bad=false
exists.
-/
theorem theorem1From13_selectGoodSchedule
    {n H c : Nat}
    (hn : 0 < n)
    (hc : c < n)
    (bad : DetSchedule n → Bool)
    (hcount :
      n * (allSchedules n H).countP bad ≤
        c * n ^ H) :
    ∃ word : DetSchedule n,
      word ∈ allSchedules n H ∧
        word.length = H ∧
        bad word = false := by
  have hpow :
      0 < n ^ H :=
    Nat.pow_pos hn

  have hcoeff :
      c * n ^ H < n * n ^ H :=
    (Nat.mul_lt_mul_right hpow).2 hc

  have hmul :
      n * (allSchedules n H).countP bad <
        n * n ^ H :=
    Nat.lt_of_le_of_lt hcount hcoeff

  have hbadLt :
      (allSchedules n H).countP bad <
        n ^ H :=
    (Nat.mul_lt_mul_left hn).mp hmul

  have hbadLen :
      (allSchedules n H).countP bad <
        (allSchedules n H).length := by
    rw [allSchedules_length]
    exact hbadLt

  obtain ⟨word, hmem, hgood⟩ :=
    q20289_exists_false_of_countP_lt
      (allSchedules n H) bad hbadLen

  exact
    ⟨word,
      hmem,
      allSchedules_schedule_length
        n H word hmem,
      hgood⟩

end PPL

#print axioms PPL.theorem1From13_selectGoodSchedule

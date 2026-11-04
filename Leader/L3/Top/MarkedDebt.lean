import Leader.L3.Top.ClockCuts
import Leader.L3.ProbStages

/-!
# Q7: phase P.4--P.5 (marked debt), the stochastic reduction

`TopClockMarkedDebtPhase` asks, from every first-tail cut, for the expected
time to a coloured cut (or a strict stop) at most `n * R(r)`,
`R(r) = 4 r^2 + 4 r` (P.4--P.5, lines 280--310).  The paper's argument is a
finite job count: every job is one nominated physical edge service; an
unrelated service never raises the count; the nominated service lowers it.

`TopMarkedDebtRows` is exactly this job count, as a potential on the
fixed-trace state.  `topClockMarkedDebtPhaseOfRows` proves the phase from
the rows with no further input: the `n`-fold waiting time of a nominated edge
is the exact first-hit recursion, no independence is used.
-/

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Strengthening the target on a closed class costs nothing.

Consumer: `topMarkedCostOfRows`. -/
theorem topMarkedCostTargetOnClosed {m : Nat} {S : Type}
    (next : S → Fin m → S) (I P Q : S → Prop)
    (hstep : ∀ x, I x → ∀ e, I (next x e))
    (hstop : ∀ x, I x → Q x → P x) :
    ∀ T x, I x →
      costNumerator next P x T ≤ costNumerator next Q x T := by
  classical
  intro T
  induction T with
  | zero =>
      intro x hx
      simp only [costNumerator_zero]
      exact Nat.le_refl 0
  | succ T ih =>
      intro x hx
      by_cases hp : P x
      · rw [costNumerator_terminal next P x hp (T + 1)]
        exact Nat.zero_le _
      · have hq : ¬ Q x := by
          intro h
          exact hp (hstop x hx h)
        rw [costNumerator_succ next P x hp T,
          costNumerator_succ next Q x hq T]
        exact Nat.add_le_add_left
          (ofFn_sum_le
            (fun e : Fin m => costNumerator next P (next x e) T)
            (fun e : Fin m => costNumerator next Q (next x e) T)
            (fun e => ih (next x e) (hstep x hx e))) _

/-- **Nominated-edge potential on a closed class.**  On a class `I` closed
under every edge, a potential that never rises off the target `P` (a
successor is in `P` or has potential at most the present one), strictly
drops at one nominated edge (successor in `P` or potential smaller by one),
and is positive off `P`, bounds the first-hit cost by `n^T * (n * Φ x)`.

Consumer: `topClockMarkedDebtPhaseOfRows`. -/
theorem topMarkedCostOfRows {S : Type} {n : Nat}
    (next : S → Fin n → S) (I P : S → Prop) (Φ : S → Nat)
    (chosen : S → Fin n)
    (hclosed : ∀ x, I x → ∀ e, I (next x e))
    (hpos : ∀ x, I x → ¬ P x → 0 < Φ x)
    (hnon : ∀ x, I x → ¬ P x → ∀ e, P (next x e) ∨ Φ (next x e) ≤ Φ x)
    (hdrop : ∀ x, I x → ¬ P x →
      P (next x (chosen x)) ∨ Φ (next x (chosen x)) + 1 ≤ Φ x) :
    ∀ x, I x → ∀ T, costNumerator next P x T ≤ n ^ T * (n * Φ x) := by
  classical
  let P' : S → Prop := fun x => P x ∨ ¬ I x
  let Φ' : S → Nat := fun x => if P' x then 0 else Φ x
  have hdrop' : ∀ x, ¬ P' x → Φ' (next x (chosen x)) + 1 ≤ Φ' x := by
    intro x hx
    have hxI : I x := by
      by_cases h : I x
      · exact h
      · exact absurd (Or.inr h) hx
    have hxP : ¬ P x := fun h => hx (Or.inl h)
    have hnI : I (next x (chosen x)) := hclosed x hxI _
    have hΦx : Φ' x = Φ x := by simp [Φ', hx]
    rw [hΦx]
    rcases hdrop x hxI hxP with h | h
    · have : P' (next x (chosen x)) := Or.inl h
      simp only [Φ', this, if_true]
      exact hpos x hxI hxP
    · by_cases hP : P' (next x (chosen x))
      · simp only [Φ', hP, if_true]
        exact hpos x hxI hxP
      · simp only [Φ', hP, if_false]
        exact h
  have hnon' : ∀ x, ¬ P' x → ∀ e, Φ' (next x e) ≤ Φ' x := by
    intro x hx e
    have hxI : I x := by
      by_cases h : I x
      · exact h
      · exact absurd (Or.inr h) hx
    have hxP : ¬ P x := fun h => hx (Or.inl h)
    have hΦx : Φ' x = Φ x := by simp [Φ', hx]
    rw [hΦx]
    rcases hnon x hxI hxP e with h | h
    · have : P' (next x e) := Or.inl h
      simp only [Φ', this, if_true]
      exact Nat.zero_le _
    · by_cases hP : P' (next x e)
      · simp only [Φ', hP, if_true]
        exact Nat.zero_le _
      · simp only [Φ', hP, if_false]
        exact h
  have hmain := Prob.costNumerator_le_of_nominated_edge next P' Φ' chosen
    hdrop' hnon'
  intro x hx T
  have h1 := topMarkedCostTargetOnClosed next I P P' hclosed
    (fun y hy hyP => by
      rcases hyP with h | h
      · exact h
      · exact absurd hy h) T x hx
  have h2 := hmain x T
  have hle : Φ' x ≤ Φ x := by
    by_cases h : P' x
    · simp only [Φ', h, if_true]
      exact Nat.zero_le _
    · simp only [Φ', h, if_false]
      exact Nat.le_refl _
  exact Nat.le_trans h1 (Nat.le_trans h2
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hle)))

/-! ## The marked-debt rows and the phase -/

/-- The job count of P.4--P.5 as data: a potential on the fixed-trace
state, positive off the target, never raised by any edge, lowered by a
nominated edge, and at most `R(r)` at every first-tail cut.  Each field is
one of the paper's counting steps; the stochastic argument is not assumed.

Consumer: `topClockMarkedDebtPhaseOfRows`. -/
structure TopMarkedDebtRows {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (cuts : TopClockCutClasses ring C s) where
  pot : TopFixedTraceState n → Nat
  chosen : TopFixedTraceState n → Fin n
  start : ∀ Z, cuts.firstTail Z → pot Z ≤ topClockR (topClockSpan n)
  positive : ∀ Z, topClockReached ring C Z →
    ¬ topClockStopOr ring C s cuts.coloured Z → 0 < pot Z
  nonincrease : ∀ Z, topClockReached ring C Z →
    ¬ topClockStopOr ring C s cuts.coloured Z → ∀ e : Fin n,
      topClockStopOr ring C s cuts.coloured (topFixedTraceNext ring C Z e) ∨
        pot (topFixedTraceNext ring C Z e) ≤ pot Z
  progress : ∀ Z, topClockReached ring C Z →
    ¬ topClockStopOr ring C s cuts.coloured Z →
      topClockStopOr ring C s cuts.coloured
          (topFixedTraceNext ring C Z (chosen Z)) ∨
        pot (topFixedTraceNext ring C Z (chosen Z)) + 1 ≤ pot Z

/-- **P.4--P.5 from the marked-debt rows.**  From every strict stop or
first-tail cut the expected time to a strict stop or coloured cut is at most
`n * R(r)`.

Consumer: `TopClockPhaseBundle.marked` (TopClockAssembly). -/
theorem topClockMarkedDebtPhaseOfRows {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (cuts : TopClockCutClasses ring C s) (hn : 0 < n)
    (rows : TopMarkedDebtRows ring C s cuts) :
    TopClockMarkedDebtPhase ring C s cuts := by
  classical
  intro Z hZ
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (topFixedTraceNext ring C)
    (topClockStopOr ring C s cuts.coloured)
    hn Z (n * topClockR (topClockSpan n))).2
  intro T
  by_cases hstop : topClockStopOr ring C s cuts.coloured Z
  · rw [costNumerator_terminal _ _ Z hstop T]
    exact Nat.zero_le _
  · have hfirst : cuts.firstTail Z := by
      rcases hZ with h | h
      · exact absurd (Or.inl h) hstop
      · exact h
    have hreach : topClockReached ring C Z :=
      (cuts.firstTailSpec Z hfirst).1
    have hcost := topMarkedCostOfRows
      (topFixedTraceNext ring C)
      (topClockReached ring C)
      (topClockStopOr ring C s cuts.coloured)
      rows.pot rows.chosen
      (fun Y hY e => topClockReachedNext ring C Y e hY)
      rows.positive rows.nonincrease rows.progress Z hreach T
    exact Nat.le_trans hcost
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (rows.start Z hfirst)))

#print axioms topMarkedCostOfRows
#print axioms topClockMarkedDebtPhaseOfRows

end L3

import Leader.L3.Top.SettledPotentialWork
import Leader.L3.ProbStages

/-!
# Q7 (P.6--P.10): the levels of the charge

One level of the charge costs at most `n (3 r) + n (2 r^2 + r + 3)`; the number of levels is the
initial charge plus one.

Consumer: `Leader/L3/Top/SettledPotentialPhase.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- Enlarging the target keeps an expected-time bound.

Consumer: `phase_level`. -/
theorem eht_mono {S : Type} {n : Nat} (next : S → Fin n → S) (hn : 0 < n) (P Q : S → Prop)
    (hPQ : ∀ x, P x → Q x) (x : S) (B : Nat)
    (h : UniformFirstHit.ExpectedHittingTimeAtMost next P x (B : Rat)) :
    UniformFirstHit.ExpectedHittingTimeAtMost next Q x (B : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost next Q hn x B).2
  intro T
  have h1 := (UniformFirstHit.expectedHittingTimeAtMost_iff_cost next P hn x B).1 h T
  exact Nat.le_trans (L3.Prob.costNumerator_target_mono next P Q hPQ x T) h1

/-- The cost of one level of the charge.

Consumer: `levels_expected`. -/
def levelCost (n r : Nat) : Nat := n * (3 * r) + n * (2 * (r * r) + r + 3)

/-- **One level.**  From a reached pinned state with a barrier and a sound colouring of charge
at most `a`, the charge falls below `a`, or no settled input remains.

Consumer: `levels_expected`. -/
theorem phase_level {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (a : Nat) (Z : TopFixedTraceState n) (d : Nat → Prop)
    (h : PInv ring C s (Z, d))
    (hA : charge (topClockSpan n) (act (topClockSpan n) (cellOf s Z) d) ≤ a) :
    UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C) (WorkTarget ring C s a) Z
      ((levelCost n (topClockSpan n) : Nat) : Rat) := by
  have hn : 0 < n := by have := hg.hn; omega
  let Amid : TopFixedTraceState n → Prop := fun Y => StateInv ring C s Y ∧ ∃ d, ColourInv s Y d ∧
    charge (topClockSpan n) (act (topClockSpan n) (cellOf s Y) d) ≤ a ∧
    Mn (topClockSpan n) (cellOf s Y) d = 0
  have h1 : UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C)
      (fun Y => Amid Y ∨ WorkTarget ring C s a Y) Z ((n * (3 * topClockSpan n) : Nat) : Rat) := by
    refine eht_mono _ hn (FrontTarget ring C s a) _ ?_ Z _ (stage_front ring C s hg a Z d h hA)
    intro Y hY
    rcases hY with hY | ⟨hJ, d', hc, hch, hor⟩
    · exact Or.inr (Or.inl hY)
    · rcases hor with hlt | hff
      · exact Or.inr (Or.inr ⟨hJ, d', hc, hlt⟩)
      · exact Or.inl ⟨hJ, d', hc, hch, frontfree_mn_zero _ _ _ hc.2.2.1 hc.2.2.2 hff⟩
  have h2 : ∀ y, Amid y → UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C)
      (WorkTarget ring C s a) y ((n * (2 * (topClockSpan n * topClockSpan n) + topClockSpan n + 3) : Nat) : Rat) := by
    intro y ⟨hJ, d', hc, hch, hz⟩
    exact stage_work ring C s hg a y d' ⟨hJ, hc⟩ hch hz
  exact L3.Prob.expectedHittingTimeAtMost_stage_le (topFixedTraceNext ring C) hn Z Amid
    (WorkTarget ring C s a) _ _ h1 h2

/-- **The levels.**  From a reached pinned state with a barrier and a sound colouring of charge
below `a`, no settled input remains within `a` levels.

Consumer: `Leader/L3/Top/SettledPotentialPhase.lean`. -/
theorem levels_expected {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) :
    ∀ (a : Nat) (Z : TopFixedTraceState n) (d : Nat → Prop), PInv ring C s (Z, d) →
      charge (topClockSpan n) (act (topClockSpan n) (cellOf s Z) d) < a →
      UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C)
        (fun Y => ¬ SettledAt s Y) Z ((a * levelCost n (topClockSpan n) : Nat) : Rat) := by
  have hn : 0 < n := by have := hg.hn; omega
  intro a
  induction a with
  | zero =>
      intro Z d _ hlt
      exact absurd hlt (Nat.not_lt_zero _)
  | succ a ih =>
      intro Z d h hlt
      have h1 : UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C)
          (fun Y => (StateInv ring C s Y ∧ ∃ d, ColourInv s Y d ∧
            charge (topClockSpan n) (act (topClockSpan n) (cellOf s Y) d) < a) ∨ ¬ SettledAt s Y)
          Z ((levelCost n (topClockSpan n) : Nat) : Rat) := by
        refine eht_mono _ hn (WorkTarget ring C s a) _ ?_ Z _
          (phase_level ring C s hg a Z d h (by omega))
        intro Y hY
        rcases hY with hY | hY
        · exact Or.inr hY
        · exact Or.inl hY
      have h2 : ∀ y, (StateInv ring C s y ∧ ∃ d, ColourInv s y d ∧
            charge (topClockSpan n) (act (topClockSpan n) (cellOf s y) d) < a) →
          UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C)
            (fun Y => ¬ SettledAt s Y) y ((a * levelCost n (topClockSpan n) : Nat) : Rat) := by
        intro y ⟨hJ, d', hc, hch⟩
        exact ih y d' ⟨hJ, hc⟩ hch
      have := L3.Prob.expectedHittingTimeAtMost_stage_le (topFixedTraceNext ring C) hn Z
        (fun Y => StateInv ring C s Y ∧ ∃ d, ColourInv s Y d ∧
          charge (topClockSpan n) (act (topClockSpan n) (cellOf s Y) d) < a)
        (fun Y => ¬ SettledAt s Y) _ _ h1 h2
      have e : (a + 1) * levelCost n (topClockSpan n) =
          levelCost n (topClockSpan n) + a * levelCost n (topClockSpan n) := by
        rw [Nat.succ_mul, Nat.add_comm]
      rw [e]
      exact this

end MarkedCells
end L3

#print axioms L3.MarkedCells.levels_expected

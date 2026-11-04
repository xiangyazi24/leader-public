import Leader.L3.Top.SettledWorkFrontTrace
import Leader.L3.Top.SettledWorkLift

/-!
# Q7 (P.7): expected time to clear the erasure fronts

From a coloured cut, the expected number of scheduler interactions until the target window has
no erasure front or no settled input is at most `n (r^2 (3 r + 1) + 3 r)`, `r = topClockSpan n`.

The potential is the lexicographic `(A, M)` of the history colouring, which is not a function
of the state alone; the bound is obtained on the product chain `(state, colouring)` and
transferred back to the state chain by `costNumerator_lift`.

Consumer: `Leader/L3/TopSettledWork.lean` (not yet written): the front part of P.7.
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- No erasure front in the target window.

Consumer: `front_clear_expected`. -/
def FrontFree {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) : Prop :=
  ∀ p, p < topClockSpan n → (cellOf s Y p).i ≠ .x

/-- Not front-free means a front exists.

Consumer: `front_clear_expected`. -/
theorem exists_front {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) (h : ¬ FrontFree s Y) :
    ∃ p, p < topClockSpan n ∧ (cellOf s Y p).i = .x := by
  apply Classical.byContradiction
  intro hno
  apply h
  intro p hp hpx
  exact hno ⟨p, hp, hpx⟩

/-- A witnessed member makes the count positive.

Consumer: `front_clear_expected`. -/
theorem cnt_pos (P : Nat → Bool) (q : Nat) (hq : P q = true) :
    ∀ r, q < r → 0 < cnt P r
  | 0 => fun h => by omega
  | k + 1 => fun hk => by
      simp only [cnt]
      by_cases hkq : q = k
      · subst hkq; simp [hq]
      · have := cnt_pos P q hq k (by omega)
        omega

/-- The edge chosen at a state: the edge of some front, if there is one.

Consumer: `front_clear_expected`. -/
noncomputable def frontEdge {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) : Fin n :=
  if h : ∃ p, p < topClockSpan n ∧ (cellOf s Y p).i = .x then winSite s (Classical.choose h)
  else s

/-- **Expected time to clear the erasure fronts.**  From a coloured cut, at an eligible
entrance, the expected time to reach a state with no settled input or no erasure front in the
target window is at most `n (r^2 (3 r + 1) + 3 r)`.

Consumer: `Leader/L3/TopSettledWork.lean` (not yet written). -/
theorem front_clear_expected {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Y0 : TopFixedTraceState n)
    (hcol : topClockConcreteColoured ring C s Y0) :
    UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C)
      (fun Y => ¬ SettledAt s Y ∨ FrontFree s Y) Y0
      ((n * (topClockSpan n * topClockSpan n * (3 * topClockSpan n + 1) +
        3 * topClockSpan n) : Nat) : Rat) := by
  have hn : 0 < n := by have := hg.hn; omega
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (topFixedTraceNext ring C) (fun Y => ¬ SettledAt s Y ∨ FrontFree s Y) hn Y0 _).2
  intro T
  obtain ⟨hreach, _, hbar, hgap, _, _⟩ := hcol
  have h0 : ColourInv s Y0 allActive := by
    refine ⟨inv_reached ring C s hg Y0 hreach, noInh_of_gap s Y0 hgap, ?_, ?_⟩
    · intro u hu; exact absurd hu (by simp [allActive])
    · intro u hu; exact absurd hu (by simp [allActive])
  let S' := TopFixedTraceState n × (Nat → Prop)
  let next' : S' → Fin n → S' := fun x e =>
    (topFixedTraceNext ring C x.1 e, colourNext ring C s x.1 e x.2)
  let I : S' → Prop := fun x => topClockReached ring C x.1 ∧ ColourInv s x.1 x.2 ∧
    Barrier (topClockSpan n) (cellOf s x.1)
  let P' : S' → Prop := fun x => ¬ SettledAt s x.1 ∨ FrontFree s x.1
  let Φ : S' → Nat := fun x => Pot (topClockSpan n) (cellOf s x.1) x.2
  let chosen : S' → Fin n := fun x => frontEdge s x.1
  have hcost := topMarkedCostOfRows next' I P' Φ chosen
    (by
      intro x hx e
      obtain ⟨hr, hc, hb⟩ := hx
      refine ⟨topClockReachedNext ring C x.1 e hr,
        cover_step_machine ring C s hg x.1 hr x.2 e hc,
        barrier_next ring C s hg x.1 hr e hc.2.1 hb⟩)
    (by
      intro x hx hnot
      have hS : SettledAt s x.1 := by
        by_cases h : SettledAt s x.1
        · exact h
        · exact absurd (Or.inl h) hnot
      have hF : ¬ FrontFree s x.1 := fun h => hnot (Or.inr h)
      obtain ⟨p, hp, hpx⟩ := exists_front s x.1 hF
      show 0 < Pot _ _ _
      unfold Pot Mn Xn
      have := cnt_pos (fun k => decide ((cellOf s x.1 k).i = .x)) p (by simpa using hpx)
        (topClockSpan n) hp
      omega)
    (by
      intro x hx hnot e
      right
      obtain ⟨hr, hc, hb⟩ := hx
      have hS : SettledAt s x.1 := by
        by_cases h : SettledAt s x.1
        · exact h
        · exact absurd (Or.inl h) hnot
      exact (pot_step_machine ring C s hg x.1 hr x.2 e hc hb hS).2)
    (by
      intro x hx hnot
      right
      obtain ⟨hr, hc, hb⟩ := hx
      have hS : SettledAt s x.1 := by
        by_cases h : SettledAt s x.1
        · exact h
        · exact absurd (Or.inl h) hnot
      have hF : ¬ FrontFree s x.1 := fun h => hnot (Or.inr h)
      have hex := exists_front s x.1 hF
      have hsel : chosen x = winSite s (Classical.choose hex) := by
        show frontEdge s x.1 = _
        unfold frontEdge
        rw [dif_pos hex]
      have hspec := Classical.choose_spec hex
      show Pot _ _ _ + 1 ≤ Pot _ _ _
      rw [hsel]
      exact front_step_machine ring C s hg x.1 hr x.2 _ hspec.1 hc hb hS hspec.2)
    (Y0, allActive) ⟨hreach, h0, barrier_of_moving s Y0 hbar⟩ T
  have hlift := costNumerator_lift (topFixedTraceNext ring C)
    (fun Y => ¬ SettledAt s Y ∨ FrontFree s Y) next' P' Prod.fst
    (fun x e => rfl) (fun x => Iff.rfl) (Y0, allActive) T
  rw [← hlift]
  refine Nat.le_trans hcost ?_
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul_left
  have h2 := charge_le (act (topClockSpan n) (cellOf s Y0) allActive) (topClockSpan n)
  have h3 := Mn_le (topClockSpan n) (cellOf s Y0) allActive
  have h4 := Nat.mul_le_mul_right (3 * topClockSpan n + 1) h2
  show Pot (topClockSpan n) (cellOf s Y0) allActive ≤ _
  unfold Pot
  omega

end MarkedCells
end L3

#print axioms L3.MarkedCells.front_clear_expected

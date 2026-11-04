import Leader.L3.Top.SettledPotentialMachine

/-!
# Q7 (P.8--P.10): the source distance along one edge, including the zero case

A source distance of zero (a sampled token at the source terminal) is kept by every edge except
the port edge when the border register of the target window accepts.

Consumer: `Leader/L3/Top/SettledPotentialStep.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- A sampled token at the terminal stays unless the port edge accepts it.

Consumer: `dist_next`. -/
theorem dist_zero_step (r : Nat) (hr : 3 ≤ r) (src : Nat → Tok) (acc : Bool) (j : Nat)
    (hj : j < r) (h : dist r src = 0) :
    dist r (srcStepAt r acc src j) = 0 ∨ (j + 1 = r ∧ acc = true) := by
  have hD := (dist_zero_iff r (by omega) src).1 h
  by_cases hint : j + 1 < r
  · left
    rw [dist_zero_iff r (by omega)]
    by_cases hj1 : j + 1 = r - 1
    · have e1 : r - 1 = j + 1 := by omega
      rw [e1, srcStepAt_resp r acc src j hint]
      rw [e1] at hD
      have hyD := hD
      generalize src j = x
      generalize src (j + 1) = y at hyD ⊢
      cases x <;> cases y <;> simp [srcPair, Tok.isD] at hyD ⊢
    · rw [srcStepAt_far r acc src j hint (r - 1) (by omega) (by omega)]
      exact hD
  · have hjr : j + 1 = r := by omega
    by_cases hacc : acc = true
    · right; exact ⟨hjr, hacc⟩
    · left
      have hacc' : acc = false := by simpa using hacc
      rw [dist_zero_iff r (by omega)]
      have e1 : r - 1 = j := by omega
      rw [e1, srcStepAt_portSrc r acc src j hint]
      rw [e1] at hD
      have hyD := hD
      generalize src j = x at hyD ⊢
      cases x <;> simp [srcPair, Tok.isD, hacc'] at hyD ⊢

/-- The window sites are not the port site of the source block.

Consumer: `dist_next`. -/
theorem winSite_ne_portSite {n : Nat} (hn : 5 ≤ n) (s : Fin n) (p : Nat) (hp : p < topClockSpan n) :
    winSite s p ≠ certSite s (topClockSpan n - 1) := by
  intro h
  have hr := span_lt_n hn
  have hr3 := span_ge_three hn
  unfold winSite at h
  have := certSite_inj_close s (topClockSpan n - 1) (topClockSpan n + p) (by omega)
    (by omega) h.symm
  omega

/-- **The source distance along one edge.**  It does not rise, except that a zero distance may
become positive when the port edge accepts.

Consumer: `Leader/L3/Top/SettledPotentialStep.lean`. -/
theorem dist_next {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Z : TopFixedTraceState n) (hreach : topClockReached ring C Z)
    (e : Fin n) :
    dist (topClockSpan n) (srcOf s (topFixedTraceNext ring C Z e)) ≤
      dist (topClockSpan n) (srcOf s Z) ∨
    (dist (topClockSpan n) (srcOf s Z) = 0 ∧ e = certSite s (topClockSpan n - 1) ∧
      accOf s Z = true) := by
  have hr3 := span_ge_three hg.hn
  by_cases hd : dist (topClockSpan n) (srcOf s Z) = 0
  · by_cases ha : ∃ j, j < topClockSpan n ∧ e = certSite s j
    · obtain ⟨j, hj, rfl⟩ := ha
      have hl := src_link_edge ring C s Z hg hreach j hj
      have heq : dist (topClockSpan n) (srcOf s (topFixedTraceNext ring C Z (certSite s j))) =
          dist (topClockSpan n) (srcStepAt (topClockSpan n) (accOf s Z) (srcOf s Z) j) :=
        dist_congr _ _ _ hl
      rcases dist_zero_step (topClockSpan n) hr3 (srcOf s Z) (accOf s Z) j hj hd with h1 | ⟨h1, h2⟩
      · left; rw [heq, h1]; omega
      · right
        refine ⟨hd, ?_, h2⟩
        have : j = topClockSpan n - 1 := by omega
        rw [this]
    · left
      have hl := src_link_away ring C s Z hg hreach e (fun j hj h => ha ⟨j, hj, h⟩)
      rw [dist_congr _ _ _ hl]
      exact Nat.le_refl _
  · left
    obtain ⟨_, _, h3, _, _⟩ := topSettledSourceDeliver ring C s hg
    exact h3 Z hreach hd e

end MarkedCells
end L3

#print axioms L3.MarkedCells.dist_next
#print axioms L3.MarkedCells.winSite_ne_portSite

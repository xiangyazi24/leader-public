import Leader.L3.Top.SettledPotentialLevels

/-!
# Q7 (P.6--P.10): from the cell invariants to the concrete settled-empty class

A reached pinned state whose window has no settled input, with a sound colouring, is in the
pinned settled-empty class.

Consumer: `Leader/L3/Top/SettledPotentialPhase.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- An empty abstract input is an empty physical input.

Consumer: `gap_of_inv`. -/
theorem inTok_E_of_abs {a : Nat} (q : InTok a) (h : absIn q = .e) : q = .E := by
  cases q with
  | E => rfl
  | X => simp [absIn] at h
  | P v t => cases t <;> simp [absIn] at h
  | S v t => cases t <;> simp [absIn] at h

/-- A live physical carry without an inherited cell class has a fresh ledger.

Consumer: `gap_of_inv`. -/
theorem carryL_fresh {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) (j : Nat)
    (hj : j < topClockSpan n) (hni : NoInh (topClockSpan n) (cellOf s Y))
    (hL : (Y.1.1 (certSite s (topClockSpan n + j))).qCarry.isL = true) :
    (cellOf s Y j).c = .fresh ∧
      ∃ ledger : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n,
        (Y.1.2.current (certSite s (topClockSpan n + j))).comparison.carry = some ledger ∧
        ledger.inherited = none := by
  have hcell : (cellOf s Y j).c = absCar (Y.1.1 (certSite s (topClockSpan n + j))).qCarry
      (Y.1.2.current (certSite s (topClockSpan n + j))).comparison.carry := rfl
  have hc : absCar (Y.1.1 (certSite s (topClockSpan n + j))).qCarry
      (Y.1.2.current (certSite s (topClockSpan n + j))).comparison.carry ≠ .inh := by
    rw [← hcell]; exact hni j hj
  rw [hcell]
  generalize (Y.1.2.current (certSite s (topClockSpan n + j))).comparison.carry = g at hc ⊢
  generalize (Y.1.1 (certSite s (topClockSpan n + j))).qCarry = q at hc hL ⊢
  cases q with
  | OFF => simp [QCarry.isL] at hL
  | L a b =>
      cases g with
      | none => simp [absCar] at hc
      | some l =>
          by_cases hi : l.inherited.isNone = true
          · exact ⟨by simp [absCar, hi], l, rfl, by simpa using hi⟩
          · simp [absCar, hi] at hc

/-- **The carry gap of the cut** from the fresh-carry invariants.

Consumer: `settledEmpty_of_clear`. -/
theorem gap_of_inv {n : Nat} (s : Fin n) (Y : TopFixedTraceState n)
    (hinv : Inv (topClockSpan n) (cellOf s Y)) (hni : NoInh (topClockSpan n) (cellOf s Y)) :
    topClockConcreteGeneratedCarryGap s Y := by
  intro j hL
  have hjl := j.isLt
  obtain ⟨hfresh, hled⟩ := carryL_fresh s Y j.val hjl hni hL
  obtain ⟨hhost, hleft⟩ := hinv.1 j.val hjl hfresh
  refine ⟨?_, ?_, ?_, hled⟩
  · exact inTok_E_of_abs _ hhost
  · intro i hi
    rcases hleft i.val hi with h1 | h1
    · left
      have : (Y.1.1 (certSite s (topClockSpan n + i.val))).qIn = .E :=
        inTok_E_of_abs _ h1
      show (Y.1.1 (certSite s (topClockSpan n + i.val))).qIn.isE = true
      rw [this]; rfl
    · right
      have h2 : (Y.1.1 (winSite s i.val)).qIn.isP = true := by
        rw [← siteCell_isP]; exact h1
      exact h2
  · intro k hk
    obtain ⟨hfk, _⟩ := carryL_fresh s Y k.val k.isLt hni hk
    exact Fin.ext (hinv.2 k.val j.val k.isLt hjl hfk hfresh)

/-- **The cell barrier is the concrete moving barrier.**

Consumer: `settledEmpty_of_clear`. -/
theorem moving_of_barrier {n : Nat} (s : Fin n) (Y : TopFixedTraceState n)
    (h : Barrier (topClockSpan n) (cellOf s Y)) : topClockConcreteMovingBarrier s Y := by
  intro i j hP hobs
  apply h i.val j.val i.isLt j.isLt
  · unfold cellOf
    rw [siteCell_isP]
    exact hP
  · unfold cellOf
    rw [siteCell_obC]
    rcases hobs with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)

/-- A window without a settled input has the settled-empty target shape.

Consumer: `settledEmpty_of_clear`. -/
theorem target_of_notSettled {n : Nat} (s : Fin n) (Y : TopFixedTraceState n)
    (hns : ¬ SettledAt s Y) : topClockTargetSettledEmpty s Y := by
  intro j
  have h1 : ¬ ((cellOf s Y j.val).i.isS = true) := fun h => hns ⟨j.val, j.isLt, h⟩
  unfold cellOf at h1
  rw [isS_link] at h1
  cases h : (Y.1.1 (certSite s (topClockSpan n + j.val))).qIn.isS
  · rfl
  · exact absurd h h1

/-- **A cleared window is in the settled-empty class.**

Consumer: `Leader/L3/Top/SettledPotentialPhase.lean`. -/
theorem settledEmpty_of_clear {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Y : TopFixedTraceState n) (hJ : StateInv ring C s Y)
    (d : Nat → Prop) (hc : ColourInv s Y d) (hns : ¬ SettledAt s Y) :
    (topClockPinnedClasses ring C s).settledEmpty Y := by
  obtain ⟨hr, hpin, hbar⟩ := hJ
  refine ⟨hpin, ⟨hr, markedDown_pure ring C s Y (pinned_down ring C s Y hpin),
    target_of_notSettled s Y hns⟩, moving_of_barrier s Y hbar,
    gap_of_inv s Y hc.1 hc.2.1, ?_⟩
  obtain ⟨Y0, hcut, hmf, hold⟩ := hpin
  exact suffix_of_pinned ring C s hg Y0 Y hcut hmf hold

end MarkedCells
end L3

#print axioms L3.MarkedCells.gap_of_inv
#print axioms L3.MarkedCells.settledEmpty_of_clear

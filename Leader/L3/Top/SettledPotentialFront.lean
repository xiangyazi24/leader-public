import Leader.L3.Top.SettledPotentialInv
import Leader.L3.Top.SettledPotentialCost
import Leader.L3.Top.SettledWorkFrontClear

/-!
# Q7 (P.6--P.10), first stage: a level of the charge falls or the window becomes front-free

From a reached pinned state with a barrier and a sound colouring of charge at most `a`, the
expected time until no settled input remains, or the charge is below `a`, or the window has no
erasure front, is at most `n * 3 r`.

Consumer: `Leader/L3/Top/SettledPotentialLevels.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- **The row-descent cost bound on an absorbing chain.**  The hypotheses are only needed off
the target.

Consumer: `stage_front`. -/
theorem cost_rows_absorb {S : Type} {n : Nat} (next : S → Fin n → S) (I P : S → Prop)
    (Φ : S → Nat) (chosen : S → Fin n)
    (hclosed : ∀ x, I x → ¬ P x → ∀ e, I (next x e))
    (hpos : ∀ x, I x → ¬ P x → 0 < Φ x)
    (hnon : ∀ x, I x → ¬ P x → ∀ e, P (next x e) ∨ Φ (next x e) ≤ Φ x)
    (hdrop : ∀ x, I x → ¬ P x → P (next x (chosen x)) ∨ Φ (next x (chosen x)) + 1 ≤ Φ x) :
    ∀ x, I x → ∀ T, costNumerator next P x T ≤ n ^ T * (n * Φ x) := by
  intro x hx T
  rw [← costNumerator_absorb next P x T]
  have hab : ∀ y e, ¬ P y → absorb next P y e = next y e := fun y e h => by
    unfold absorb; rw [if_neg h]
  exact topMarkedCostOfRows (absorb next P) I P Φ chosen
    (by
      intro y hy e
      by_cases h : P y
      · unfold absorb; rw [if_pos h]; exact hy
      · rw [hab y e h]; exact hclosed y hy h e)
    hpos
    (by intro y hy hnot e; rw [hab y e hnot]; exact hnon y hy hnot e)
    (by intro y hy hnot; rw [hab y _ hnot]; exact hdrop y hy hnot)
    x hx T

/-- A count of nothing is zero.

Consumer: `frontfree_mn_zero`. -/
theorem cnt_eq_zero (P : Nat → Bool) : ∀ r, (∀ k, k < r → P k = false) → cnt P r = 0
  | 0, _ => rfl
  | k + 1, h => by
      have := cnt_eq_zero P k (fun j hj => h j (by omega))
      simp only [cnt]
      rw [h k (by omega)]
      simpa using this

/-- **A front-free window has no front debt**, since every doomed register is covered by a
front or by a doomed register to its left.

Consumer: `stage_front`. -/
theorem frontfree_mn_zero (r : Nat) (cells : Nat → Cell) (d : Nat → Prop)
    (hcov : Cover r cells d) (hlt : ∀ u, d u → u < r)
    (hff : ∀ p, p < r → (cells p).i ≠ .x) : Mn r cells d = 0 := by
  have hnd : ∀ m k, k ≤ m → ¬ d k := by
    intro m
    induction m with
    | zero =>
        intro k hk hd
        have := (hcov k hd).1
        omega
    | succ m ih =>
        intro k hk hd
        obtain ⟨hk0, _, hx | hd'⟩ := hcov k hd
        · exact hff (k - 1) (by have := hlt k hd; omega) hx
        · exact ih (k - 1) (by omega) hd'
  unfold Mn Dn Xn
  have h1 : cnt (fun k => decide (d k)) r = 0 :=
    cnt_eq_zero _ r (fun k _ => by simp [hnd k k (Nat.le_refl _)])
  have h2 : cnt (fun k => decide ((cells k).i = .x)) r = 0 :=
    cnt_eq_zero _ r (fun k hk => by simp [hff k hk])
  omega

/-- The target of the first stage.

Consumer: `stage_front`. -/
def FrontTarget {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n) (a : Nat)
    (Y : TopFixedTraceState n) : Prop :=
  ¬ SettledAt s Y ∨ (StateInv ring C s Y ∧ ∃ d, ColourInv s Y d ∧
    charge (topClockSpan n) (act (topClockSpan n) (cellOf s Y) d) ≤ a ∧
    (charge (topClockSpan n) (act (topClockSpan n) (cellOf s Y) d) < a ∨ FrontFree s Y))

/-- Off the target, a settled input, a full charge level and a front.

Consumer: `stage_front`. -/
theorem not_frontTarget {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (a : Nat) (Y : TopFixedTraceState n) (hnot : ¬ FrontTarget ring C s a Y) (hJ : StateInv ring C s Y)
    (d : Nat → Prop) (hc : ColourInv s Y d)
    (hA : charge (topClockSpan n) (act (topClockSpan n) (cellOf s Y) d) ≤ a) :
    SettledAt s Y ∧ a ≤ charge (topClockSpan n) (act (topClockSpan n) (cellOf s Y) d) ∧
      ¬ FrontFree s Y := by
  refine ⟨?_, ?_, ?_⟩
  · exact Classical.byContradiction fun h => hnot (Or.inl h)
  · exact Classical.byContradiction fun h => hnot (Or.inr ⟨hJ, d, hc, hA, Or.inl (by omega)⟩)
  · exact fun h => hnot (Or.inr ⟨hJ, d, hc, hA, Or.inr h⟩)

/-- **First stage.**  The expected time to the target `FrontTarget` is at most `n * 3 r`.

Consumer: `Leader/L3/Top/SettledPotentialLevels.lean`. -/
theorem stage_front {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (a : Nat) (Z : TopFixedTraceState n) (d : Nat → Prop)
    (h : PInv ring C s (Z, d))
    (hA : charge (topClockSpan n) (act (topClockSpan n) (cellOf s Z) d) ≤ a) :
    UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C) (FrontTarget ring C s a) Z
      ((n * (3 * topClockSpan n) : Nat) : Rat) := by
  have hn : 0 < n := by have := hg.hn; omega
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (topFixedTraceNext ring C) (FrontTarget ring C s a) hn Z _).2
  intro T
  let S' := TopFixedTraceState n × (Nat → Prop)
  let I : S' → Prop := fun x => PInv ring C s x ∧
    charge (topClockSpan n) (act (topClockSpan n) (cellOf s x.1) x.2) ≤ a
  let P' : S' → Prop := fun x => FrontTarget ring C s a x.1
  let Φ : S' → Nat := fun x => Mn (topClockSpan n) (cellOf s x.1) x.2
  have hcost := cost_rows_absorb (prodNext ring C s) I P' Φ (fun x => frontEdge s x.1)
    (by
      intro x hx hnot e
      obtain ⟨hp, hch⟩ := hx
      obtain ⟨hS, _, _⟩ := not_frontTarget ring C s a x.1 hnot hp.1 x.2 hp.2 hch
      refine ⟨pinv_next ring C s hg x e hp, ?_⟩
      exact Nat.le_trans (charge_step_machine ring C s hg x.1 hp.1.1 x.2 e hp.2 hp.1.2.2 hS).2 hch)
    (by
      intro x hx hnot
      obtain ⟨hp, hch⟩ := hx
      obtain ⟨hS, _, hF⟩ := not_frontTarget ring C s a x.1 hnot hp.1 x.2 hp.2 hch
      obtain ⟨p, hpl, hpx⟩ := exists_front s x.1 hF
      show 0 < Mn _ _ _
      unfold Mn Xn
      have := cnt_pos (fun k => decide ((cellOf s x.1 k).i = .x)) p (by simpa using hpx)
        (topClockSpan n) hpl
      omega)
    (by
      intro x hx hnot e
      obtain ⟨hp, hch⟩ := hx
      obtain ⟨hS, hle, _⟩ := not_frontTarget ring C s a x.1 hnot hp.1 x.2 hp.2 hch
      have hpc := pinv_next ring C s hg x e hp
      obtain ⟨_, hpot⟩ := pot_step_machine ring C s hg x.1 hp.1.1 x.2 e hp.2 hp.1.2.2 hS
      obtain ⟨_, hch'⟩ := charge_step_machine ring C s hg x.1 hp.1.1 x.2 e hp.2 hp.1.2.2 hS
      by_cases hlt : charge (topClockSpan n) (act (topClockSpan n)
          (cellOf s (topFixedTraceNext ring C x.1 e)) (colourNext ring C s x.1 e x.2)) < a
      · left
        exact Or.inr ⟨hpc.1, _, hpc.2, Nat.le_of_lt hlt, Or.inl hlt⟩
      · right
        have heq : charge (topClockSpan n) (act (topClockSpan n)
            (cellOf s (topFixedTraceNext ring C x.1 e)) (colourNext ring C s x.1 e x.2)) =
            charge (topClockSpan n) (act (topClockSpan n) (cellOf s x.1) x.2) := by omega
        unfold Pot at hpot
        rw [heq] at hpot
        show Mn (topClockSpan n) (cellOf s (topFixedTraceNext ring C x.1 e))
          (colourNext ring C s x.1 e x.2) ≤ Mn (topClockSpan n) (cellOf s x.1) x.2
        omega)
    (by
      intro x hx hnot
      obtain ⟨hp, hch⟩ := hx
      obtain ⟨hS, hle, hF⟩ := not_frontTarget ring C s a x.1 hnot hp.1 x.2 hp.2 hch
      have hpc := pinv_next ring C s hg x (frontEdge s x.1) hp
      have hex := exists_front s x.1 hF
      have hsel : frontEdge s x.1 = winSite s (Classical.choose hex) := by
        unfold frontEdge
        rw [dif_pos hex]
      have hspec := Classical.choose_spec hex
      have hpot := front_step_machine ring C s hg x.1 hp.1.1 x.2 _ hspec.1 hp.2 hp.1.2.2 hS hspec.2
      obtain ⟨_, hch'⟩ := charge_step_machine ring C s hg x.1 hp.1.1 x.2 (frontEdge s x.1) hp.2
        hp.1.2.2 hS
      rw [← hsel] at hpot
      by_cases hlt : charge (topClockSpan n) (act (topClockSpan n)
          (cellOf s (topFixedTraceNext ring C x.1 (frontEdge s x.1)))
          (colourNext ring C s x.1 (frontEdge s x.1) x.2)) < a
      · left
        exact Or.inr ⟨hpc.1, _, hpc.2, Nat.le_of_lt hlt, Or.inl hlt⟩
      · right
        have heq : charge (topClockSpan n) (act (topClockSpan n)
            (cellOf s (topFixedTraceNext ring C x.1 (frontEdge s x.1)))
            (colourNext ring C s x.1 (frontEdge s x.1) x.2)) =
            charge (topClockSpan n) (act (topClockSpan n) (cellOf s x.1) x.2) := by omega
        unfold Pot at hpot
        rw [heq] at hpot
        show Mn (topClockSpan n) (cellOf s (topFixedTraceNext ring C x.1 (frontEdge s x.1)))
          (colourNext ring C s x.1 (frontEdge s x.1) x.2) + 1 ≤
          Mn (topClockSpan n) (cellOf s x.1) x.2
        omega)
    (Z, d) ⟨h, hA⟩ T
  have hlift := costNumerator_lift (topFixedTraceNext ring C) (FrontTarget ring C s a) (prodNext ring C s)
    P' Prod.fst (fun x e => rfl) (fun x => Iff.rfl) (Z, d) T
  rw [← hlift]
  refine Nat.le_trans hcost ?_
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul_left
  exact Mn_le (topClockSpan n) (cellOf s Z) d

end MarkedCells
end L3

#print axioms L3.MarkedCells.stage_front
#print axioms L3.MarkedCells.frontfree_mn_zero

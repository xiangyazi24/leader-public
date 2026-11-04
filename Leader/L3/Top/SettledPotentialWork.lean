import Leader.L3.Top.SettledPotentialFront

/-!
# Q7 (P.6--P.10), second stage: a front-free window lowers its charge

From a reached pinned state with a barrier, a sound colouring of charge at most `a`, and no
front debt, the expected time until no settled input remains or the charge is below `a` is at
most `n (2 r^2 + r + 3)`, `r = topClockSpan n`.

Consumer: `Leader/L3/Top/SettledPotentialLevels.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The target of the second stage.

Consumer: `stage_work`. -/
def WorkTarget {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n) (a : Nat)
    (Y : TopFixedTraceState n) : Prop :=
  ¬ SettledAt s Y ∨ (StateInv ring C s Y ∧ ∃ d, ColourInv s Y d ∧
    charge (topClockSpan n) (act (topClockSpan n) (cellOf s Y) d) < a)

/-- The edge that strictly lowers the charge or the supply potential, if there is one.

Consumer: `stage_work`. -/
noncomputable def thEdge {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (x : TopFixedTraceState n × (Nat → Prop)) : Fin n :=
  if h : ∃ e : Fin n,
      charge (topClockSpan n) (act (topClockSpan n) (cellOf s (topFixedTraceNext ring C x.1 e))
          (colourNext ring C s x.1 e x.2)) <
        charge (topClockSpan n) (act (topClockSpan n) (cellOf s x.1) x.2) ∨
      (Mn (topClockSpan n) (cellOf s (topFixedTraceNext ring C x.1 e)) (colourNext ring C s x.1 e x.2)
          = 0 ∧ Th s (topFixedTraceNext ring C x.1 e) < Th s x.1)
  then Classical.choose h else s

/-- **Second stage.**

Consumer: `Leader/L3/Top/SettledPotentialLevels.lean`. -/
theorem stage_work {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (a : Nat) (Z : TopFixedTraceState n) (d : Nat → Prop)
    (h : PInv ring C s (Z, d))
    (hA : charge (topClockSpan n) (act (topClockSpan n) (cellOf s Z) d) ≤ a)
    (hM : Mn (topClockSpan n) (cellOf s Z) d = 0) :
    UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C) (WorkTarget ring C s a) Z
      ((n * (2 * (topClockSpan n * topClockSpan n) + topClockSpan n + 3) : Nat) : Rat) := by
  have hn : 0 < n := by have := hg.hn; omega
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (topFixedTraceNext ring C) (WorkTarget ring C s a) hn Z _).2
  intro T
  let S' := TopFixedTraceState n × (Nat → Prop)
  let I : S' → Prop := fun x => PInv ring C s x ∧
    charge (topClockSpan n) (act (topClockSpan n) (cellOf s x.1) x.2) ≤ a ∧
    (charge (topClockSpan n) (act (topClockSpan n) (cellOf s x.1) x.2) < a ∨
      Mn (topClockSpan n) (cellOf s x.1) x.2 = 0)
  let P' : S' → Prop := fun x => WorkTarget ring C s a x.1
  let Φ : S' → Nat := fun x => Th s x.1 + 1
  -- the facts available off the target
  have hoff : ∀ x : S', I x → ¬ P' x →
      SettledAt s x.1 ∧ Mn (topClockSpan n) (cellOf s x.1) x.2 = 0 := by
    intro x hx hnot
    obtain ⟨hp, hch, hor⟩ := hx
    refine ⟨Classical.byContradiction fun hS => hnot (Or.inl hS), ?_⟩
    rcases hor with hlt | hz
    · exact absurd (Or.inr ⟨hp.1, x.2, hp.2, hlt⟩) hnot
    · exact hz
  have hcost := cost_rows_absorb (prodNext ring C s) I P' Φ (thEdge ring C s)
    (by
      intro x hx hnot e
      obtain ⟨hS, hz⟩ := hoff x hx hnot
      obtain ⟨hp, hch, _⟩ := hx
      refine ⟨pinv_next ring C s hg x e hp, ?_, ?_⟩
      · exact Nat.le_trans
          (charge_step_machine ring C s hg x.1 hp.1.1 x.2 e hp.2 hp.1.2.2 hS).2 hch
      · rcases th_step ring C s hg x.1 hp.1.1 x.2 e hp.2 hp.1.2.2 hS hz with h1 | ⟨h2, _⟩
        · exact Or.inl (Nat.lt_of_lt_of_le h1 hch)
        · exact Or.inr h2)
    (by intro x _ _; exact Nat.succ_pos _)
    (by
      intro x hx hnot e
      obtain ⟨hS, hz⟩ := hoff x hx hnot
      obtain ⟨hp, hch, _⟩ := hx
      have hpc := pinv_next ring C s hg x e hp
      rcases th_step ring C s hg x.1 hp.1.1 x.2 e hp.2 hp.1.2.2 hS hz with h1 | ⟨_, h3, _⟩
      · left
        exact Or.inr ⟨hpc.1, _, hpc.2, Nat.lt_of_lt_of_le h1 hch⟩
      · right
        show Th s (topFixedTraceNext ring C x.1 e) + 1 ≤ Th s x.1 + 1
        omega)
    (by
      intro x hx hnot
      obtain ⟨hS, hz⟩ := hoff x hx hnot
      obtain ⟨hp, hch, _⟩ := hx
      have hex := th_strict ring C s hg x.1 hp.1.1 x.2 hp.2 hp.1.2.2 hS hz
      have hsel : thEdge ring C s x = Classical.choose hex := by
        unfold thEdge
        rw [dif_pos hex]
      have hspec := Classical.choose_spec hex
      have hpc := pinv_next ring C s hg x (Classical.choose hex) hp
      rw [hsel]
      rcases hspec with h1 | ⟨_, h3⟩
      · left
        exact Or.inr ⟨hpc.1, _, hpc.2, Nat.lt_of_lt_of_le h1 hch⟩
      · right
        show Th s (topFixedTraceNext ring C x.1 (Classical.choose hex)) + 1 + 1 ≤ Th s x.1 + 1
        omega)
    (Z, d) ⟨h, hA, Or.inr hM⟩ T
  have hlift := costNumerator_lift (topFixedTraceNext ring C) (WorkTarget ring C s a) (prodNext ring C s)
    P' Prod.fst (fun x e => rfl) (fun x => Iff.rfl) (Z, d) T
  rw [← hlift]
  refine Nat.le_trans hcost ?_
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul_left
  have := Th_tight ring C s hg Z
  show Th s Z + 1 ≤ _
  omega

end MarkedCells
end L3

#print axioms L3.MarkedCells.stage_work

import Leader.L3.Top.SettledPotentialSrc

/-!
# Q7 (P.8--P.10): the supply potential along one real edge

Consumer: `Leader/L3/Top/SettledPotentialPhase.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The pattern relation from agreement below `r`.

Consumer: `goodNext_congr`. -/
theorem samePat_of_eq (r : Nat) (c1 c2 : Nat → Cell) (h : ∀ k, k < r → c1 k = c2 k) :
    SamePat r c1 c2 := by
  intro k hk
  rw [h k hk]
  exact ⟨rfl, Iff.rfl, rfl⟩

/-- The consuming-carry predicate only reads the first `r` registers.

Consumer: `goodNext_congr`. -/
theorem consAt_congr (r : Nat) (c1 c2 : Nat → Cell) (h : ∀ k, k < r → c1 k = c2 k) :
    ConsAt r c1 ↔ ConsAt r c2 := by
  have hH := hpOf_congr r c1 c2 (samePat_of_eq r c1 c2 h)
  unfold ConsAt
  rw [hH]
  by_cases hq : hpOf r c2 + 1 < r
  · rw [h _ hq]
  · simp [hq]

/-- A step that does not raise the measure and keeps a consuming carry consuming.

Consumer: `th_step`. -/
def GoodNext (r : Nat) (c c' : Nat → Cell) : Prop :=
  Gv r c' ≤ Gv r c ∧ (ConsAt r c → ConsAt r c')

/-- Good steps are invariant under agreement below `r`.

Consumer: `th_step`. -/
theorem goodNext_congr (r : Nat) (c c1 c2 : Nat → Cell) (h : ∀ k, k < r → c1 k = c2 k)
    (g : GoodNext r c c1) : GoodNext r c c2 := by
  refine ⟨?_, fun hc => (consAt_congr r c1 c2 h).1 (g.2 hc)⟩
  rw [← Gv_congr r c1 c2 (samePat_of_eq r c1 c2 h)]
  exact g.1

/-- The supply potential along a good step that does not raise the source distance.

Consumer: `th_step`. -/
theorem th_le_good (r : Nat) (c c' : Nat → Cell) (d d' : Nat) (g : GoodNext r c c') (hd : d' ≤ d) :
    Gv r c' + (if ConsAt r c' then 0 else d') ≤ Gv r c + (if ConsAt r c then 0 else d) := by
  by_cases hc : ConsAt r c
  · have := g.2 hc
    rw [if_pos this, if_pos hc]
    have := g.1
    omega
  · rw [if_neg hc]
    have := g.1
    split <;> omega

/-- The supply potential drops strictly along a good step when the measure drops, or when the
source distance drops while nothing is consumed.

Consumer: `th_step`. -/
theorem th_lt_good (r : Nat) (c c' : Nat → Cell) (d d' : Nat) (g : GoodNext r c c') (hd : d' ≤ d)
    (hcond : Gv r c' < Gv r c ∨ (¬ ConsAt r c ∧ d' < d)) :
    Gv r c' + (if ConsAt r c' then 0 else d') < Gv r c + (if ConsAt r c then 0 else d) := by
  by_cases hc : ConsAt r c
  · have := g.2 hc
    rw [if_pos this, if_pos hc]
    rcases hcond with h1 | ⟨h1, _⟩
    · omega
    · exact absurd hc h1
  · rw [if_neg hc]
    have := g.1
    rcases hcond with h1 | ⟨_, h1⟩ <;> split <;> omega

/-- The frame, the cleanup and every acceptance are good steps of a front-free window.

Consumer: `th_step`. -/
theorem good_port (r : Nat) (cells : Nat → Cell) (h : FEnv r cells) (hr : 1 < r) (t : Bool) :
    GoodNext r cells cells ∧ GoodNext r cells (setOne cells 0 (portClean (cells 0))) ∧
    GoodNext r cells (setOne cells 0 (portAccept t (cells 0))) := by
  refine ⟨⟨Nat.le_refl _, fun hh => hh⟩, ?_, ?_⟩
  · rw [clean_id r cells h (by omega)]
    exact ⟨Nat.le_refl _, fun hh => hh⟩
  · by_cases hx : cells 0 = { i := .e, c := .off }
    · have hp : (if t = true then Inp.pt else Inp.pn).isP = true := by cases t <;> rfl
      have e1 : portAccept t (cells 0) = { i := (if t = true then Inp.pt else Inp.pn), c := .off } := by
        unfold portAccept; rw [if_pos hx]
      rw [e1]
      have hg := gv_accept r cells h hr _ hp hx
      refine ⟨?_, fun hh => hg.1.2 hh⟩
      by_cases hc : ConsAt r cells
      · rw [hg.2.1 hc]; exact Nat.le_refl _
      · have := hg.2.2 hc; omega
    · rw [accept_id cells t hx]
      exact ⟨Nat.le_refl _, fun hh => hh⟩

end MarkedCells
end L3

#print axioms L3.MarkedCells.good_port

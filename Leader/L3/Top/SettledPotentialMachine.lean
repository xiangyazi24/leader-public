import Leader.L3.Top.SettledPotentialPort
import Leader.L3.Top.SettledPotentialCost
import Leader.L3.Top.SettledWorkSource

/-!
# Q7 (P.8--P.10): the invariants of a front-free reached state

At a reached state of a coloured run with a settled input, no front and no doomed input, the
cells of the target window satisfy the invariants of the pure measure `Gv`, and the active charge
is the charge of the settled sites.

Consumer: `Leader/L3/Top/SettledPotentialStep.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- No front and no doomed register when the front debt is zero.

Consumer: `fenv_machine`. -/
theorem mn_zero_facts (r : Nat) (cells : Nat → Cell) (d : Nat → Prop) (h : Mn r cells d = 0) :
    (∀ k, k < r → (cells k).i ≠ .x) ∧ (∀ k, k < r → ¬ d k) := by
  unfold Mn Xn Dn at h
  constructor
  · intro k hk hx
    have := cnt_pos (fun k => decide ((cells k).i = .x)) k (by simpa using hx) r hk
    omega
  · intro k hk hd
    have := cnt_pos (fun k => decide (d k)) k (by simpa using hd) r hk
    omega

/-- **The pure invariants of a front-free reached state.**

Consumer: `Leader/L3/Top/SettledPotentialStep.lean`. -/
theorem fenv_machine {n : Nat} (s : Fin n) (Z : TopFixedTraceState n)
    (d : Nat → Prop) (hc : ColourInv s Z d) (hbar : Barrier (topClockSpan n) (cellOf s Z))
    (hex : SettledAt s Z) (hM : Mn (topClockSpan n) (cellOf s Z) d = 0) :
    FEnv (topClockSpan n) (cellOf s Z) :=
  { inv := hc.1
    ni := hc.2.1
    bar := hbar
    ex := hex
    nx := (mn_zero_facts _ _ _ hM).1 }

/-- Without doomed registers the active charge is the charge of the settled sites.

Consumer: `Leader/L3/Top/SettledPotentialStep.lean`. -/
theorem charge_eq_At (r : Nat) (cells : Nat → Cell) (d : Nat → Prop) (hd : ∀ k, k < r → ¬ d k) :
    charge r (act r cells d) = At r cells := by
  unfold At
  congr 1
  funext k
  unfold act
  by_cases hk : k < r
  · simp [hd k hk]
  · simp [hk]

/-- **The potential of the supply phase.**  The measure `Gv` of the window, plus the source
distance unless a live carry is consuming.

Consumer: `Leader/L3/Top/SettledPotentialStep.lean`. -/
noncomputable def Th {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) : Nat :=
  Gv (topClockSpan n) (cellOf s Z) +
    (if ConsAt (topClockSpan n) (cellOf s Z) then 0
     else dist (topClockSpan n) (srcOf s Z))

/-- The supply potential is bounded.

Consumer: `Leader/L3/TopSettledPotentialStage.lean`. -/
theorem Th_le {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Z : TopFixedTraceState n) :
    Th s Z ≤ topClockSpan n * (2 * topClockSpan n + 2) + (topClockSpan n + 1) + 1 +
      topClockSpan n + (topClockSpan n + 1) := by
  have h1 := Gv_le (topClockSpan n) (cellOf s Z) (by have := span_ge_three hg.hn; omega)
  have h2 := dist_le (topClockSpan n) (srcOf s Z)
  unfold Th
  split <;> omega

end MarkedCells
end L3

#print axioms L3.MarkedCells.fenv_machine
#print axioms L3.MarkedCells.Th_le

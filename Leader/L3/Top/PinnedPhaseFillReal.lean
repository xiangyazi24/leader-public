import Leader.L3.Top.PinnedPhaseFillBridge

/-!
# Q7 (P.12 preparation, lemma 3, concrete layer): the letters realise the abstract steps

`Realized` says that the successor window cells, source tokens and residue are the ones the
abstract step `FillStep` computes.

Consumer: `Leader/L3/Top/PinnedPhaseFillCost.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The successor of a letter is described by the abstract data.

Consumer: `real_edge`, `real_term`, `real_src`, `real_frame`, `real_port_clean`,
`real_port_accept`. -/
def Realized {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (τ : Nat) (Z : TopFixedTraceState n) (e : Fin n) (c' : Nat → Cell) (src' : Nat → Tok)
    (a' : Nat) : Prop :=
  (∀ j, j < topClockSpan n → cellOf s (topFixedTraceNext ring C Z e) j = c' j) ∧
  (∀ i, i < topClockSpan n → srcOf s (topFixedTraceNext ring C Z e) i = src' i) ∧
  aOf s (topFixedTraceNext ring C Z e) τ = a'

/-- **The edge of a non-terminal window register.**

Consumer: `fill_concrete_step`. -/
theorem real_edge {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Z : TopFixedTraceState n) (hreach : topClockReached ring C Z)
    (τ : Nat) (hs : FillShape (topClockSpan n) (cellOf s Z)) (p : Nat)
    (hp : p + 1 < topClockSpan n) :
    Realized ring C s τ Z (winSite s p)
      (setTwo (cellOf s Z) p
        (pair (decide (p = 0)) false (cellOf s Z p) (cellOf s Z (p + 1))).1
        (pair (decide (p = 0)) false (cellOf s Z p) (cellOf s Z (p + 1))).2)
      (srcOf s Z) (aOf s Z τ) := by
  have hr3 := span_ge_three hg.hn
  have hcells : ∀ j, j < topClockSpan n →
      cellOf s (topFixedTraceNext ring C Z (winSite s p)) j =
        setTwo (cellOf s Z) p
          (pair (decide (p = 0)) false (cellOf s Z p) (cellOf s Z (p + 1))).1
          (pair (decide (p = 0)) false (cellOf s Z p) (cellOf s Z (p + 1))).2 j := by
    intro j hj
    rw [link_window ring C s Z hg hreach p (by omega) j hj]
    unfold edgeStep
    rw [if_pos hp]
  refine ⟨hcells, ?_, ?_⟩
  · intro i hi
    apply src_link_away ring C s Z hg hreach
    · intro j hj h
      exact win_ne_src hg.hn C s hg.hbad p j (by omega) hj h
    · exact hi
  · unfold aOf
    rw [paQ_away ring C s Z _ τ (win_ne_port hg.hn s p (by omega)),
      fcnt_congr _ _ _ hcells, fcnt_edge _ p hp _ hs]

/-- **The terminal edge of the window.**

Consumer: `fill_concrete_step`. -/
theorem real_term {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Z : TopFixedTraceState n) (hreach : topClockReached ring C Z)
    (τ : Nat) (hs : FillShape (topClockSpan n) (cellOf s Z))
    (hle : fcnt (topClockSpan n) (cellOf s Z) ≤ (paQ s Z τ).length) :
    Realized ring C s τ Z (winSite s (topClockSpan n - 1))
      (setOne (cellOf s Z) (topClockSpan n - 1)
        (pair false true (cellOf s Z (topClockSpan n - 1)) { i := .e, c := .off }).1)
      (srcOf s Z)
      (if (cellOf s Z (topClockSpan n - 1)).i = .pt then (aOf s Z τ + 1) % topClockSpan n
        else aOf s Z τ) := by
  have hr3 := span_ge_three hg.hn
  have hcells : ∀ j, j < topClockSpan n →
      cellOf s (topFixedTraceNext ring C Z (winSite s (topClockSpan n - 1))) j =
        setOne (cellOf s Z) (topClockSpan n - 1)
          (pair false true (cellOf s Z (topClockSpan n - 1)) { i := .e, c := .off }).1 j := by
    intro j hj
    rw [link_window ring C s Z hg hreach (topClockSpan n - 1) (by omega) j hj]
    unfold edgeStep
    rw [if_neg (by omega)]
  refine ⟨hcells, ?_, ?_⟩
  · intro i hi
    apply src_link_away ring C s Z hg hreach
    · intro j hj h
      exact win_ne_src hg.hn C s hg.hbad (topClockSpan n - 1) j (by omega) hj h
    · exact hi
  · have hQ := paQ_away ring C s Z (winSite s (topClockSpan n - 1)) τ
      (win_ne_port hg.hn s (topClockSpan n - 1) (by omega))
    have hfc := fcnt_congr _ _ _ hcells
    rcases fcnt_term _ (by omega) _ hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_neg h2]
      unfold aOf
      rw [hQ, hfc, h1]
    · rw [if_pos h2]
      unfold aOf
      rw [hQ, hfc]
      have hx : (paQ s Z τ).length - (fcnt (topClockSpan n) (cellOf s Z) - 1) =
          ((paQ s Z τ).length - fcnt (topClockSpan n) (cellOf s Z)) + 1 := by omega
      have h3 : fcnt (topClockSpan n)
          (setOne (cellOf s Z) (topClockSpan n - 1)
            (pair false true (cellOf s Z (topClockSpan n - 1)) { i := .e, c := .off }).1) =
          fcnt (topClockSpan n) (cellOf s Z) - 1 := by omega
      rw [h3, hx, Nat.mod_add_mod]

/-- **The edge of a source site other than the port.**

Consumer: `fill_concrete_step`. -/
theorem real_src {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Z : TopFixedTraceState n) (hreach : topClockReached ring C Z)
    (τ : Nat) (j : Nat) (hj : j + 1 < topClockSpan n) :
    Realized ring C s τ Z (certSite s j) (cellOf s Z)
      (srcStepAt (topClockSpan n) (accOf s Z) (srcOf s Z) j) (aOf s Z τ) := by
  have hr3 := span_ge_three hg.hn
  have hrn := span_lt_n hg.hn
  have hb : certSite s j ≠ certSite s (topClockSpan n - 1) := src_ne_port s j hj hrn
  have hcells := cells_frame ring C s Z hg (certSite s j)
    (fun p hp h => win_ne_src hg.hn C s hg.hbad p j hp (by omega) h.symm) hb
  refine ⟨hcells, src_link_edge ring C s Z hg hreach j (by omega), ?_⟩
  unfold aOf
  rw [paQ_away ring C s Z _ τ hb, fcnt_congr _ _ _ hcells]

/-- **A letter outside the window and the source block.**

Consumer: `fill_concrete_step`. -/
theorem real_frame {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Z : TopFixedTraceState n) (hreach : topClockReached ring C Z)
    (τ : Nat) (e : Fin n) (ha : ∀ p, p < topClockSpan n → e ≠ winSite s p)
    (hsrc : ∀ j, j < topClockSpan n → e ≠ certSite s j) :
    Realized ring C s τ Z e (cellOf s Z) (srcOf s Z) (aOf s Z τ) := by
  have hr3 := span_ge_three hg.hn
  have hb : e ≠ certSite s (topClockSpan n - 1) := hsrc _ (by omega)
  have hcells := cells_frame ring C s Z hg e ha hb
  refine ⟨hcells, fun i hi => src_link_away ring C s Z hg hreach e hsrc i hi, ?_⟩
  unfold aOf
  rw [paQ_away ring C s Z _ τ hb, fcnt_congr _ _ _ hcells]

end MarkedCells
end L3

#print axioms L3.MarkedCells.real_edge
#print axioms L3.MarkedCells.real_term
#print axioms L3.MarkedCells.real_src
#print axioms L3.MarkedCells.real_frame

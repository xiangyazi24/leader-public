import Leader.L3.Top.PinnedPhaseFillLink

/-!
# Q7 (P.12 preparation, lemma 3, concrete layer): every letter is a step of the fill regime

For a reached state whose window has the fill shape, the successor window, the successor source
tokens and the successor residue `aOf` are those of the abstract step `FillStep`:

* the edge of window register `p` (`real_edge`), the terminal edge (`real_term`);
* the edge of a source site other than the port (`real_src`);
* the port edge: it accepts exactly when a sampled token stands at the terminal and the border
  register accepts (`real_port_clean`, `real_port_accept`);
* every other edge leaves everything alone (`real_frame`).

Consumer: `Leader/L3/Top/PinnedPhaseFillCost.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The source block and the window do not overlap on the ring.

Consumer: `win_ne_src`. -/
theorem two_span_le_n {n : Nat} (hn : 5 ≤ n) (C : HeadlineConfiguration n) (s : Fin n)
    (hbad : HeadlineDigit.BadCompletePair C s) : 2 * topClockSpan n ≤ n := by
  apply Classical.byContradiction
  intro h
  have hrn := span_lt_n hn
  obtain ⟨d, hd⟩ : ∃ d, topClockSpan n + topClockSpan n = n + d := ⟨2 * topClockSpan n - n, by omega⟩
  have h1 := geom_terminal C s hbad
  have e1 : certSite s (topClockSpan n + topClockSpan n) = certSite s d := by
    rw [hd, ← certSite_add, certSite_n]
  have h2 := src_beta C s hbad d (by omega)
  rw [e1, h2] at h1
  simp at h1
  omega

/-- A window site is not a source site.

Consumer: `real_edge`, `real_src`, `real_frame`. -/
theorem win_ne_src {n : Nat} (hn : 5 ≤ n) (C : HeadlineConfiguration n) (s : Fin n)
    (hbad : HeadlineDigit.BadCompletePair C s) (p j : Nat) (hp : p < topClockSpan n)
    (hj : j < topClockSpan n) : winSite s p ≠ certSite s j := by
  intro h
  have h2 := two_span_le_n hn C s hbad
  unfold winSite at h
  have := certSite_inj_close s j (topClockSpan n + p) (by omega) (by omega) h.symm
  omega

/-- A source site is not the port site unless it is the last one.

Consumer: `real_src`. -/
theorem src_ne_port {n : Nat} (s : Fin n) (j : Nat) (hj : j + 1 < topClockSpan n)
    (hrn : topClockSpan n < n) : certSite s j ≠ certSite s (topClockSpan n - 1) := by
  intro h
  have := certSite_inj_close s j (topClockSpan n - 1) (by omega) (by omega) h
  omega

/-- The flag count only reads the first `r` registers.

Consumer: `real_edge`, `real_term`. -/
theorem fcnt_congr (r : Nat) (c c' : Nat → Cell) (h : ∀ j, j < r → c j = c' j) :
    fcnt r c = fcnt r c' := by
  unfold fcnt
  apply wsum_congr
  intro k hk
  simp [fl, h k hk]

/-- The accepted queue does not change off the port edge.

Consumer: `real_edge`, `real_term`, `real_src`, `real_frame`. -/
theorem paQ_away {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n) (τ : Nat) (hb : e ≠ certSite s (topClockSpan n - 1)) :
    paQ s (topFixedTraceNext ring C Z e) τ = paQ s Z τ := by
  unfold paQ
  rw [exportsAfter_step_away ring C s Z e τ hb]

/-- The flag count after a window edge.

Consumer: `real_edge`. -/
theorem fcnt_edge (r p : Nat) (hp : p + 1 < r) (c : Nat → Cell) (hs : FillShape r c) :
    fcnt r (setTwo c p (pair (decide (p = 0)) false (c p) (c (p + 1))).1
      (pair (decide (p = 0)) false (c p) (c (p + 1))).2) = fcnt r c := by
  rcases fill_edge_cases r p hp c hs with h | ⟨hP, hy, he⟩ | ⟨hP, hy, he⟩
  · rw [h]
  · rw [he]; exact (move_counts r p hp c hP hy).1
  · rw [he]
    by_cases hpt : (c p).i = .pt
    · have hi : (if (c p).i = Inp.pt then Inp.st else Inp.sn) = Inp.st := if_pos hpt
      rw [hi]
      exact (settle_counts r p (by omega) c hP { i := .st, c := .off } rfl rfl).1
    · have hi : (if (c p).i = Inp.pt then Inp.st else Inp.sn) = Inp.sn := if_neg hpt
      rw [hi]
      exact (settle_counts r p (by omega) c hP { i := .sn, c := .off } rfl rfl).1

/-- The flag count after the terminal edge.

Consumer: `real_term`. -/
theorem fcnt_term (r : Nat) (hr : 2 ≤ r) (c : Nat → Cell) (hs : FillShape r c) :
    (fcnt r (setOne c (r - 1) (pair false true (c (r - 1)) { i := .e, c := .off }).1) = fcnt r c ∧
      (c (r - 1)).i ≠ .pt) ∨
    (fcnt r (setOne c (r - 1) (pair false true (c (r - 1)) { i := .e, c := .off }).1) + 1 = fcnt r c ∧
      (c (r - 1)).i = .pt) := by
  rcases fill_term_cases r (by omega) c hs with ⟨hk, he⟩ | ⟨hpn, he⟩ | ⟨hpt, he⟩
  · left
    rw [he]
    refine ⟨rfl, ?_⟩
    rcases hk with h | h <;> rw [h] <;> decide
  · left
    rw [he]
    have hP : (c (r - 1)).i.isP = true := by simp [hpn, Inp.isP]
    exact ⟨(settle_counts r (r - 1) (by omega) c hP { i := .sn, c := .off } rfl rfl).1,
      by rw [hpn]; decide⟩
  · right
    rw [he]
    have hP : (c (r - 1)).i.isP = true := by simp [hpt, Inp.isP]
    exact ⟨(delete_counts r (by omega) c hP).1, hpt⟩

/-- A letter that touches neither the window nor the source leaves the window cells alone.

Consumer: `real_src`, `real_frame`. -/
theorem cells_frame {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (hg : WinGeo ring C s) (e : Fin n)
    (ha : ∀ p, p < topClockSpan n → e ≠ winSite s p)
    (hb : e ≠ certSite s (topClockSpan n - 1)) :
    ∀ j, j < topClockSpan n → cellOf s (topFixedTraceNext ring C Z e) j = cellOf s Z j := by
  intro j hj
  unfold cellOf
  have hr3 := span_ge_three hg.hn
  apply siteCell_away
  · intro h; exact ha j hj h.symm
  · intro h
    by_cases hj0 : j = 0
    · subst hj0
      apply hb
      apply certSite_pred ring s e (topClockSpan n - 1)
      rw [← h]
      unfold winSite
      congr 1
      omega
    · apply ha (j - 1) (by omega)
      apply certSite_pred ring s e (topClockSpan n + (j - 1))
      rw [← h]
      unfold winSite
      congr 1
      omega

end MarkedCells
end L3

#print axioms L3.MarkedCells.two_span_le_n
#print axioms L3.MarkedCells.win_ne_src
#print axioms L3.MarkedCells.cells_frame

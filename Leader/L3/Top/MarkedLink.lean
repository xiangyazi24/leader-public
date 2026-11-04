import Leader.L3.Top.MarkedGeom
import Leader.L3.Top.MarkedSelect
import Leader.L3.Top.MarkedInv

/-!
# Q7: the fixed trace acts on the window cells as the abstract steps

`cellOf s Z j` is the abstract class of target register `j`.  Every edge of
`topFixedTraceNext` sends the window cells to an abstract successor (`link_step`),
and the edge of register `p` sends them to `edgeStep` exactly (`link_window`).

Consumer: `Leader/L3/Top/MarkedDebtRows.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- The site of target register `j`.

Consumer: `link_step`. -/
def winSite {n : Nat} (s : Fin n) (j : Nat) : Fin n := certSite s (topClockSpan n + j)

/-- The abstract cell of target register `j`.

Consumer: `link_step`. -/
def cellOf {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (j : Nat) : Cell :=
  siteCell Z (winSite s j)

/-- The terminal source output does not read the responder.

Consumer: `link_step`. -/
theorem pair_term_indep (b : Bool) (x y y' : Cell) :
    (pair b true x y).1 = (pair b true x y').1 := by
  rcases x with ⟨xi, xk⟩
  cases xi <;> cases xk <;> cases b <;>
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS]

/-- The window geometry at one eligible entrance.

Consumer: `topClockMarkedDebtPhase_holds`. -/
structure WinGeo {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) : Prop where
  hn : 5 ≤ n
  hl : ∀ i, (C i).l = false
  hbad : HeadlineDigit.BadCompletePair C s

/-- The right neighbour of a window site.

Consumer: `link_step`. -/
theorem winSite_next {n : Nat} (ring : DirectedRing n) (s : Fin n) (p : Nat) :
    ring.rightNeighbor (winSite s p) = winSite s (p + 1) := by
  unfold winSite
  rw [rn_certSite]
  rfl

/-- Window sites are distinct.

Consumer: `link_step`. -/
theorem winSite_inj {n : Nat} (hn : 5 ≤ n) (s : Fin n) (a b : Nat)
    (ha : a ≤ topClockSpan n) (hb : b ≤ topClockSpan n)
    (h : winSite s a = winSite s b) : a = b := by
  have hr := span_lt_n hn
  unfold winSite at h
  rcases Nat.le_total a b with hab | hab
  · have := certSite_inj_close s (topClockSpan n + a) (topClockSpan n + b) (by omega)
      (by omega) h
    omega
  · have := certSite_inj_close s (topClockSpan n + b) (topClockSpan n + a) (by omega)
      (by omega) h.symm
    omega

/-- Only the first register is a marker.

Consumer: `link_step`. -/
theorem winSite_beta {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hbad : HeadlineDigit.BadCompletePair C s) (j : Nat)
    (hj : j < topClockSpan n) :
    (C (winSite s j)).beta = decide (j = 0) := by
  unfold winSite
  by_cases h0 : j = 0
  · subst h0
    simpa using geom_border C s hbad
  · rw [geom_interior C s hbad j (by omega) hj]
    simp [h0]

/-- The site after the window is a marker.

Consumer: `link_step`. -/
theorem winSite_term_beta {n : Nat} (C : HeadlineConfiguration n)
    (s : Fin n) (hbad : HeadlineDigit.BadCompletePair C s) :
    (C (winSite s (topClockSpan n))).beta = true := by
  unfold winSite
  exact geom_terminal C s hbad

/-- The edge of register `p` acts on the window as `edgeStep`.

Consumer: `link_step`. -/
theorem link_window {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (hg : WinGeo ring C s)
    (hreach : topClockReached ring C Z) (p : Nat) (hp : p < topClockSpan n) :
    ∀ j, j < topClockSpan n →
      cellOf s (topFixedTraceNext ring C Z (winSite s p)) j =
        edgeStep (topClockSpan n) (cellOf s Z) p j := by
  intro j hj
  have hfrz := publicFrozen_reached ring C Z hreach
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hxl : (Z.1.1 (winSite s p)).l = false := by
    rw [(hfrz _).1]; exact hg.hl _
  have hyl : (Z.1.1 (ring.rightNeighbor (winSite s p))).l = false := by
    rw [(hfrz _).1]; exact hg.hl _
  have hbx : (Z.1.1 (winSite s p)).beta = decide (p = 0) := by
    rw [(hfrz _).2]; exact winSite_beta ring C s hg.hbad p hp
  have hsrc := siteCell_source ring C Z (winSite s p) hxl hyl
  rw [hbx] at hsrc
  have hr3 := span_ge_three hg.hn
  unfold edgeStep cellOf
  by_cases hp1 : p + 1 < topClockSpan n
  · rw [if_pos hp1]
    have hyb : (Z.1.1 (ring.rightNeighbor (winSite s p))).beta = false := by
      rw [winSite_next, (hfrz _).2, winSite_beta ring C s hg.hbad (p + 1) hp1]
      simp
    have hresp := siteCell_responder_interior ring hn2 C Z (winSite s p) hxl hyl hyb
    rw [hbx] at hresp
    rw [hyb] at hsrc
    rw [winSite_next] at hsrc hresp
    by_cases hjp : j = p
    · subst hjp
      simp only [setTwo, if_true]
      exact hsrc
    · by_cases hjp1 : j = p + 1
      · subst hjp1
        simp only [setTwo, if_neg hjp, if_true]
        exact hresp
      · simp only [setTwo, if_neg hjp, if_neg hjp1]
        apply siteCell_away
        · intro h; exact hjp (winSite_inj hg.hn s j p (by omega) (by omega) h)
        · rw [winSite_next]
          intro h; exact hjp1 (winSite_inj hg.hn s j (p + 1) (by omega) (by omega) h)
  · rw [if_neg hp1]
    have hpr : p + 1 = topClockSpan n := by omega
    have hybeta : (Z.1.1 (ring.rightNeighbor (winSite s p))).beta = true := by
      rw [winSite_next, (hfrz _).2, hpr]
      exact winSite_term_beta C s hg.hbad
    have hyl' : (Z.1.1 (ring.rightNeighbor (winSite s p))).l = false := hyl
    rw [hybeta] at hsrc
    have hp0 : decide (p = 0) = false := by
      have : p ≠ 0 := by omega
      simp [this]
    rw [hp0] at hsrc
    have hpe : topClockSpan n - 1 = p := by omega
    by_cases hjp : j = p
    · subst hjp
      rw [hpe]
      simp only [setOne, if_true]
      rw [hsrc]
      exact pair_term_indep false _ _ _
    · have hjp' : j ≠ topClockSpan n - 1 := by omega
      simp only [setOne, if_neg hjp']
      apply siteCell_away
      · intro h; exact hjp (winSite_inj hg.hn s j p (by omega) (by omega) h)
      · rw [winSite_next, hpr]
        intro h; have := winSite_inj hg.hn s j (topClockSpan n) (by omega) (by omega) h
        omega

/-- Every edge acts on the window cells as an abstract step.

Consumer: `topClockMarkedDebtPhase_holds`. -/
theorem link_step {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (hg : WinGeo ring C s)
    (hreach : topClockReached ring C Z) (e : Fin n) :
    ∃ cells', Step (topClockSpan n) (cellOf s Z) cells' ∧
      ∀ j, j < topClockSpan n → cellOf s (topFixedTraceNext ring C Z e) j = cells' j := by
  have hfrz := publicFrozen_reached ring C Z hreach
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hr3 := span_ge_three hg.hn
  have hrn := span_lt_n hg.hn
  by_cases ha : ∃ p, p < topClockSpan n ∧ e = winSite s p
  · obtain ⟨p, hp, rfl⟩ := ha
    exact ⟨edgeStep (topClockSpan n) (cellOf s Z) p,
      edgeStep_step _ _ p hp, link_window ring C s Z hg hreach p hp⟩
  · by_cases hb : e = certSite s (topClockSpan n - 1)
    · -- the port edge
      have hy : ring.rightNeighbor e = winSite s 0 := by
        rw [hb, rn_certSite]
        unfold winSite
        congr 1
        omega
      have hxl : (Z.1.1 e).l = false := by rw [(hfrz _).1]; exact hg.hl _
      have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
        rw [(hfrz _).1]; exact hg.hl _
      have hyb : (Z.1.1 (ring.rightNeighbor e)).beta = true := by
        rw [hy, (hfrz _).2, winSite_beta ring C s hg.hbad 0 (by omega)]
        simp
      have hresp := siteCell_responder_terminal ring hn2 C Z e hxl hyl hyb
      rw [hy] at hresp
      have haway : ∀ j, 0 < j → j < topClockSpan n →
          cellOf s (topFixedTraceNext ring C Z e) j = cellOf s Z j := by
        intro j hj0 hj
        unfold cellOf
        apply siteCell_away
        · intro h
          rw [hb] at h
          unfold winSite at h
          have := certSite_inj_close s (topClockSpan n - 1) (topClockSpan n + j) (by omega)
            (by omega) h.symm
          omega
        · rw [hy]
          intro h
          have := winSite_inj hg.hn s j 0 (by omega) (by omega) h
          omega
      rcases hresp with hc | ⟨t, hc⟩
      · refine ⟨setOne (cellOf s Z) 0 (portClean (cellOf s Z 0)), Step.clean, ?_⟩
        intro j hj
        by_cases hj0 : j = 0
        · subst hj0
          simp only [setOne, if_true]
          exact hc
        · simp only [setOne, if_neg hj0]
          exact haway j (by omega) hj
      · refine ⟨setOne (cellOf s Z) 0 (portAccept t (cellOf s Z 0)), Step.accept t, ?_⟩
        intro j hj
        by_cases hj0 : j = 0
        · subst hj0
          simp only [setOne, if_true]
          exact hc
        · simp only [setOne, if_neg hj0]
          exact haway j (by omega) hj
    · refine ⟨cellOf s Z, Step.frame, ?_⟩
      intro j hj
      unfold cellOf
      apply siteCell_away
      · intro h; exact ha ⟨j, hj, h.symm⟩
      · intro h
        by_cases hj0 : j = 0
        · subst hj0
          apply hb
          apply certSite_pred ring s e (topClockSpan n - 1)
          rw [← h]
          unfold winSite
          congr 1
          omega
        · apply ha
          refine ⟨j - 1, by omega, ?_⟩
          apply certSite_pred ring s e (topClockSpan n + (j - 1))
          rw [← h]
          unfold winSite
          congr 1
          omega

end MarkedCells
end L3

#print axioms L3.MarkedCells.link_window
#print axioms L3.MarkedCells.link_step

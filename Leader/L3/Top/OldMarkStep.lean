import Leader.L3.Top.OldFlagsStep
import Leader.L3.Top.SettledCover
import Leader.L3.Top.OldMarkSelect

/-!
# Q7: the old-pending flags after one edge are below the abstract flags

For every edge `e` of the fixed trace, the flags of the next state are below the flags
predicted by the abstract step: `flagsAt` for a window edge, `flagsPort` for the port edge,
and the old flags themselves for every other edge.

Consumer: `Leader/L3/Top/RepairedMarked.lean`.
-/

namespace L3
namespace MarkedCells

open Classical

set_option autoImplicit false

/-- Flags after a window edge.

Consumer: `rank_old_row`. -/
theorem old_next_window {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) (p : Nat) (hp : p < topClockSpan n) :
    ∀ j, j < topClockSpan n →
      oldFlag s τ (topFixedTraceNext ring C Z (winSite s p)) j = true →
      flagsAt (topClockSpan n) (cellOf s Z) (oldFlag s τ Z) p j = true := by
  intro j hj hold
  have hfrz := publicFrozen_reached ring C Z hreach
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hr3 := span_ge_three hg.hn
  have hxl : (Z.1.1 (winSite s p)).l = false := by rw [(hfrz _).1]; exact hg.hl _
  have hyl : (Z.1.1 (ring.rightNeighbor (winSite s p))).l = false := by
    rw [(hfrz _).1]; exact hg.hl _
  have hag := link_window ring C s Z hg hreach p hp
  obtain ⟨hjr, hsite⟩ := (oldFlag_iff s τ _ j).1 hold
  have hdist : ∀ q, q < topClockSpan n → q ≠ p → q ≠ p + 1 →
      winSite s q ≠ winSite s p ∧ winSite s q ≠ ring.rightNeighbor (winSite s p) := by
    intro q hq h1 h2
    refine ⟨fun h => h1 (winSite_inj hg.hn s q p (by omega) (by omega) h), ?_⟩
    rw [winSite_next]
    intro h
    exact h2 (winSite_inj hg.hn s q (p + 1) (by omega) (by omega) h)
  unfold flagsAt
  by_cases hp1 : p + 1 < topClockSpan n
  · rw [if_pos hp1]
    unfold flagsEdge
    have hyb : (Z.1.1 (ring.rightNeighbor (winSite s p))).beta = false := by
      rw [winSite_next, (hfrz _).2, winSite_beta ring C s hg.hbad (p + 1) hp1]
      simp
    have hcp : cellOf s (topFixedTraceNext ring C Z (winSite s p)) p =
        (pair (decide (p = 0)) false (cellOf s Z p) (cellOf s Z (p + 1))).1 := by
      rw [hag p hp]; simp [edgeStep, hp1, setTwo]
    have hcq : cellOf s (topFixedTraceNext ring C Z (winSite s p)) (p + 1) =
        (pair (decide (p = 0)) false (cellOf s Z p) (cellOf s Z (p + 1))).2 := by
      rw [hag (p + 1) hp1]; simp [edgeStep, hp1, setTwo]
    by_cases hjp : j = p
    · subst hjp
      simp only [if_true]
      have hs := old_source ring C s τ Z _ hxl hyl hsite
      have hoj : oldFlag s τ Z j = true := (oldFlag_iff s τ Z j).2 ⟨hp, hs⟩
      have hisP : (pair (decide (j = 0)) false (cellOf s Z j) (cellOf s Z (j + 1))).1.i.isP
          = true := by
        rw [← hcp]; unfold cellOf; rw [siteCell_isP]; exact hsite.1
      simp [oldX, hoj, hisP]
    · by_cases hjp1 : j = p + 1
      · subst hjp1
        simp only [if_neg hjp, if_true]
        have hsite' : oldSite s τ (topFixedTraceNext ring C Z (winSite s p))
            (ring.rightNeighbor (winSite s p)) := by rw [winSite_next]; exact hsite
        have hisPb : (pair (decide (p = 0)) false (cellOf s Z p) (cellOf s Z (p + 1))).2.i.isP
            = true := by
          rw [← hcq]; unfold cellOf; rw [siteCell_isP]; exact hsite.1
        rcases old_responder ring hn2 C s τ Z _ hxl hyl (Or.inl hyb) hsite' with
          ⟨h1, h2⟩ | ⟨_, h1, h2, h3⟩
        · rw [winSite_next] at h2 h1
          have hoy : oldFlag s τ Z (p + 1) = true := (oldFlag_iff s τ Z _).2 ⟨hp1, h2⟩
          have hy : (cellOf s Z (p + 1)).i.isP = true := by
            unfold cellOf; rw [siteCell_isP]; exact h1
          simp [oldY, hoy, hisPb, hy]
        · rw [winSite_next] at h1
          have hox : oldFlag s τ Z p = true := (oldFlag_iff s τ Z _).2 ⟨hp, h3⟩
          have hx : (cellOf s Z p).i.isP = true := by
            unfold cellOf; rw [siteCell_isP]; exact h2
          have hy : (cellOf s Z (p + 1)).i.isP = false := by
            unfold cellOf; rw [siteCell_isP]; exact h1
          simp [oldY, hox, hisPb, hx, hy]
      · simp only [if_neg hjp, if_neg hjp1]
        have hd := hdist j hj hjp hjp1
        have := old_away ring C s τ Z _ _ hd.1 hd.2 hsite
        exact (oldFlag_iff s τ Z j).2 ⟨hj, this⟩
  · rw [if_neg hp1]
    unfold flagsTerm
    have hpe : p = topClockSpan n - 1 := by omega
    have hcp : cellOf s (topFixedTraceNext ring C Z (winSite s p)) p =
        (pair false true (cellOf s Z p) { i := .e, c := .off }).1 := by
      rw [hag p hp]; unfold edgeStep; rw [if_neg hp1]; simp only [setOne, if_pos hpe]; rw [hpe]
    by_cases hjp : j = p
    · subst hjp
      have hs := old_source ring C s τ Z _ hxl hyl hsite
      have hoj : oldFlag s τ Z j = true := (oldFlag_iff s τ Z j).2 ⟨hp, hs⟩
      have hisP : (pair false true (cellOf s Z j) { i := .e, c := .off }).1.i.isP = true := by
        rw [← hcp]; unfold cellOf; rw [siteCell_isP]; exact hsite.1
      simp only [hpe, if_true] at *
      simp [oldX, hoj, hisP, hpe]
    · have hjp' : j ≠ topClockSpan n - 1 := by omega
      simp only [if_neg hjp']
      have h1 : winSite s j ≠ winSite s p := fun h =>
        hjp (winSite_inj hg.hn s j p (by omega) (by omega) h)
      have h2 : winSite s j ≠ ring.rightNeighbor (winSite s p) := by
        rw [winSite_next]
        intro h
        have := winSite_inj hg.hn s j (p + 1) (by omega) (by omega) h
        omega
      have := old_away ring C s τ Z _ _ h1 h2 hsite
      exact (oldFlag_iff s τ Z j).2 ⟨hj, this⟩

/-- Flags after the port edge.

Consumer: `rank_old_row`. -/
theorem old_next_port {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) (hτ : τ ≤ Z.1.2.clock) (e : Fin n)
    (hb : e = certSite s (topClockSpan n - 1)) (c' : Cell)
    (hc0 : cellOf s (topFixedTraceNext ring C Z e) 0 = c') :
    ∀ j, j < topClockSpan n →
      oldFlag s τ (topFixedTraceNext ring C Z e) j = true →
      flagsPort (cellOf s Z) (oldFlag s τ Z) c' j = true := by
  intro j hj hold
  have hfrz := publicFrozen_reached ring C Z hreach
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hr3 := span_ge_three hg.hn
  have hrn := span_lt_n hg.hn
  have hy : ring.rightNeighbor e = winSite s 0 := by
    rw [hb, rn_certSite]
    unfold winSite
    congr 1
    omega
  have hxl : (Z.1.1 e).l = false := by rw [(hfrz _).1]; exact hg.hl _
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by rw [(hfrz _).1]; exact hg.hl _
  obtain ⟨hjr, hsite⟩ := (oldFlag_iff s τ _ j).1 hold
  unfold flagsPort
  by_cases hj0 : j = 0
  · subst hj0
    simp only [if_true]
    have hsite' : oldSite s τ (topFixedTraceNext ring C Z e) (ring.rightNeighbor e) := by
      rw [hy]; exact hsite
    have hyb : (Z.1.1 (ring.rightNeighbor e)).beta = true := by
      rw [hy, (hfrz _).2, winSite_beta ring C s hg.hbad 0 (by omega)]
      simp
    have hy' : ring.rightNeighbor e = certSite s (topClockSpan n) := by
      rw [hy]; rfl
    rcases old_responder ring hn2 C s τ Z e hxl hyl (Or.inr ⟨hτ, hb, hy'⟩) hsite' with
      ⟨h1, h2⟩ | ⟨h1, _⟩
    · rw [hy] at h1 h2
      have hoj : oldFlag s τ Z 0 = true := (oldFlag_iff s τ Z 0).2 ⟨by omega, h2⟩
      have hisP : c'.i.isP = true := by
        rw [← hc0]; unfold cellOf; rw [siteCell_isP]; exact hsite.1
      simp [oldX, hoj, hisP]
    · exfalso
      rw [hyb] at h1
      exact absurd h1 (by decide)
  · simp only [if_neg hj0]
    have h1 : winSite s j ≠ e := by
      intro h
      rw [hb] at h
      unfold winSite at h
      have := certSite_inj_close s (topClockSpan n - 1) (topClockSpan n + j) (by omega)
        (by omega) h.symm
      omega
    have h2 : winSite s j ≠ ring.rightNeighbor e := by
      rw [hy]
      intro h
      have := winSite_inj hg.hn s j 0 (by omega) (by omega) h
      omega
    exact (oldFlag_iff s τ Z j).2 ⟨hj, old_away ring C s τ Z _ _ h1 h2 hsite⟩

/-- Flags after an edge outside the window and off the port.

Consumer: `rank_old_row`. -/
theorem old_next_frame {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) (Z : TopFixedTraceState n) (e : Fin n)
    (hnw : ¬ ∃ p, p < topClockSpan n ∧ e = winSite s p)
    (hb : e ≠ certSite s (topClockSpan n - 1)) :
    ∀ j, j < topClockSpan n →
      oldFlag s τ (topFixedTraceNext ring C Z e) j = true → oldFlag s τ Z j = true := by
  intro j hj hold
  have hr3 := span_ge_three hg.hn
  obtain ⟨hjr, hsite⟩ := (oldFlag_iff s τ _ j).1 hold
  have h1 : winSite s j ≠ e := fun h => hnw ⟨j, hj, h.symm⟩
  have h2 : winSite s j ≠ ring.rightNeighbor e := by
    intro h
    by_cases hj0 : j = 0
    · subst hj0
      apply hb
      apply certSite_pred ring s e (topClockSpan n - 1)
      rw [← h]
      unfold winSite
      congr 1
      omega
    · apply hnw
      refine ⟨j - 1, by omega, ?_⟩
      apply certSite_pred ring s e (topClockSpan n + (j - 1))
      rw [← h]
      unfold winSite
      congr 1
      omega
  exact (oldFlag_iff s τ Z j).2 ⟨hj, old_away ring C s τ Z _ _ h1 h2 hsite⟩

end MarkedCells
end L3

#print axioms L3.MarkedCells.old_next_window
#print axioms L3.MarkedCells.old_next_port
#print axioms L3.MarkedCells.old_next_frame

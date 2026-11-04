import Leader.L3.Top.OldMarkStep
import Leader.L3.Top.OldMarkZero
import Leader.L3.Top.StrongClasses

/-!
# Q7: P.4--P.5 for the repaired classes

The potential is the marked rank `rank r (markCells (cellOf s Y) (oldFlag s τ Y))`, where
`τ` is the clock of the first-tail cut.  It is at most `r (4 r + 4) = topClockR r`; no edge
raises it; the rightmost marked violator's edge lowers it; and it is zero exactly on the
repaired coloured cut.

Consumer: `TopClockPhaseBundle.marked` (TopClockAssembly).
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false

/-- The states that extend the cut `Z0` along a word.

Consumer: `topClockMarkedDebtPhase_repaired`. -/
def MarkedFrom {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z0 Y : TopFixedTraceState n) : Prop :=
  ∃ w : List (Fin n), Y = topFixedTraceRun ring C (Z0.2 ++ w)

/-- Auxiliary fact `fold_clock` of the old-pending repair.

Consumer: `topClockMarkedDebtPhase_repaired`. -/
theorem fold_clock {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) :
    ∀ (w : List (Fin n)) (Z : TopFixedTraceState n),
      (w.foldl (topFixedTraceNext ring C) Z).1.2.clock = Z.1.2.clock + w.length := by
  intro w
  induction w with
  | nil => intro Z; simp
  | cons e rest ih =>
      intro Z
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      simp [topFixedTraceNext, digitAuditStep]
      omega

/-- The clock of an extension is at least the clock of the cut.

Consumer: `topClockMarkedDebtPhase_repaired`. -/
theorem markedFrom_clock {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z0 Y : TopFixedTraceState n) (h0 : topClockReached ring C Z0) (h : MarkedFrom ring C Z0 Y) :
    Z0.1.2.clock ≤ Y.1.2.clock := by
  obtain ⟨w, hw⟩ := h
  rw [hw, topFixedTraceRunAppendWord]
  have : topFixedTraceRun ring C Z0.2 = Z0 := h0.symm
  rw [this, fold_clock]
  omega

/-- Auxiliary fact `markedFrom_start` of the old-pending repair.

Consumer: `topClockMarkedDebtPhase_repaired`. -/
theorem markedFrom_start {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z0 : TopFixedTraceState n) (h0 : topClockReached ring C Z0) : MarkedFrom ring C Z0 Z0 :=
  ⟨[], by rw [List.append_nil]; exact h0⟩

/-- Auxiliary fact `markedFrom_next` of the old-pending repair.

Consumer: `topClockMarkedDebtPhase_repaired`. -/
theorem markedFrom_next {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z0 Y : TopFixedTraceState n) (e : Fin n) (h : MarkedFrom ring C Z0 Y) :
    MarkedFrom ring C Z0 (topFixedTraceNext ring C Y e) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w ++ [e], ?_⟩
  rw [← List.append_assoc, topFixedTraceRunAppendWord ring C (Z0.2 ++ w) [e], ← hw]
  rfl

/-- Auxiliary fact `markedFrom_reached` of the old-pending repair.

Consumer: `topClockMarkedDebtPhase_repaired`. -/
theorem markedFrom_reached {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z0 Y : TopFixedTraceState n) (h : MarkedFrom ring C Z0 Y) : topClockReached ring C Y := by
  obtain ⟨w, hw⟩ := h
  unfold topClockReached
  rw [hw, topFixedTraceRun_snd]

/-- Auxiliary fact `markedFrom_down` of the old-pending repair.

Consumer: `topClockMarkedDebtPhase_repaired`. -/
theorem markedFrom_down {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z0 Y : TopFixedTraceState n) (hcut : topFreshTailPermanentCut ring C s Z0)
    (h : MarkedFrom ring C Z0 Y) : MarkedDown ring C s Y := by
  obtain ⟨w, hw⟩ := h
  exact ⟨Z0, hcut, w, hw⟩

/-- The old flags are zero outside the window.

Consumer: `topClockMarkedDebtPhase_repaired`. -/
theorem oldFlag_lt {n : Nat} (s : Fin n) (τ : Nat) (Y : TopFixedTraceState n) (j : Nat)
    (h : oldFlag s τ Y j = true) : j < topClockSpan n :=
  ((oldFlag_iff s τ Y j).1 h).1

/-- The marked rank of the next state is below the marked rank of the abstract step of the
window edge of register `p`.

Consumer: `topClockMarkedDebtPhase_repaired`. -/
theorem rank_next_window {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) (p : Nat) (hp : p < topClockSpan n) :
    rank (topClockSpan n)
        (markCells (cellOf s (topFixedTraceNext ring C Z (winSite s p)))
          (oldFlag s τ (topFixedTraceNext ring C Z (winSite s p)))) ≤
      rank (topClockSpan n)
        (markCells (edgeStep (topClockSpan n) (cellOf s Z) p)
          (flagsAt (topClockSpan n) (cellOf s Z) (oldFlag s τ Z) p)) := by
  have hag := link_window ring C s Z hg hreach p hp
  have h1 : rank (topClockSpan n)
      (markCells (cellOf s (topFixedTraceNext ring C Z (winSite s p)))
        (oldFlag s τ (topFixedTraceNext ring C Z (winSite s p)))) =
      rank (topClockSpan n)
        (markCells (edgeStep (topClockSpan n) (cellOf s Z) p)
          (oldFlag s τ (topFixedTraceNext ring C Z (winSite s p)))) := by
    apply rank_congr
    intro j hj
    simp [markCells, hag j hj]
  rw [h1]
  apply rank_mark_mono
  intro j hj
  exact old_next_window ring C s hg τ Z hreach p hp j (oldFlag_lt s τ _ j hj) hj

/-- Off the window and off the port, the window cells are unchanged.

Consumer: `rank_next_frame`. -/
theorem frame_cells {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Z : TopFixedTraceState n) (e : Fin n)
    (hnw : ¬ ∃ p, p < topClockSpan n ∧ e = winSite s p)
    (hb : e ≠ certSite s (topClockSpan n - 1)) :
    ∀ j, j < topClockSpan n → cellOf s (topFixedTraceNext ring C Z e) j = cellOf s Z j := by
  intro j hj
  have hr3 := span_ge_three hg.hn
  unfold cellOf
  apply siteCell_away
  · intro h; exact hnw ⟨j, hj, h.symm⟩
  · intro h
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

/-- The marked rank does not rise along an edge off the window and off the port.

Consumer: `topClockMarkedDebtPhase_repaired`. -/
theorem rank_next_frame {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) (Z : TopFixedTraceState n) (e : Fin n)
    (hnw : ¬ ∃ p, p < topClockSpan n ∧ e = winSite s p)
    (hb : e ≠ certSite s (topClockSpan n - 1)) :
    rank (topClockSpan n)
        (markCells (cellOf s (topFixedTraceNext ring C Z e)) (oldFlag s τ (topFixedTraceNext ring C Z e))) ≤
      rank (topClockSpan n) (markCells (cellOf s Z) (oldFlag s τ Z)) := by
  have hag := frame_cells ring C s hg Z e hnw hb
  have h1 : rank (topClockSpan n)
      (markCells (cellOf s (topFixedTraceNext ring C Z e)) (oldFlag s τ (topFixedTraceNext ring C Z e))) =
      rank (topClockSpan n) (markCells (cellOf s Z) (oldFlag s τ (topFixedTraceNext ring C Z e))) := by
    apply rank_congr
    intro j hj
    simp [markCells, hag j hj]
  rw [h1]
  apply rank_mark_mono
  intro j hj
  exact old_next_frame ring C s hg τ Z e hnw hb j (oldFlag_lt s τ _ j hj) hj

/-- The marked rank does not rise along the port edge.

Consumer: `topClockMarkedDebtPhase_repaired`. -/
theorem rank_next_port {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) (hτ : τ ≤ Z.1.2.clock) (e : Fin n)
    (hb : e = certSite s (topClockSpan n - 1)) (hinv : Inv (topClockSpan n) (cellOf s Z)) :
    rank (topClockSpan n)
        (markCells (cellOf s (topFixedTraceNext ring C Z e)) (oldFlag s τ (topFixedTraceNext ring C Z e))) ≤
      rank (topClockSpan n) (markCells (cellOf s Z) (oldFlag s τ Z)) := by
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
  have hc' : cellOf s (topFixedTraceNext ring C Z e) 0 = portClean (cellOf s Z 0) ∨
      ∃ t, cellOf s (topFixedTraceNext ring C Z e) 0 = portAccept t (cellOf s Z 0) := hresp
  have hcells : ∀ j, j < topClockSpan n →
      cellOf s (topFixedTraceNext ring C Z e) j =
        setOne (cellOf s Z) 0 (cellOf s (topFixedTraceNext ring C Z e) 0) j := by
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0; simp [setOne]
    · simp only [setOne, if_neg hj0]; exact haway j (by omega) hj
  have ho : ∀ j, j < topClockSpan n → oldFlag s τ Z j = true → (cellOf s Z j).i.isP = true :=
    fun j _ h => oldFlag_isP s τ Z j h
  have hf : ∀ j, j < topClockSpan n → (cellOf s Z j).c = .fresh → (cellOf s Z j).i = .e :=
    fun j hj h => (hinv.1 j hj h).1
  have hstep := rank_port_old (topClockSpan n) (by omega) (cellOf s Z) (oldFlag s τ Z)
    (cellOf s (topFixedTraceNext ring C Z e) 0) hc' ho hf
  have h1 : rank (topClockSpan n)
      (markCells (cellOf s (topFixedTraceNext ring C Z e)) (oldFlag s τ (topFixedTraceNext ring C Z e))) =
      rank (topClockSpan n)
        (markCells (setOne (cellOf s Z) 0 (cellOf s (topFixedTraceNext ring C Z e) 0))
          (oldFlag s τ (topFixedTraceNext ring C Z e))) := by
    apply rank_congr
    intro j hj
    simp [markCells, hcells j hj]
  rw [h1]
  have h2 := rank_mark_mono (topClockSpan n)
    (setOne (cellOf s Z) 0 (cellOf s (topFixedTraceNext ring C Z e) 0))
    (flagsPort (cellOf s Z) (oldFlag s τ Z) (cellOf s (topFixedTraceNext ring C Z e) 0))
    (oldFlag s τ (topFixedTraceNext ring C Z e))
    (fun j hj => old_next_port ring C s hg τ Z hreach hτ e hb _ rfl j (oldFlag_lt s τ _ j hj) hj)
  exact Nat.le_trans h2 hstep

end MarkedCells
end L3

#print axioms L3.MarkedCells.rank_next_window
#print axioms L3.MarkedCells.rank_next_port
#print axioms L3.MarkedCells.rank_next_frame

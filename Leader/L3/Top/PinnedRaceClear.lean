import Leader.L3.Top.PinnedRaceFront
import Leader.L3.Top.PinnedRaceUnfav
import Leader.L3.Top.FinalMobileCost

/-!
# Q7 (P.12 favourable): the front clears the old suffix in at most `r` services

From a pinned favourable cut the window has the shape `FS r p` (`TopPinnedRaceFront`).  Every
real edge keeps the shape or retires the front, never raises the front work, and the edge of the
front lowers it; at the end the window has only `E/P` registers without carry, which together
with the pin is the pinned pending-only class.  Hence a pinned favourable cut reaches the pinned
pending-only class within mean `n * r`.

The new class value `topClockPinnedFavClasses` adds the pin to the favourable class (the
inherited favourable class only says `MarkedDown`, which cannot supply the pin); every other
field is that of `topClockPinnedClasses`.

Consumer: `TopClockPhaseBundle.favourable` (TopClockAssembly), first stage.
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The settled registers after the tail are non-tails.

Consumer: `fs_of_favourable`. -/
theorem misAt_sn {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (h : Fin (topClockSpan n))
    (hh : topClockConcreteMisplacedAt s Z h) :
    ∀ j, h.val < j → j < topClockSpan n → cellOf s Z j = { i := .sn, c := .off } := by
  obtain ⟨hL, hR, hH⟩ := misAt_cells s Z h hh
  intro j hj1 hj2
  obtain ⟨_, _, _, hright, _, _⟩ := hh
  obtain ⟨sample', _, _, _, _, hin', _⟩ := hright ⟨j, hj2⟩ (by simp; omega)
  have hc := (hR j (by omega) hj2).2
  unfold cellOf siteCell at hc ⊢
  unfold topClockConcreteInputAt at hin'
  have hq : (Z.1.1 (winSite s j)).qIn = .S sample'.value false := hin'
  simp only at hc ⊢
  rw [hq]
  simp only [absIn]
  rw [hc]
  simp

/-- The tail row: a nonborder settled tail before a settled non-tail becomes a front.

Consumer: `fs_of_favourable`. -/
theorem pair_tail_front : pair false false { i := .st, c := .off } { i := .sn, c := .off } =
    ({ i := .x, c := .off }, { i := .sn, c := .off }) := by
  simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS]

/-- **The favourable cut has the shape `FS`.**

Consumer: `topPinnedFavourableClear`. -/
theorem fs_of_favourable {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Z : TopFixedTraceState n)
    (hfav : topClockConcreteFavourable ring C s Z) :
    ∃ p, FS (topClockSpan n) p (cellOf s Z) := by
  obtain ⟨hreachZ, pre, h, hmt, hmis, hZ2, _⟩ := hfav
  have hr3 := span_ge_three hg.hn
  have hreachY : topClockReached ring C (topFixedTraceRun ring C pre) := by
    unfold topClockReached; rw [topFixedTraceRun_snd]
  have hZeq : Z = topFixedTraceNext ring C (topFixedTraceRun ring C pre) (winSite s h.val) := by
    have h1 : Z = topFixedTraceRun ring C Z.2 := hreachZ
    rw [h1, hZ2]
    exact topFixedTraceRunAppendWord ring C pre [certSite s (topClockSpan n + h.val)]
  have hh1 := hmis.1
  have hh2 := hmis.2.1
  obtain ⟨hL, hR, hH⟩ := misAt_cells s (topFixedTraceRun ring C pre) h hmis
  have hsn := misAt_sn s (topFixedTraceRun ring C pre) h hmis
  refine ⟨h.val, h.isLt, ?_, ?_, ?_⟩
  · intro j hj
    rw [hZeq]
    rw [link_window ring C s _ hg hreachY h.val h.isLt j (by omega)]
    unfold edgeStep
    rw [if_pos hh2]
    simp only [setTwo, if_neg (show j ≠ h.val by omega), if_neg (show j ≠ h.val + 1 by omega)]
    exact hL j hj
  · rw [hZeq]
    rw [link_window ring C s _ hg hreachY h.val h.isLt h.val h.isLt]
    unfold edgeStep
    rw [if_pos hh2]
    have hb : decide (h.val = 0) = false := by simp; omega
    have hy := hsn (h.val + 1) (by omega) hh2
    simp only [setTwo, if_true]
    rw [hb, hH, hy, pair_tail_front]
  · intro j hj1 hj2
    rw [hZeq]
    rw [link_window ring C s _ hg hreachY h.val h.isLt j hj2]
    unfold edgeStep
    rw [if_pos hh2]
    have hb : decide (h.val = 0) = false := by simp; omega
    have hy := hsn (h.val + 1) (by omega) hh2
    by_cases hjh : j = h.val + 1
    · subst hjh
      simp only [setTwo, if_neg (show h.val + 1 ≠ h.val by omega), if_true]
      rw [hb, hH, hy, pair_tail_front]
    · simp only [setTwo, if_neg (show j ≠ h.val by omega), if_neg hjh]
      exact hsn j hj1 hj2

/-- The shape only reads the first `r` registers.

Consumer: `fs_step_machine`. -/
theorem FS_congr (r p : Nat) (c1 c2 : Nat → Cell) (h : ∀ j, j < r → c1 j = c2 j)
    (hf : FS r p c1) : FS r p c2 := by
  obtain ⟨hpr, hL, hX, hR⟩ := hf
  refine ⟨hpr, fun j hj => by rw [← h j (by omega)]; exact hL j hj,
    by rw [← h p hpr]; exact hX, fun j h1 h2 => by rw [← h j h2]; exact hR j h1 h2⟩

/-- The cleared window only reads the first `r` registers.

Consumer: `fs_step_machine`. -/
theorem Clr_congr (r : Nat) (c1 c2 : Nat → Cell) (h : ∀ j, j < r → c1 j = c2 j)
    (hf : Clr r c1) : Clr r c2 := fun j hj => by rw [← h j hj]; exact hf j hj

/-- The front work only reads the first `r` registers.

Consumer: `fs_step_machine`. -/
theorem frontWork_agree (r : Nat) (c1 c2 : Nat → Cell) (h : ∀ j, j < r → c1 j = c2 j) :
    frontWork r c1 = frontWork r c2 :=
  frontWork_congr r c1 c2 (fun k hk => by unfold wX; rw [h k hk])

/-- **One real edge keeps the front shape or clears the window; the front work does not rise and
falls on the edge of the front.**

Consumer: `topPinnedFavourableClear`. -/
theorem fs_step_machine {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Y : TopFixedTraceState n)
    (hreach : topClockReached ring C Y) (p : Nat) (hfs : FS (topClockSpan n) p (cellOf s Y))
    (e : Fin n) :
    Clr (topClockSpan n) (cellOf s (topFixedTraceNext ring C Y e)) ∨
    ∃ p', FS (topClockSpan n) p' (cellOf s (topFixedTraceNext ring C Y e)) ∧
      frontWork (topClockSpan n) (cellOf s (topFixedTraceNext ring C Y e)) ≤
        frontWork (topClockSpan n) (cellOf s Y) ∧
      (e = winSite s p → frontWork (topClockSpan n) (cellOf s (topFixedTraceNext ring C Y e)) + 1 ≤
        frontWork (topClockSpan n) (cellOf s Y)) := by
  have hr3 := span_ge_three hg.hn
  have hpr := hfs.1
  by_cases hw : ∃ q, q < topClockSpan n ∧ e = winSite s q
  · obtain ⟨q, hq, rfl⟩ := hw
    have hag := link_window ring C s Y hg hreach q hq
    by_cases hq1 : q + 1 < topClockSpan n
    · rcases fs_edge (topClockSpan n) p q (cellOf s Y) hq1 hfs with ⟨hF, hwk, hne⟩ | ⟨hF, hwk, hqp⟩
      · right
        refine ⟨p, FS_congr _ _ _ _ (fun j hj => (hag j hj).symm) hF, ?_, ?_⟩
        · rw [frontWork_agree _ _ _ hag]; exact hwk
        · intro hh
          exact absurd (winSite_inj hg.hn s q p (by omega) (by omega) hh) hne
      · right
        refine ⟨p + 1, FS_congr _ _ _ _ (fun j hj => (hag j hj).symm) hF, ?_, ?_⟩
        · rw [frontWork_agree _ _ _ hag]; omega
        · intro _
          rw [frontWork_agree _ _ _ hag]; exact hwk
    · have hqr : q = topClockSpan n - 1 := by omega
      have hedge : edgeStep (topClockSpan n) (cellOf s Y) q =
          edgeStep (topClockSpan n) (cellOf s Y) (topClockSpan n - 1) := by
        unfold edgeStep
        rw [if_neg hq1, if_neg (by omega)]
      rcases fs_term (topClockSpan n) p (cellOf s Y) (by omega) hfs with
        ⟨hF, hwk, hne⟩ | ⟨hC, hp⟩
      · right
        rw [← hedge] at hF hwk
        refine ⟨p, FS_congr _ _ _ _ (fun j hj => (hag j hj).symm) hF, ?_, ?_⟩
        · rw [frontWork_agree _ _ _ hag]; exact hwk
        · intro hh
          have := winSite_inj hg.hn s q p (by omega) (by omega) hh
          omega
      · left
        rw [← hedge] at hC
        exact Clr_congr _ _ _ (fun j hj => (hag j hj).symm) hC
  · rcases link_shape ring C s Y hg hreach e hw with hag | hag | ⟨t, hag⟩
    · right
      refine ⟨p, FS_congr _ _ _ _ (fun j hj => (hag j hj).symm) hfs, ?_, ?_⟩
      · rw [frontWork_agree _ _ _ hag]; exact Nat.le_refl _
      · intro hh; exact absurd ⟨p, hfs.1, hh⟩ hw
    · right
      have hp := fs_port (topClockSpan n) p (cellOf s Y) (by omega) hfs _ (Or.inl rfl)
      refine ⟨p, FS_congr _ _ _ _ (fun j hj => (hag j hj).symm) hp.1, ?_, ?_⟩
      · rw [frontWork_agree _ _ _ hag, hp.2]; exact Nat.le_refl _
      · intro hh; exact absurd ⟨p, hfs.1, hh⟩ hw
    · right
      have hp := fs_port (topClockSpan n) p (cellOf s Y) (by omega) hfs _ (Or.inr ⟨t, rfl⟩)
      refine ⟨p, FS_congr _ _ _ _ (fun j hj => (hag j hj).symm) hp.1, ?_, ?_⟩
      · rw [frontWork_agree _ _ _ hag, hp.2]; exact Nat.le_refl _
      · intro hh; exact absurd ⟨p, hfs.1, hh⟩ hw

/-- A weighted sum is at least any single weight below the bound.

Consumer: `topPinnedFavourableClear`. -/
theorem wsum_ge_at (f : Nat → Nat) : ∀ r p, p < r → f p ≤ wsum f r
  | 0, _, h => by omega
  | r + 1, p, h => by
      simp only [wsum]
      by_cases hp : p = r
      · subst hp; omega
      · have := wsum_ge_at f r p (by omega)
        omega

/-- **A pinned cleared window is the pinned pending-only class.**

Consumer: `topPinnedFavourableClear`. -/
theorem pendingOnly_of_clr {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Y : TopFixedTraceState n)
    (hp : topClockPinned ring C s Y) (hc : Clr (topClockSpan n) (cellOf s Y)) :
    (topClockPinnedClasses ring C s).pendingOnly Y := by
  obtain ⟨Y0, hcut, hfrom, hold⟩ := hp
  refine ⟨⟨Y0, hcut, hfrom, hold⟩, markedFrom_down ring C s Y0 Y hcut hfrom,
    markedFrom_reached ring C Y0 Y hfrom,
    markedDown_pure ring C s Y (markedFrom_down ring C s Y0 Y hcut hfrom),
    suffix_of_pinned ring C s hg Y0 Y hcut hfrom hold, ?_⟩
  intro j
  obtain ⟨hep, hoff⟩ := hc j.val j.isLt
  refine ⟨?_, ?_⟩
  · unfold cellOf winSite at hep
    exact (siteCell_ep _ _).1 hep
  · unfold cellOf winSite at hoff
    rcases hq : (Y.1.1 (certSite s (topClockSpan n + j.val))).qCarry with _ | ⟨a, b⟩
    · rfl
    · exfalso
      exact (siteCell_carry_on Y (certSite s (topClockSpan n + j.val))).2 (by rw [hq]; rfl) hoff

/-- **P.12 favourable, clearing stage.**  From a pinned favourable cut, the outward front clears
the old suffix and the pinned pending-only class is reached within mean `n * r`.

Consumer: `TopClockPhaseBundle.favourable` (TopClockAssembly), first stage. -/
theorem topPinnedFavourableClear {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) (Z : TopFixedTraceState n)
    (hp : topClockPinned ring C s Z) (hfav : topClockConcreteFavourable ring C s Z) :
    UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C)
      (topClockPinnedClasses ring C s).pendingOnly Z ((n * topClockSpan n : Nat) : Rat) := by
  classical
  have hg : WinGeo ring C s := ⟨hn, hl, hbad⟩
  have hn0 : 0 < n := by omega
  have hr3 := span_ge_three hn
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (topFixedTraceNext ring C) (topClockPinnedClasses ring C s).pendingOnly hn0 Z
    (n * topClockSpan n)).2
  intro T
  let T' : TopFixedTraceState n → Prop := (topClockPinnedClasses ring C s).pendingOnly
  let I : TopFixedTraceState n → Prop := fun Y =>
    (topClockReached ring C Y ∧ topClockPinned ring C s Y ∧
      ∃ q, FS (topClockSpan n) q (cellOf s Y)) ∨ T' Y
  let Φ : TopFixedTraceState n → Nat := fun Y => frontWork (topClockSpan n) (cellOf s Y)
  let chosen : TopFixedTraceState n → Fin n := fun Y =>
    if hh : ∃ q, FS (topClockSpan n) q (cellOf s Y) then winSite s (Classical.choose hh) else s
  obtain ⟨p0, hp0⟩ := fs_of_favourable ring C s hg Z hfav
  have hreachZ : topClockReached ring C Z := hfav.1
  have hcost := topFinalCostOfRows (topFixedTraceNext ring C) I T' Φ chosen
    (by
      intro Y hI hnot e
      rcases hI with ⟨hr, hpin, q, hq⟩ | hT
      · have hpin' := topPreparationPinnedNext ring C s hg Y e hpin
        rcases fs_step_machine ring C s hg Y hr q hq e with hC | ⟨q', hq', _, _⟩
        · exact Or.inr (pendingOnly_of_clr ring C s hg _ hpin' hC)
        · exact Or.inl ⟨topClockReachedNext ring C Y e hr, hpin', q', hq'⟩
      · exact absurd hT hnot)
    (by
      intro Y hI hnot
      rcases hI with ⟨hr, hpin, q, hq⟩ | hT
      · have h1 := wsum_ge_at (wX (cellOf s Y)) (topClockSpan n) q hq.1
        have h2 : wX (cellOf s Y) q = 1 := by unfold wX; rw [hq.2.2.1]; simp
        show 0 < wsum (wX (cellOf s Y)) (topClockSpan n)
        omega
      · exact absurd hT hnot)
    (by
      intro Y hI hnot e
      rcases hI with ⟨hr, hpin, q, hq⟩ | hT
      · have hpin' := topPreparationPinnedNext ring C s hg Y e hpin
        rcases fs_step_machine ring C s hg Y hr q hq e with hC | ⟨q', hq', hw, _⟩
        · exact Or.inl (pendingOnly_of_clr ring C s hg _ hpin' hC)
        · exact Or.inr hw
      · exact absurd hT hnot)
    (by
      intro Y hI hnot
      rcases hI with ⟨hr, hpin, q, hq⟩ | hT
      · have hex : ∃ q, FS (topClockSpan n) q (cellOf s Y) := ⟨q, hq⟩
        have hsel : chosen Y = winSite s (Classical.choose hex) := by
          show (if hh : ∃ q, FS (topClockSpan n) q (cellOf s Y) then
            winSite s (Classical.choose hh) else s) = _
          rw [dif_pos hex]
        have hspec := Classical.choose_spec hex
        have hpin' := topPreparationPinnedNext ring C s hg Y (chosen Y) hpin
        rw [hsel] at hpin' ⊢
        rcases fs_step_machine ring C s hg Y hr _ hspec (winSite s (Classical.choose hex)) with
          hC | ⟨q', hq', hw, hd⟩
        · exact Or.inl (pendingOnly_of_clr ring C s hg _ hpin' hC)
        · exact Or.inr (hd rfl)
      · exact absurd hT hnot)
    Z (Or.inl ⟨hreachZ, hp, p0, hp0⟩) T
  refine Nat.le_trans hcost ?_
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul_left
  have := wsum_le_below (wX (cellOf s Z)) 1 (topClockSpan n) (fun k _ => by
    unfold wX; split <;> omega)
  show wsum (wX (cellOf s Z)) (topClockSpan n) ≤ _
  omega

end MarkedCells
end L3

#print axioms L3.MarkedCells.fs_of_favourable
#print axioms L3.MarkedCells.fs_step_machine
#print axioms L3.MarkedCells.pendingOnly_of_clr
#print axioms L3.MarkedCells.topPinnedFavourableClear

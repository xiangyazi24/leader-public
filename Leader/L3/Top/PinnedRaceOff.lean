import Leader.L3.Top.PinnedRaceStep

/-!
# Q7 (P.12 race): the misplaced-tail shape survives every third edge

`left_after`: the registers before the tail stay `E/P` without carry.  `misAt_off`: after any
edge other than the outgoing edge `winSite s h` and the incoming edge `winSite s (h - 1)`, the
cut is still misplaced at `h`, with the same sampled tail and settled non-tails.

Consumer: `Leader/L3/Top/PinnedRacePhase.lean`.
-/

namespace L3
namespace MarkedCells

open Classical

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The registers before the tail stay `E/P` without carry under a third edge.

Consumer: `misAt_off`. -/
theorem left_after {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) (h : Nat) (hh1 : 1 ≤ h) (hh2 : h + 1 < topClockSpan n)
    (hL : ∀ j, j < h → EP (cellOf s Z j) ∧ (cellOf s Z j).c = .off)
    (e : Fin n) (he1 : e ≠ winSite s h) (he2 : e ≠ winSite s (h - 1)) :
    ∀ j, j < h → EP (cellOf s (topFixedTraceNext ring C Z e) j) ∧
      (cellOf s (topFixedTraceNext ring C Z e) j).c = .off := by
  have hr3 := span_ge_three hg.hn
  by_cases hw : ∃ p, p < topClockSpan n ∧ e = winSite s p
  · obtain ⟨p, hp, rfl⟩ := hw
    have hph : p ≠ h := fun hh => he1 (by rw [hh])
    have hph1 : p ≠ h - 1 := fun hh => he2 (by rw [hh])
    have hag := link_window ring C s Z hg hreach p hp
    intro j hj
    rw [hag j (by omega)]
    unfold edgeStep
    by_cases hp1 : p + 1 < topClockSpan n
    · rw [if_pos hp1]
      by_cases hlo : p + 2 ≤ h
      · have hpp := pair_ep_off (decide (p = 0)) (cellOf s Z p) (cellOf s Z (p + 1))
          (hL p (by omega)).1 (hL p (by omega)).2 (hL (p + 1) (by omega)).1
          (hL (p + 1) (by omega)).2
        by_cases hjp : j = p
        · subst hjp; simp only [setTwo, if_true]; exact ⟨hpp.1, hpp.2.1⟩
        · by_cases hjp1 : j = p + 1
          · subst hjp1; simp only [setTwo, if_neg hjp, if_true]; exact ⟨hpp.2.2.1, hpp.2.2.2⟩
          · simp only [setTwo, if_neg hjp, if_neg hjp1]; exact hL j hj
      · have hjp : j ≠ p := by omega
        have hjp1 : j ≠ p + 1 := by omega
        simp only [setTwo, if_neg hjp, if_neg hjp1]; exact hL j hj
    · rw [if_neg hp1]
      have hjp : j ≠ topClockSpan n - 1 := by omega
      simp only [setOne, if_neg hjp]; exact hL j hj
  · intro j hj
    rcases link_shape ring C s Z hg hreach e hw with hag | hag | ⟨t, hag⟩
    · rw [hag j (by omega)]; exact hL j hj
    · rw [hag j (by omega)]
      by_cases hj0 : j = 0
      · subst hj0
        simp only [setOne, if_true]
        obtain ⟨hep, hc⟩ := hL 0 hj
        unfold portClean
        rw [if_pos hc]; exact ⟨hep, hc⟩
      · simp only [setOne, if_neg hj0]; exact hL j hj
    · rw [hag j (by omega)]
      by_cases hj0 : j = 0
      · subst hj0
        simp only [setOne, if_true]
        obtain ⟨hep, hc⟩ := hL 0 hj
        unfold portAccept
        by_cases hx : cellOf s Z 0 = { i := .e, c := .off }
        · rw [if_pos hx]
          refine ⟨?_, rfl⟩
          unfold EP
          cases t <;> simp [Inp.isP]
        · rw [if_neg hx]; exact ⟨hep, hc⟩
      · simp only [setOne, if_neg hj0]; exact hL j hj

/-- **A third edge leaves a misplaced-tail cut misplaced at the same tail.**

Consumer: `Leader/L3/Top/PinnedRacePhase.lean`. -/
theorem misAt_off {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) (h : Fin (topClockSpan n))
    (hmis : topClockConcreteMisplacedAt s Z h) (e : Fin n)
    (he1 : e ≠ winSite s h.val) (he2 : e ≠ winSite s (h.val - 1)) :
    topClockConcreteMisplacedAt s (topFixedTraceNext ring C Z e) h := by
  have hr3 := span_ge_three hg.hn
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hfrz := publicFrozen_reached ring C Z hreach
  have hlz : ∀ v : Fin n, (Z.1.1 v).l = false := fun v => by rw [(hfrz v).1]; exact hg.hl v
  obtain ⟨hcellsL, hcellsR, hcellsH⟩ := misAt_cells s Z h hmis
  obtain ⟨hh1, hh2, ⟨sample, hrec, hlane, hsite, htailf, hin, hatom⟩, hright, hleft, hcar⟩ := hmis
  have hpred : ∀ j, 1 ≤ j → ring.rightNeighbor e = winSite s j → e = winSite s (j - 1) := by
    intro j hj hrne
    apply certSite_pred ring s e (topClockSpan n + (j - 1))
    have : topClockSpan n + (j - 1) + 1 = topClockSpan n + j := by omega
    rw [this]; exact hrne
  have hbeta : ∀ j, 1 ≤ j → j < topClockSpan n → (Z.1.1 (winSite s j)).beta = false := by
    intro j hj hjr
    rw [(hfrz _).2, winSite_beta ring C s hg.hbad j hjr]
    simp [show j ≠ 0 by omega]
  have hrec' : ∀ x : DigitSample (compileAdvice (ceilLogTwo n)) n,
      DigitRecordedSample Z.1.2 x → DigitRecordedSample (topFixedTraceNext ring C Z e).1.2 x :=
    fun x hx => digitRecordedSampleStep ring (piD Z.1.1) Z.1.2 e x hx
  have right_kept : ∀ j, h.val < j → ∀ (hjr : j < topClockSpan n)
      (v : Fin (compileAdvice (ceilLogTwo n)).topA), (Z.1.1 (winSite s j)).qIn = .S v false →
      ((topFixedTraceNext ring C Z e).1.1 (winSite s j)).qIn = .S v false ∧
      ((topFixedTraceNext ring C Z e).1.1 (winSite s j)).qCarry = .OFF ∧
      ((topFixedTraceNext ring C Z e).1.2.current (winSite s j)).comparison.input =
        (Z.1.2.current (winSite s j)).comparison.input := by
    intro j hj hjr v hq
    have hk : (Z.1.1 (winSite s j)).qCarry = .OFF := hcar ⟨j, hjr⟩
    have hb := hbeta j (by omega) hjr
    by_cases h1 : e = winSite s j
    · subst h1
      exact step_settled_x ring C Z _ (hlz _) (hlz _) v hq hk hb
    · by_cases h2 : ring.rightNeighbor e = winSite s j
      · have hej := hpred j (by omega) h2
        have hjh : j - 1 ≠ h.val := fun hh => he1 (by rw [hej, hh])
        have hjh2 : h.val < j - 1 := by omega
        obtain ⟨sample', _, _, _, _, hin', _⟩ := hright ⟨j - 1, by omega⟩ (by simp; omega)
        have hq' : (Z.1.1 e).qIn = .S sample'.value false := by rw [hej]; exact hin'
        have hk' : (Z.1.1 e).qCarry = .OFF := by rw [hej]; exact hcar ⟨j - 1, by omega⟩
        have hb' : (Z.1.1 e).beta = false := by rw [hej]; exact hbeta (j - 1) (by omega) (by omega)
        have key := step_settled_y ring hn2 C Z e (hlz _) (hlz _) sample'.value v hq' hk' hb'
          (by rw [h2]; exact hq) (by rw [h2]; exact hk) (by rw [h2]; exact hb)
        rw [h2] at key
        exact key
      · have haw := step_away ring C Z e (winSite s j) (fun hh => h1 hh.symm)
          (fun hh => h2 hh.symm)
        exact ⟨by rw [haw.1]; exact hq, by rw [haw.2.1]; exact hk, haw.2.2⟩
  have hawh := step_away ring C Z e (winSite s h.val) (fun hh => he1 hh.symm)
    (fun hh => he2 (hpred h.val hh1 hh.symm))
  have hleftNew := left_after ring C s hg Z hreach h.val hh1 hh2 hcellsL e he1 he2
  refine ⟨hh1, hh2, ⟨sample, hrec' sample hrec, hlane, hsite, htailf, ?_, ?_⟩, ?_, ?_, ?_⟩
  · show ((topFixedTraceNext ring C Z e).1.1 (winSite s h.val)).qIn = _
    rw [hawh.1]; exact hin
  · show ((topFixedTraceNext ring C Z e).1.2.current (winSite s h.val)).comparison.input = _
    rw [hawh.2.2]; exact hatom
  · intro j hj
    obtain ⟨sample', hrec2, hl', hs', ht', hin', hat'⟩ := hright j hj
    have hk := right_kept j.val hj j.isLt sample'.value hin'
    refine ⟨sample', hrec' sample' hrec2, hl', hs', ht', ?_, ?_⟩
    · show ((topFixedTraceNext ring C Z e).1.1 (winSite s j.val)).qIn = _
      rw [hk.1]
    · show ((topFixedTraceNext ring C Z e).1.2.current (winSite s j.val)).comparison.input = _
      rw [hk.2.2]; exact hat'
  · intro j hj
    have := (hleftNew j.val hj).1
    unfold cellOf winSite at this
    exact (siteCell_ep _ _).1 this
  · intro j
    by_cases hjh : j.val < h.val
    · have := (hleftNew j.val hjh).2
      unfold cellOf winSite at this
      show ((topFixedTraceNext ring C Z e).1.1 (winSite s j.val)).qCarry = .OFF
      rcases hq : ((topFixedTraceNext ring C Z e).1.1 (certSite s (topClockSpan n + j.val))).qCarry
        with _ | ⟨a, b⟩
      · exact hq
      · exfalso
        have hon := (siteCell_carry_on (topFixedTraceNext ring C Z e)
          (certSite s (topClockSpan n + j.val))).2 (by rw [hq]; rfl)
        exact hon this
    · by_cases hjeq : j.val = h.val
      · have hjj : j = h := Fin.ext hjeq
        subst hjj
        show ((topFixedTraceNext ring C Z e).1.1 (winSite s j.val)).qCarry = .OFF
        rw [hawh.2.1]; exact hcar j
      · have hj : h.val < j.val := by omega
        obtain ⟨sample', _, _, _, _, hin', _⟩ := hright j hj
        exact (right_kept j.val hj j.isLt sample'.value hin').2.1

end MarkedCells
end L3

#print axioms L3.MarkedCells.left_after
#print axioms L3.MarkedCells.misAt_off

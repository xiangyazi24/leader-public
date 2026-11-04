import Leader.L3.Top.PinnedPhaseFavourable
import Leader.L3.Top.PinnedRaceUnfav

/-!
# Q7 (P.12--P.13): the favourable phase on the classes without an earlier strict stop

From a favourable cut (or a strict stop) of `topClockStopClasses`, the expected time to a strict
stop is at most `n * (r + V)`:

* the outward front clears the window within `n * r` and the cleared window is an aligned fill
  start (`topAlignedClear`: `|Q| - pending` is constant along the clearing and `0 mod r` at the
  misplaced cut);
* the aligned fill stage forms the settled tail at the border (`topFillStageAligned`) and the
  aligned completion records the strict stop (`aligned_strict_cost`), within `n * V`.

Consumer: `TopClockPhaseBundle.favourable` (TopClockAssembly).
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- Forming the front from the settled tail keeps the number of pending registers.

Consumer: `favourable_start`. -/
theorem pendCnt_front_form (r h : Nat) (c : Nat → Cell) (hh1 : 1 ≤ h) (hh2 : h + 1 < r)
    (ht : c h = { i := .st, c := .off }) (hs : c (h + 1) = { i := .sn, c := .off }) :
    pendCnt r (edgeStep r c h) = pendCnt r c := by
  unfold edgeStep
  rw [if_pos hh2]
  have hb : decide (h = 0) = false := by simp; omega
  rw [hb, ht, hs, pair_tail_front]
  simp only []
  unfold pendCnt
  have hw := wsum_edit (pl c) (pl (setTwo c h { i := .x, c := .off } { i := .sn, c := .off })) h
    (fun k h1 h2 => by simp [pl, setTwo, h1, h2]) r (by omega)
  have e1 : pl c h = 0 := by simp [pl, ht, Inp.isP]
  have e2 : pl c (h + 1) = 0 := by simp [pl, hs, Inp.isP]
  have e3 : pl (setTwo c h { i := .x, c := .off } { i := .sn, c := .off }) h = 0 := by
    simp [pl, setTwo, Inp.isP]
  have e4 : pl (setTwo c h { i := .x, c := .off } { i := .sn, c := .off }) (h + 1) = 0 := by
    simp [pl, setTwo, Inp.isP]
  omega

/-- **The start of the favourable phase**: a favourable cut of the prepared classes is a front
window whose queue satisfies `|Q| = pending + r * m`, extending a permanent cut.

Consumer: `topStopFavourablePhase`. -/
theorem favourable_start {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Z : TopFixedTraceState n)
    (hfav : (topClockPrepClasses ring C s).favourable Z) :
    ∃ Y0, topFreshTailPermanentCut ring C s Y0 ∧ MarkedFrom ring C Y0 Z ∧
      topClockNoOldPending s Z Y0.1.2.clock ∧
      (∃ m, (paQ s Z Y0.1.2.clock).length = pendCnt (topClockSpan n) (cellOf s Z) +
        topClockSpan n * m) ∧ ∃ p, FS (topClockSpan n) p (cellOf s Z) := by
  have hr3 := span_ge_three hg.hn
  obtain ⟨_, _, hconc, pre', e', hZ2, Y0, hcut, hfromW, holdW, hlW, haW⟩ := hfav
  have hfs := fs_of_favourable ring C s hg Z hconc
  obtain ⟨hreachZ, pre, h, hmt, hmis, hZ2', hX⟩ := hconc
  have hpp : pre = pre' := by
    have := List.append_inj' (hZ2'.symm.trans hZ2) (by simp)
    exact this.1
  subst hpp
  have hreachW : topClockReached ring C (topFixedTraceRun ring C pre) := by
    unfold topClockReached; rw [topFixedTraceRun_snd]
  have hZeq : Z = topFixedTraceNext ring C (topFixedTraceRun ring C pre) (winSite s h.val) := by
    have h1 : Z = topFixedTraceRun ring C Z.2 := hreachZ
    rw [h1, hZ2']
    exact topFixedTraceRunAppendWord ring C pre [certSite s (topClockSpan n + h.val)]
  have hclockW : Y0.1.2.clock ≤ (topFixedTraceRun ring C pre).1.2.clock :=
    markedFrom_clock ring C Y0 _ hcut.1 hfromW
  have hh1 := hmis.1
  have hh2 := hmis.2.1
  obtain ⟨hL, hR, hH⟩ := misAt_cells s (topFixedTraceRun ring C pre) h hmis
  have hsn := misAt_sn s (topFixedTraceRun ring C pre) h hmis
  -- the anchor and the pure stream of the misplaced cut
  obtain ⟨hreach0, hgen, anchor, hanchor, htime, hfuture⟩ := hcut
  have hpure : topClockConcretePureStream s (topFixedTraceRun ring C pre) anchor := by
    obtain ⟨w, hw⟩ := hfromW
    rw [hw]; exact hfuture w
  have hcut' : topFreshTailPermanentCut ring C s Y0 := ⟨hreach0, hgen, anchor, hanchor, htime, hfuture⟩
  obtain ⟨m, hm⟩ := misplaced_count s (topFixedTraceRun ring C pre) anchor hpure
    (by rw [htime]; exact hlW) (by rw [htime]; exact haW) h.val hh1 hh2
    (fun j hj => by
      obtain ⟨hep, hoff⟩ := hL j hj
      rcases hep with h' | h'
      · exact Or.inl h'
      · rcases hx : (cellOf s (topFixedTraceRun ring C pre) j).i with _ | _ | _ | _ | _ | _ <;>
          rw [hx] at h' <;> simp [Inp.isP] at h' ⊢)
    (by rw [hH])
    (fun j hj1 hj2 => by rw [hsn j hj1 hj2])
  refine ⟨Y0, hcut', ?_, ?_, ?_, hfs⟩
  · rw [hZeq]; exact markedFrom_next ring C Y0 _ _ hfromW
  · rw [hZeq]; exact noOld_next ring C s hg Y0.1.2.clock _ hreachW hclockW _ holdW
  · refine ⟨m, ?_⟩
    have hQ : paQ s Z anchor.time = paQ s (topFixedTraceRun ring C pre) anchor.time := by
      rw [hZeq]; exact paQ_away ring C s _ _ _ (win_ne_port hg.hn s h.val h.isLt)
    rw [htime] at hm hQ
    rw [hQ, hm]
    have hcells : ∀ j, j < topClockSpan n → cellOf s Z j =
        edgeStep (topClockSpan n) (cellOf s (topFixedTraceRun ring C pre)) h.val j := by
      intro j hj
      rw [hZeq]
      exact link_window ring C s _ hg hreachW h.val h.isLt j hj
    rw [pendCnt_congr _ _ _ hcells, pendCnt_front_form _ h.val _ hh1 hh2 hH
      (hsn (h.val + 1) (by omega) hh2)]

/-- **P.12--P.13 favourable phase for the classes without an earlier strict stop.**

Consumer: `TopClockPhaseBundle.favourable` (TopClockAssembly). -/
theorem topStopFavourablePhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockFavourablePhase ring C s (topClockStopClasses ring C s) := by
  classical
  have hg : WinGeo ring C s := ⟨hn, hl, hbad⟩
  have hn0 : 0 < n := by omega
  have hr3 := span_ge_three hn
  intro Z hZ
  by_cases hstop : topFixedStrictStop ring C s Z
  · exact hit_now _ hn0 _ Z hstop _
  · have hfav : (topClockStopClasses ring C s).favourable Z := by
      rcases hZ with h | h
      · exact absurd h hstop
      · exact h
    obtain ⟨hfp, hNZ⟩ := hfav
    obtain ⟨Y0, hcut, hfrom, hold, hcount, hfs⟩ := favourable_start ring C s hg Z hfp
    -- the second stage: aligned fill and aligned completion
    let T : TopFixedTraceState n → Prop := topFixedStrictStop ring C s
    let A : TopFixedTraceState n → Prop := fun Y =>
      (PuPinAt ring C s Y0 Y ∧ FillShape (topClockSpan n) (cellOf s Y) ∧
        aOf s Y Y0.1.2.clock = 0) ∧ NoPrefixStop ring C s Y
    have h2 : ∀ y, A y → UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C) T y
        ((n * topClockV (topClockSpan n) : Nat) : Rat) := by
      intro y hy
      obtain ⟨⟨hPy, hsy, hay⟩, hNy⟩ := hy
      let A2 : TopFixedTraceState n → Prop := fun Y =>
        AlignReg ring C s Y0 Y ∧ NoPrefixStop ring C s Y
      have e1 := topFillStageAligned ring hn C s hl hbad Y0 y hPy hsy hay
      have e1' := phase_nps_hit ring C s hn0
        (fun Y => PuPinAt ring C s Y0 Y ∧ ExitShape (topClockSpan n) (cellOf s Y) 0)
        (fun Y => A2 Y ∨ T Y) (fun Y hY => Or.inr hY)
        (fun Y hNY hY => Or.inl ⟨⟨hY.1, exit_align (by omega) hY.2⟩, hNY⟩)
        y (Or.inl hNy) _ e1
      have e2 : ∀ w, A2 w → UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C) T w
          ((n * (topClockSpan n + 1) : Nat) : Rat) := by
        intro w hw
        have hcost := aligned_strict_cost ring C s hg Y0 w hw.1 (Or.inl hw.2)
        exact (UniformFirstHit.expectedHittingTimeAtMost_iff_cost (topFixedTraceNext ring C) _
          hn0 w (n * (topClockSpan n + 1))).2 hcost
      have e3 := Prob.expectedHittingTimeAtMost_stage_le (topFixedTraceNext ring C) hn0 y A2 T
        (n * (2 * topClockSpan n * topClockSpan n + 4 * topClockSpan n + 2))
        (n * (topClockSpan n + 1)) e1' e2
      have e : n * (2 * topClockSpan n * topClockSpan n + 4 * topClockSpan n + 2) +
          n * (topClockSpan n + 1) = n * topClockV (topClockSpan n) := by
        rw [← Nat.mul_add]
        unfold topClockV
        congr 1
        rw [Nat.pow_two, Nat.mul_assoc]
        omega
      rw [e] at e3
      exact e3
    -- the first stage: the aligned clearing
    have h1 := topAlignedClear ring hn C s hl hbad Y0 Z hcut hfrom hold hcount hfs
    have h1' := phase_nps_hit ring C s hn0
      (fun Y => PuPinAt ring C s Y0 Y ∧ FillShape (topClockSpan n) (cellOf s Y) ∧
        aOf s Y Y0.1.2.clock = 0)
      (fun Y => A Y ∨ T Y) (fun Y hY => Or.inr hY)
      (fun Y hNY hY => Or.inl ⟨hY, hNY⟩)
      Z (Or.inl hNZ) _ h1
    have h3 := Prob.expectedHittingTimeAtMost_stage_le (topFixedTraceNext ring C) hn0 Z A T
      (n * topClockSpan n) (n * topClockV (topClockSpan n)) h1' h2
    have e : n * topClockSpan n + n * topClockV (topClockSpan n) =
        n * (topClockSpan n + topClockV (topClockSpan n)) := by rw [Nat.mul_add]
    rw [e] at h3
    exact h3

/-- **The seven proved phase contracts at one class value**: marked, settled, mobile,
preparation, race, favourable and unfavourable, all for `topClockStopClasses`.

Consumer: `TopClockPhaseBundle` (TopClockAssembly), fields `marked`, `settled`, `mobile`,
`prepare`, `race`, `favourable`, `unfavourable`. -/
theorem topStopPhases {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockMarkedDebtPhase ring C s (topClockStopClasses ring C s) ∧
    TopClockSettledWorkPhase ring C s (topClockStopClasses ring C s) ∧
    TopClockFinalMobilePhase ring C s (topClockStopClasses ring C s) ∧
    TopClockPreparationPhase ring C s (topClockStopClasses ring C s) ∧
    TopClockRacePhase ring C s (topClockStopClasses ring C s) ∧
    TopClockFavourablePhase ring C s (topClockStopClasses ring C s) ∧
    TopClockUnfavourablePhase ring C s (topClockStopClasses ring C s) :=
  ⟨topStopMarkedPhase ring hn C s hl hbad, topStopSettledPhase ring hn C s hl hbad,
    topStopMobilePhase ring hn C s hl hbad, topStopPreparationPhase ring hn C s hl hbad,
    topStopRacePhase ring hn C s hl hbad, topStopFavourablePhase ring hn C s hl hbad,
    topStopUnfavourablePhase ring hn C s hl hbad⟩

end MarkedCells
end L3

#print axioms L3.MarkedCells.favourable_start
#print axioms L3.MarkedCells.topStopFavourablePhase
#print axioms L3.MarkedCells.topStopPhases

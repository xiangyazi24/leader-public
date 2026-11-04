import Leader.L3.Top.PinnedPhaseFillCost

/-!
# Q7 (P.12 preparation): the start and the exit of the fill stage

* A pending-only cut of the prepared classes starts the fill stage: its window holds only empty and
  pending registers (`pendingOnly_start`).
* A settled tail away from the border at the exit of the fill stage is a misplaced cut of the
  prepared classes (`exit_misplaced`); at the border it is an aligned window.

Consumer: `Leader/L3/TopPinnedPhaseFill.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The pure cohorts of a state that extends a permanent cut.

Consumer: `exit_misplaced`. -/
theorem pinned_cohorts {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Y0 Y : TopFixedTraceState n) (hcut : topFreshTailPermanentCut ring C s Y0)
    (hY : MarkedFrom ring C Y0 Y) : topClockConcretePureCohorts s Y := by
  obtain ⟨hreach0, _, anchor, hanchor, htime, hfuture⟩ := hcut
  obtain ⟨w, hw⟩ := hY
  refine ⟨anchor, ?_, ?_⟩
  · rw [hw, topFixedTraceRunAppendWord ring C Y0.2 w, ← hreach0]
    exact topClockTailAnchorWord ring C s anchor w Y0 hanchor
  · rw [hw]
    exact hfuture w

/-- **A settled tail away from the border at the exit of the fill stage is a misplaced cut of the
prepared classes.**

Consumer: `topPrepFill` (the preparation phase). -/
theorem exit_misplaced {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Y0 W : TopFixedTraceState n)
    (hP : PuPinAt ring C s Y0 W) (h : Nat) (hh : ExitShape (topClockSpan n) (cellOf s W) h)
    (hh1 : 1 ≤ h) : (topClockPrepClasses ring C s).misplacedTail W := by
  have hr3 := span_ge_three hg.hn
  have hcut := hP.1
  obtain ⟨hcut0, hgen, anchor, hanchor, htime, hfuture⟩ := hcut
  obtain ⟨hfrom, hold, hl, ha⟩ := hP.2
  have hreach : topClockReached ring C W := markedFrom_reached ring C Y0 W hfrom
  have hcoh := pinned_cohorts ring C s Y0 W hP.1 hfrom
  have hsuf := suffix_of_pinned ring C s hg Y0 W hP.1 hfrom hold
  have hpure : topClockConcretePureStream s W anchor := by
    obtain ⟨w, hw⟩ := hfrom
    rw [hw]; exact hfuture w
  obtain ⟨hh2, hleft, htail, hright⟩ := hh
  have hmis := misplaced_of_labelled s W anchor hpure (by rw [htime]; exact hl)
    (by rw [htime]; exact ha) ⟨h, by omega⟩ hh1 hh2
    (fun j hj => by
      rcases (hleft j hj).2 with h' | h' | h' <;> simp [h'])
    (by rw [htail])
    (fun j hj1 hj2 => by rw [hright j hj1 hj2])
  exact ⟨⟨Y0, hP.1, hfrom, hold, hl, ha⟩, ⟨Y0, hP.1, hfrom⟩, hreach, hcoh, hsuf, ⟨h, by omega⟩,
    hmis.1⟩

/-- **The start of the fill stage**: a pending-only cut of the prepared classes is a pinned labelled
state whose window holds only empty and pending registers.

Consumer: `topPrepFill` (the preparation phase). -/
theorem pendingOnly_start {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Z : TopFixedTraceState n)
    (h : (topClockPrepClasses ring C s).pendingOnly Z) :
    ∃ Y0, PuPinAt ring C s Y0 Z ∧ FillShape (topClockSpan n) (cellOf s Z) := by
  have hr3 := span_ge_three hg.hn
  obtain ⟨⟨Y0, hcut, hfrom, hold⟩, hdown, hreach, hcoh, hsuf, htarget⟩ := h
  have hnone := pinned_hnone ring C s Y0 Z hcut hfrom
  have hcells : ∀ j, j < topClockSpan n → (cellOf s Z j).c = .off ∧
      ((cellOf s Z j).i = .e ∨ (cellOf s Z j).i = .pt ∨ (cellOf s Z j).i = .pn) := by
    intro j hj
    obtain ⟨hin, hcar⟩ := htarget ⟨j, hj⟩
    refine ⟨?_, ?_⟩
    · unfold cellOf siteCell
      exact (absCar_off _ _).2 hcar
    · unfold cellOf siteCell
      rcases hq : (Z.1.1 (certSite s (topClockSpan n + j))).qIn with _ | _ | ⟨v, t⟩ | ⟨v, t⟩ <;>
        rw [hq] at hin <;> (try cases t) <;> simp [InTok.isE, InTok.isP, winSite, absIn, hq] at hin ⊢
  have hfree : puFree (topClockSpan n) (cellOf s Z) := by
    intro j hj
    refine ⟨(hcells j hj).1, ?_⟩
    rcases (hcells j hj).2 with h' | h' | h' <;> rw [h'] <;> decide
  have hnoS : ∀ j, j < topClockSpan n → (cellOf s Z j).i.isS = false := by
    intro j hj
    rcases (hcells j hj).2 with h' | h' | h' <;> rw [h'] <;> rfl
  refine ⟨Y0, ⟨hcut, hfrom, hold, ?_, ?_⟩, ⟨0, by omega, ?_, ?_⟩⟩
  · exact pulinv_of_noS ring C s hg Y0.1.2.clock Z hreach hnone hfree hnoS
  · exact pulinv_all_of_noS s Z Y0.1.2.clock hold hnoS
  · intro j hj
    simpa using hcells j (by omega)
  · intro j hj1 hj2
    omega

end MarkedCells
end L3

#print axioms L3.MarkedCells.exit_misplaced
#print axioms L3.MarkedCells.pendingOnly_start

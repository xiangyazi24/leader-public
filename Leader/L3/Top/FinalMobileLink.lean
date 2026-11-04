import Leader.L3.Top.FinalMobileCells
import Leader.L3.Top.MarkedDebtRows

/-!
# Q7: the clearing potential of the final mobile phase on the physical window

The window cells `cellOf s Y` of a fixed-trace state carry the physical content of the
settled-empty cut: no register holds a settled input (`NoS`), and every pending input stands
strictly left of every front and every live carry (`Bar`).  The potential is the number of
fronts and live carries, `clearPot`.  On such states no edge raises it, and the edge of an
obstacle register lowers it (`clearPot_drop`).  At potential zero the target window has the
pending-only shape (`shape_of_clear`).

Consumer: `Leader/L3/TopFinalMobilePhase.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- A register is an obstacle exactly when it holds a front or a live carry.

Consumer: `bar_of_barrier`, `shape_of_clear`. -/
theorem siteCell_obx {n : Nat} (Z : TopFixedTraceState n) (v : Fin n) :
    obx (siteCell Z v) = true ↔ ((Z.1.1 v).qIn = .X ∨ (Z.1.1 v).qCarry.isL = true) := by
  have hc := siteCell_carry_on Z v
  have hx : (siteCell Z v).i = .x ↔ (Z.1.1 v).qIn = .X := by
    rcases h : (Z.1.1 v).qIn with _ | _ | ⟨a, t⟩ | ⟨a, t⟩ <;> (try cases t) <;>
      simp [siteCell, absIn, h]
  unfold obx
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  rw [hx, hc]

/-- The number of fronts and live carries of the target window.

Consumer: `topClockFinalMobilePhase_of_genealogy`. -/
def clearPot {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) : Nat :=
  obCount (cellOf s Y) (topClockSpan n)

/-- The clearing invariant of the window: no settled input, pending inputs left of every
obstacle.

Consumer: `topClockFinalMobilePhase_of_genealogy`. -/
def ClearGood {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) : Prop :=
  NoS (topClockSpan n) (cellOf s Y) ∧ Bar (topClockSpan n) (cellOf s Y)

/-- A settled-empty target window has no settled cell.

Consumer: `clearGood_of_cut`. -/
theorem noS_of_settledEmpty {n : Nat} (s : Fin n) (Y : TopFixedTraceState n)
    (h : topClockTargetSettledEmpty s Y) : NoS (topClockSpan n) (cellOf s Y) := by
  intro j hj
  unfold cellOf
  rw [isS_link]
  exact h ⟨j, hj⟩

/-- The moving barrier of the cut is the cell barrier.

Consumer: `clearGood_of_cut`. -/
theorem bar_of_barrier {n : Nat} (s : Fin n) (Y : TopFixedTraceState n)
    (h : topClockConcreteMovingBarrier s Y) : Bar (topClockSpan n) (cellOf s Y) := by
  intro i j hi hj hP hob
  have hP' : (topClockConcreteInputAt s Y ⟨i, hi⟩).isP = true := by
    unfold topClockConcreteInputAt
    have := siteCell_isP Y (winSite s i)
    unfold cellOf at hP
    rw [this] at hP
    exact hP
  have hob' : (Y.1.1 (winSite s j)).qIn = .X ∨ (Y.1.1 (winSite s j)).qCarry.isL = true :=
    (siteCell_obx Y (winSite s j)).1 hob
  have := h ⟨i, hi⟩ ⟨j, hj⟩ hP'
    (by
      rcases hob' with h1 | h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1))
  exact this

/-- **The clearing invariant holds at the settled-empty cut.**

Consumer: `topClockFinalMobilePhase_of_genealogy`. -/
theorem clearGood_of_cut {n : Nat} (s : Fin n) (Y : TopFixedTraceState n)
    (hS : topClockTargetSettledEmpty s Y) (hB : topClockConcreteMovingBarrier s Y) :
    ClearGood s Y :=
  ⟨noS_of_settledEmpty s Y hS, bar_of_barrier s Y hB⟩

/-- Pointwise equal registers have equal counts.

Consumer: `clearPot_next`. -/
theorem obCount_congr (c c' : Nat → Cell) :
    ∀ k, (∀ j, j < k → c j = c' j) → obCount c k = obCount c' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    simp only [obCount]
    rw [ih (fun j hj => h j (by omega)), h k (by omega)]

/-- **No edge raises the potential, and the clearing invariant persists**, while an
obstacle remains.

Consumer: `topClockFinalMobilePhase_of_genealogy`. -/
theorem clearGood_next {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Y : TopFixedTraceState n)
    (hreach : topClockReached ring C Y) (hY : ClearGood s Y) (hpos : 0 < clearPot s Y)
    (e : Fin n) :
    ClearGood s (topFixedTraceNext ring C Y e) ∧
      clearPot s (topFixedTraceNext ring C Y e) ≤ clearPot s Y := by
  have hr3 := span_ge_three hg.hn
  obtain ⟨cells', hstep, hagree⟩ := link_step ring C s Y hg hreach e
  have hobs := obCount_pos _ _ hpos
  obtain ⟨h1, h2, _⟩ := step_good _ (by omega) _ _ hY.1 hY.2 hobs hstep
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro j hj
    rw [hagree j hj]
    exact h1 j hj
  · intro i j hi hj hP hob
    rw [hagree i hi] at hP
    rw [hagree j hj] at hob
    exact h2 i j hi hj hP hob
  · unfold clearPot
    rw [obCount_congr (cellOf s (topFixedTraceNext ring C Y e)) cells' _
      (fun j hj => hagree j hj)]
    exact step_count _ (by omega) _ _ hY.1 hY.2 hobs hstep

/-- The nominated edge: the register of an obstacle.

Consumer: `topClockFinalMobilePhase_of_genealogy`. -/
noncomputable def clearEdge {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) : Fin n :=
  open Classical in
  if h : ∃ p, p < topClockSpan n ∧ obx (cellOf s Y p) = true then
    winSite s (Classical.choose h)
  else s

/-- **The nominated edge lowers the potential**, while an obstacle remains.

Consumer: `topClockFinalMobilePhase_of_genealogy`. -/
theorem clearPot_drop {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Y : TopFixedTraceState n)
    (hreach : topClockReached ring C Y) (hY : ClearGood s Y) (hpos : 0 < clearPot s Y) :
    clearPot s (topFixedTraceNext ring C Y (clearEdge s Y)) + 1 ≤ clearPot s Y := by
  classical
  have hr3 := span_ge_three hg.hn
  have hex : ∃ p, p < topClockSpan n ∧ obx (cellOf s Y p) = true := obCount_pos _ _ hpos
  have hsel : clearEdge s Y = winSite s (Classical.choose hex) := by
    unfold clearEdge
    rw [dif_pos hex]
  have hspec := Classical.choose_spec hex
  rw [hsel]
  have hagree := link_window ring C s Y hg hreach _ hspec.1
  have hdrop := edge_count_drop _ (by omega) (cellOf s Y) _ hspec.1 hY.1 hY.2 hspec.2
  unfold clearPot at *
  rw [obCount_congr _ _ _ hagree]
  omega

/-- The potential is at most the number of registers.

Consumer: `topClockFinalMobilePhase_of_genealogy`. -/
theorem clearPot_le {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) :
    clearPot s Y ≤ topClockSpan n :=
  obCount_le_self _ _

/-- **Potential zero is the pending-only shape.**

Consumer: `topClockFinalMobilePhase_of_genealogy`. -/
theorem shape_of_clear {n : Nat} (s : Fin n) (Y : TopFixedTraceState n)
    (hY : ClearGood s Y) (h0 : clearPot s Y = 0) : topClockTargetPendingOnly s Y := by
  intro j
  have hob := obCount_zero _ _ h0 j.val j.isLt
  have hobv : ¬ ((Y.1.1 (winSite s j.val)).qIn = .X ∨
      (Y.1.1 (winSite s j.val)).qCarry.isL = true) := by
    intro h
    have := (siteCell_obx Y (winSite s j.val)).2 h
    unfold cellOf at hob
    rw [hob] at this
    exact absurd this (by decide)
  have hS : (Y.1.1 (winSite s j.val)).qIn.isS = false := by
    have := hY.1 j.val j.isLt
    unfold cellOf at this
    rw [isS_link] at this
    exact this
  change (((Y.1.1 (winSite s j.val)).qIn.isE = true) ∨ ((Y.1.1 (winSite s j.val)).qIn.isP = true)) ∧
    (Y.1.1 (winSite s j.val)).qCarry = .OFF
  constructor
  · rcases hq : (Y.1.1 (winSite s j.val)).qIn with _ | _ | ⟨a, t⟩ | ⟨a, t⟩
    · left; rfl
    · exact absurd (Or.inl hq) hobv
    · right; rfl
    · rw [hq] at hS; exact absurd hS (by simp [InTok.isS])
  · rcases hq : (Y.1.1 (winSite s j.val)).qCarry with _ | ⟨c, e⟩
    · rfl
    · exact absurd (Or.inr (by rw [hq]; rfl)) hobv

end MarkedCells
end L3

#print axioms L3.MarkedCells.clearGood_of_cut
#print axioms L3.MarkedCells.clearGood_next
#print axioms L3.MarkedCells.clearPot_drop
#print axioms L3.MarkedCells.shape_of_clear

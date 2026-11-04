import Leader.L3.StageM.OldRank
import Leader.L3.Bank.RepairDigitPacketMomentRelease

/-!
# Stage M (R10c, Lemma e-max): the coloured ghost window over the lane, and the Stage M moment

section 5, items 1 and 4-5 (`inheritedColourLaneStep`, `inheritedWorkRankStepLe`,
`inheritedWorkRankProgress`) on the pure lane.

* `GhostOf R s G`: the flagged window `G` (`L3.StageMOldRank.OCell`) projects to the lane window
  `winOf R s` once the carry colour is forgotten (`fr`: inherited to fresh). In `G` a carry
  present at the Stage M entrance is `.inh`, a carry launched later at the border is `.fresh`
  (the Q7 `carries` row), and a pending packet present at the entrance carries the old flag.
* `ghostInit`: the entrance window (every live carry inherited, every pending packet old);
  `ghostInitOf`, `ghostInitInv`.
* `ghostOfStep` (**inheritedColourLaneStep**): every lane letter moves the ghost by the window
  move of the letter (`laneMove`: frame, window edge, port cleanup, port acceptance), and the
  projection follows the lane (`laneWin`). `ghostInvStep`: the fresh-carry invariants `Inv` of
  the ghost are kept (Q7 `inv_step`).
* `gnext`: the ghost lane chain (lane and ghost together); `ghostMoment`: from every ghost lane
  state, `E[z^τ] ≤ w^{orank R G}`, `w = N/(N-n)`, to inherited-work rank zero, with
  `orank R G ≤ R (4R+4)` (`orankLe`).
* `ghostStop`: at rank zero with `GhostOf` and `Inv`, the lane window satisfies the window
  invariants of the attempt class (`Inv`, `Barrier` of `winOf R s`) and no old pending packet is
  left.

Consumer: the Stage M assembly (`L3.StageMAssembly`, through `momentSimQ`).
-/

namespace L3.StageMGhostLane

set_option autoImplicit false

open L3.MarkedCells
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.PacketMomentRows
open L3.PacketMomentWindow
open L3.PacketMoment
open L3.DigitPacketRelease
open L3.StageMOldRank

/-! ### Forgetting the carry colour -/

/-- Forget the carry colour: an inherited carry becomes fresh. Consumer: `GhostOf`. -/
def fr (c : Cell) : Cell := { i := c.i, c := if c.c = .inh then .fresh else c.c }

/-- The Q7 window edge does not read the carry colour. Consumer: `frApply`. -/
theorem frPair (b t : Bool) (x y : Cell) :
    fr (pair b t x y).1 = (pair b t (fr x) (fr y)).1 ∧
      fr (pair b t x y).2 = (pair b t (fr x) (fr y)).2 := by
  rcases x with ⟨xi, xc⟩
  rcases y with ⟨yi, yc⟩
  cases b <;> cases t <;> cases xi <;> cases xc <;> cases yi <;> cases yc <;> decide

/-- The port cleanup does not read the carry colour. Consumer: `frApply`. -/
theorem frClean (c : Cell) : fr (portClean c) = portClean (fr c) := by
  rcases c with ⟨ci, cc⟩
  cases ci <;> cases cc <;> decide

/-- The port acceptance does not read the carry colour. Consumer: `frApply`. -/
theorem frAccept (t : Bool) (c : Cell) : fr (portAccept t c) = portAccept t (fr c) := by
  rcases c with ⟨ci, cc⟩
  cases t <;> cases ci <;> cases cc <;> decide

/-- Window moves commute with forgetting the colour. Consumer: `ghostOfStep`. -/
theorem frApply (r : Nat) (cells : Nat → Cell) (m : WMove) :
    (fun j => fr (wApply r cells m j)) = wApply r (fun j => fr (cells j)) m := by
  funext j
  cases m with
  | frame => rfl
  | edge p =>
      show fr (edgeStep r cells p j) = edgeStep r (fun j => fr (cells j)) p j
      unfold edgeStep
      by_cases h : p + 1 < r
      · rw [if_pos h, if_pos h]
        have hp := frPair (decide (p = 0)) false (cells p) (cells (p + 1))
        unfold setTwo
        by_cases h1 : j = p
        · rw [if_pos h1, if_pos h1]; exact hp.1
        · rw [if_neg h1, if_neg h1]
          by_cases h2 : j = p + 1
          · rw [if_pos h2, if_pos h2]; exact hp.2
          · rw [if_neg h2, if_neg h2]
      · rw [if_neg h, if_neg h]
        have hp := (frPair false true (cells (r - 1)) { i := .e, c := .off }).1
        unfold setOne
        by_cases h1 : j = r - 1
        · rw [if_pos h1, if_pos h1]; exact hp
        · rw [if_neg h1, if_neg h1]
  | clean =>
      show fr (setOne cells 0 (portClean (cells 0)) j) =
        setOne (fun j => fr (cells j)) 0 (portClean (fr (cells 0))) j
      unfold setOne
      by_cases h1 : j = 0
      · rw [if_pos h1, if_pos h1]; exact frClean _
      · rw [if_neg h1, if_neg h1]
  | accept t =>
      show fr (setOne cells 0 (portAccept t (cells 0)) j) =
        setOne (fun j => fr (cells j)) 0 (portAccept t (fr (cells 0))) j
      unfold setOne
      by_cases h1 : j = 0
      · rw [if_pos h1, if_pos h1]; exact frAccept _ _
      · rw [if_neg h1, if_neg h1]

/-! ### The ghost window over the lane -/

/-- **The ghost projects to the lane window.** Consumer: every step and the stop. -/
def GhostOf (R : Nat) (s : CohortLane) (G : Nat → OCell) : Prop :=
  ∀ j, fr (G j).cell = winOf R s j

/-- The ghost move of a lane letter. Consumer: `gnext`. -/
def gstep (R : Nat) (s : CohortLane) (G : Nat → OCell) : Option Nat → Nat → OCell
  | none => G
  | some k => oApply R G (laneMove R s k)

/-- **inheritedColourLaneStep.** Every lane letter moves the ghost by the window move of the
letter and keeps the projection. Consumer: the Stage M assembly. -/
theorem ghostOfStep (R : Nat) (s : CohortLane) (G : Nat → OCell) (h : GhostOf R s G)
    (o : Option Nat) : GhostOf R (cohortLaneStep R s o) (gstep R s G o) := by
  cases o with
  | none => exact h
  | some k =>
      intro j
      have e1 := laneWin R s k
      have e2 := frApply R (cellsOf G) (laneMove R s k)
      have e3 := ocellApply R G (laneMove R s k)
      have hw : (fun j => fr (cellsOf G j)) = winOf R s := funext fun j => h j
      calc fr (oApply R G (laneMove R s k) j).cell
          = fr (cellsOf (oApply R G (laneMove R s k)) j) := rfl
        _ = fr (wApply R (cellsOf G) (laneMove R s k) j) := by rw [e3]
        _ = wApply R (fun j => fr (cellsOf G j)) (laneMove R s k) j := congrFun e2 j
        _ = wApply R (winOf R s) (laneMove R s k) j := by rw [hw]
        _ = winOf R (cohortEdge R s k) j := by rw [e1]

/-- The fresh-carry invariants of the ghost are kept by every lane letter. Consumer: the Stage M
assembly. -/
theorem ghostInvStep (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (G : Nat → OCell)
    (h : Inv R (cellsOf G)) (o : Option Nat) : Inv R (cellsOf (gstep R s G o)) := by
  cases o with
  | none => exact h
  | some k =>
      show Inv R (cellsOf (oApply R G (laneMove R s k)))
      rw [ocellApply]
      exact inv_step R hR _ _ h (moveStep R _ _ (laneMoveOk R s k))

/-- **The entrance ghost**: every live carry inherited, every pending packet old. Consumer: the
Stage M assembly. -/
def ghostInit (R : Nat) (s : CohortLane) : Nat → OCell := fun j =>
  { i := cellIn (s.inp (R + j)), c := if s.live (R + j) then .inh else .off,
    o := (cellIn (s.inp (R + j))).isP }

/-- The entrance ghost projects to the lane window. Consumer: the Stage M assembly. -/
theorem ghostInitOf (R : Nat) (s : CohortLane) : GhostOf R s (ghostInit R s) := by
  intro j
  show fr { i := cellIn (s.inp (R + j)), c := if s.live (R + j) then .inh else .off } =
    liftC (s.inp (R + j)) (s.live (R + j))
  unfold fr liftC
  cases s.live (R + j) <;> rfl

/-- The entrance ghost has no fresh carry. Consumer: the Stage M assembly. -/
theorem ghostInitInv (R : Nat) (s : CohortLane) : Inv R (cellsOf (ghostInit R s)) := by
  have hno : ∀ j, (cellsOf (ghostInit R s) j).c ≠ .fresh := by
    intro j
    show (if s.live (R + j) then Car.inh else Car.off) ≠ .fresh
    cases s.live (R + j) <;> decide
  exact ⟨fun j _ hj => absurd hj (hno j), fun j _ _ _ hj => absurd hj (hno j)⟩

/-- At the entrance every pending packet of the window is old. Consumer: the start of the
post-entrance queue (`L3.StageMQueue`). -/
theorem ghostInitOld (R : Nat) (s : CohortLane) (j : Nat) :
    oP (ghostInit R s j) = (cellIn (s.inp (R + j))).isP := by
  show ((cellIn (s.inp (R + j))).isP && (cellIn (s.inp (R + j))).isP) = _
  cases (cellIn (s.inp (R + j))).isP <;> rfl

/-! ### The ghost lane chain and the Stage M moment -/

/-- **The ghost lane chain**: the lane and its ghost move together. Consumer: `ghostMoment`,
the Stage M assembly. -/
def gnext {n : Nat} (R : Nat) (edgeOf : Fin n → Option Nat)
    (z : CohortLane × (Nat → OCell)) (e : Fin n) : CohortLane × (Nat → OCell) :=
  (cohortLaneStep R z.1 (edgeOf e), gstep R z.1 z.2 (edgeOf e))

/-- A target edge is a window edge. Consumer: `ghostMoment`. -/
theorem laneMoveTarget (R : Nat) (s : CohortLane) (p : Nat) (hp : p < R) :
    laneMove R s (R + p) = .edge p := by
  unfold laneMove
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

/-- **The Stage M moment on the ghost lane chain.** From every ghost lane state the
inherited-work rank reaches zero with `E[z^τ] ≤ w^{orank R G}`, `w = N/(N-n)`, uniformly over the
source and the lane (no invariant). Consumer: the Stage M assembly. -/
theorem ghostMoment {n : Nat} (R : Nat) (hR : 2 ≤ R) (hn : 1 ≤ n) (N : Nat) (hN : n ≤ N)
    (site : Nat → Fin n) (edgeOf : Fin n → Option Nat)
    (hedge : ∀ k, k < 2 * R → edgeOf (site k) = some k) (z : CohortLane × (Nat → OCell)) :
    MomentBoundQ (gnext R edgeOf) (fun z => orank R z.2 = 0) N (N ^ orank R z.2)
      ((N - n) ^ orank R z.2) z := by
  have hex : ∀ z : CohortLane × (Nat → OCell), ∃ e : Fin n, ¬ orank R z.2 = 0 →
      orank R (gnext R edgeOf z e).2 + 1 ≤ orank R z.2 := by
    intro z
    by_cases h0 : orank R z.2 = 0
    · exact ⟨site 0, fun h => absurd h0 h⟩
    · obtain ⟨p, hp, hd⟩ := orankProgress R hR z.2 (by omega)
      refine ⟨site (R + p), fun _ => ?_⟩
      show orank R (gstep R z.1 z.2 (edgeOf (site (R + p)))) + 1 ≤ orank R z.2
      rw [hedge (R + p) (by omega)]
      show orank R (oApply R z.2 (laneMove R z.1 (R + p))) + 1 ≤ orank R z.2
      rw [laneMoveTarget R z.1 p hp]
      exact hd
  exact momentOfPotential (gnext R edgeOf) (fun z => orank R z.2 = 0) N (fun z => orank R z.2)
    (fun z => Classical.choose (hex z)) hn hN
    (fun z hz => Classical.choose_spec (hex z) hz)
    (fun z _ e => by
      show orank R (gstep R z.1 z.2 (edgeOf e)) ≤ orank R z.2
      cases edgeOf e with
      | none => exact Nat.le_refl _
      | some k => exact orankMoveLe R hR z.2 _ (laneMoveOk R z.1 k)) z

/-! ### The stop -/

/-- Inv depends only on the first `r` registers. Consumer: `ghostStop`. -/
theorem invCongr (r : Nat) (c c' : Nat → Cell) (h : ∀ j, j < r → c' j = c j) (hi : Inv r c) :
    Inv r c' := by
  refine ⟨fun j hj hf => ?_, fun j k hj hk hf hg => ?_⟩
  · rw [h j hj] at hf ⊢
    obtain ⟨h1, h2⟩ := hi.1 j hj hf
    refine ⟨h1, fun i hi' => ?_⟩
    rw [h i (by omega)]
    exact h2 i hi'
  · rw [h j hj] at hf
    rw [h k hk] at hg
    exact hi.2 j k hj hk hf hg

/-- Barrier depends only on the first `r` registers. Consumer: `ghostStop`. -/
theorem barrierCongr (r : Nat) (c c' : Nat → Cell) (h : ∀ j, j < r → c' j = c j)
    (hb : Barrier r c) : Barrier r c' := by
  intro i j hi hj hP hO
  rw [h i hi] at hP
  rw [h j hj] at hO
  exact hb i j hi hj hP hO

/-- **The stop of Stage M on the lane.** At inherited-work rank zero, with the projection and
the fresh-carry invariants, the lane window has the window invariants of the attempt class and no
old pending packet is left; the ghost equals the lane window on the target. Consumer: the Stage M
assembly (`WinAligned` at the stop). -/
theorem ghostStop (R : Nat) (s : CohortLane) (G : Nat → OCell) (hg : GhostOf R s G)
    (hi : Inv R (cellsOf G)) (h0 : orank R G = 0) :
    Inv R (winOf R s) ∧ Barrier R (winOf R s) ∧ (∀ j, j < R → oP (G j) = false) ∧
      (∀ j, j < R → winOf R s j = cellsOf G j) := by
  have hr : rank R (cellsOf G) = 0 := by have := rankLeOrank R G; omega
  have hgap := rank_zero_gap R (cellsOf G) hi hr
  have hbar := rank_zero_barrier R (cellsOf G) hr
  have heq : ∀ j, j < R → winOf R s j = cellsOf G j := by
    intro j hj
    rw [← hg j]
    have hne : (cellsOf G j).c ≠ .inh := by
      by_cases hc : (cellsOf G j).c = .off
      · rw [hc]; decide
      · rw [(hgap j hj hc).1]; decide
    show { i := (cellsOf G j).i, c := if (cellsOf G j).c = .inh then .fresh else (cellsOf G j).c } =
      cellsOf G j
    rw [if_neg hne]
  exact ⟨invCongr R _ _ heq hi, barrierCongr R _ _ heq hbar,
    fun j hj => orankZeroNoOld R G h0 j hj, heq⟩

end L3.StageMGhostLane

#print axioms L3.StageMGhostLane.ghostOfStep
#print axioms L3.StageMGhostLane.ghostInvStep
#print axioms L3.StageMGhostLane.ghostInitOf
#print axioms L3.StageMGhostLane.ghostInitInv
#print axioms L3.StageMGhostLane.ghostMoment
#print axioms L3.StageMGhostLane.ghostStop

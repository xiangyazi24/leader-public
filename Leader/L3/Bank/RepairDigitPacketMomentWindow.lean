import Leader.L3.Bank.RepairDigitPacketMomentRows
import Leader.L3.Top.SettledPotentialFront

/-!
# The e-packet lane is the Q7 window: one lane edge is one window move

The target half of the lane (sites `R, ..., 2R-1`) read as the Q7 window `winOf R s`
(`liftC`: live carries are fresh), the source half as the source block `srcLane s`.
Every lane edge `k` acts as one window move `laneMove R s k` (frame, window edge `k - R`,
port cleanup, port acceptance) and on the source block as `srcStepAt` (`laneWin`, `laneSrc`).

Then the pure Q7 lemmas apply move by move: the window invariants (`moveInv`), the
non-rising active charge (`moveCharge`), the lexicographic front potential (`movePot`,
`moveFront`), and, at zero front debt, the good steps of the supply measure (`moveGood`).
No statement here mentions the Top chain.
-/

namespace L3.PacketMomentWindow

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open L3.MarkedCells
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.PacketMomentRows

/-! ### The window of a lane -/

/-- The target half of the lane as a Q7 window. Consumer: `laneWin`. -/
def winOf (R : Nat) (s : CohortLane) : Nat → Cell :=
  fun j => liftC (s.inp (R + j)) (s.live (R + j))

/-- The source half of the lane as a Q7 source block. Consumer: `laneSrc`. -/
def srcLane (s : CohortLane) : Nat → Tok := fun j => tokOf (s.out j)

/-- A move of the window. Consumer: `laneWin`. -/
inductive WMove
  | frame
  | edge (p : Nat)
  | clean
  | accept (t : Bool)

/-- The window after a move. Consumer: `laneWin`. -/
def wApply (r : Nat) (cells : Nat → Cell) : WMove → Nat → Cell
  | .frame => cells
  | .edge p => edgeStep r cells p
  | .clean => setOne cells 0 (portClean (cells 0))
  | .accept t => setOne cells 0 (portAccept t (cells 0))

/-- The window register hit by a move. Consumer: `moveColour`. -/
def wIdx : WMove → Option Nat
  | .edge p => some p
  | _ => none

/-- A legal move. Consumer: `moveStep`. -/
def WMove.Ok (r : Nat) : WMove → Prop
  | .edge p => p < r
  | _ => True

/-- The colouring after a move. Consumer: `L3.PacketMomentU`. -/
def moveColour (r : Nat) (cells : Nat → Cell) (m : WMove) (d : Nat → Prop) : Nat → Prop :=
  colourGen r cells (wApply r cells m) d (wIdx m)

/-- The port move: accept a sampled token into an empty carry-free border, else clean up.
Consumer: `laneMove`. -/
def portMove (cells : Nat → Cell) (x : Tok) : WMove :=
  if x.isD && decide (cells 0 = { i := .e, c := .off }) then .accept (decide (x = .dt))
  else .clean

/-- The window move of lane edge `k`. Consumer: `laneWin`. -/
def laneMove (R : Nat) (s : CohortLane) (k : Nat) : WMove :=
  if k + 1 < R then .frame
  else if k + 1 = R then portMove (winOf R s) (srcLane s k)
  else if k < 2 * R then .edge (k - R)
  else .frame

/-- Lane moves are legal. Consumer: `L3.PacketMomentU`. -/
theorem laneMoveOk (R : Nat) (s : CohortLane) (k : Nat) : (laneMove R s k).Ok R := by
  unfold laneMove
  by_cases h1 : k + 1 < R
  · rw [if_pos h1]; trivial
  · rw [if_neg h1]
    by_cases h2 : k + 1 = R
    · rw [if_pos h2]; unfold portMove; split <;> trivial
    · rw [if_neg h2]
      by_cases h3 : k < 2 * R
      · rw [if_pos h3]; show k - R < R; omega
      · rw [if_neg h3]; trivial

/-- Unfolding a lane update. Consumer: `laneWin`, `laneSrc`. -/
theorem cohortUpd_apply {α : Type} (f : Nat → α) (a : Nat) (v : α) (j : Nat) :
    cohortUpd f a v j = if j = a then v else f j := rfl

/-- **One lane edge is one window move.** Consumer: `L3.PacketMomentU`. -/
theorem laneWin (R : Nat) (s : CohortLane) (k : Nat) :
    winOf R (cohortEdge R s k) = wApply R (winOf R s) (laneMove R s k) := by
  funext j
  unfold laneMove
  by_cases h1 : k + 1 < R
  · rw [if_pos h1]
    unfold cohortEdge
    rw [if_pos h1]
    rfl
  · rw [if_neg h1]
    by_cases h2 : k + 1 = R
    · rw [if_pos h2]
      unfold cohortEdge
      rw [if_neg h1, if_pos h2]
      have e0 : winOf R s 0 = liftC (s.inp (k + 1)) (s.live (k + 1)) := by
        unfold winOf; rw [Nat.add_zero, h2]
      have hl := (portLift (s.out k) (s.inp (k + 1)) (s.live (k + 1))).2
      show liftC (cohortUpd s.inp (k + 1) _ (R + j)) (cohortUpd s.live (k + 1) _ (R + j)) = _
      rw [cohortUpd_apply, cohortUpd_apply]
      unfold portMove
      rw [e0]
      have hsk : srcLane s k = tokOf (s.out k) := rfl
      rw [hsk]
      by_cases hj : j = 0
      · subst hj
        rw [if_pos (by omega), if_pos (by omega)]
        rw [← hl]
        split
        · show _ = setOne (winOf R s) 0 _ 0
          simp only [setOne, if_true]
          rw [e0]
        · show _ = setOne (winOf R s) 0 _ 0
          simp only [setOne, if_true]
          rw [e0]
      · rw [if_neg (by omega), if_neg (by omega)]
        split <;> (show _ = setOne (winOf R s) 0 _ j; simp only [setOne, if_neg hj]; rfl)
    · rw [if_neg h2]
      by_cases h3 : k < 2 * R
      · rw [if_pos h3]
        show winOf R (cohortEdge R s k) j = edgeStep R (winOf R s) (k - R) j
        have hkR : R ≤ k := by omega
        have e1 : winOf R s (k - R) = liftC (s.inp k) (s.live k) := by
          unfold winOf; rw [show R + (k - R) = k by omega]
        have e2 : winOf R s (k - R + 1) = liftC (s.inp (k + 1)) (s.live (k + 1)) := by
          unfold winOf; rw [show R + (k - R + 1) = k + 1 by omega]
        by_cases h4 : k + 1 < 2 * R
        · unfold edgeStep
          rw [if_pos (by omega)]
          have e3 : decide (k - R = 0) = decide (k = R) := by
            by_cases h : k = R
            · simp [h]
            · simp [h]; omega
          rw [e1, e2, e3, finLift]
          unfold cohortEdge
          rw [if_neg h1, if_neg h2, if_pos h4]
          show liftC (cohortUpd (cohortUpd s.inp k _) (k + 1) _ (R + j))
            (cohortUpd (cohortUpd s.live k _) (k + 1) _ (R + j)) = _
          simp only [cohortUpd_apply, setTwo]
          by_cases hj1 : j = k - R
          · rw [if_pos hj1, if_neg (by omega), if_pos (by omega), if_neg (by omega),
              if_pos (by omega)]
          · rw [if_neg hj1]
            by_cases hj2 : j = k - R + 1
            · rw [if_pos hj2, if_pos (by omega), if_pos (by omega)]
            · rw [if_neg hj2, if_neg (by omega), if_neg (by omega), if_neg (by omega),
                if_neg (by omega)]
              rfl
        · have h5 : k + 1 = 2 * R := by omega
          unfold edgeStep
          rw [if_neg (by omega)]
          have e4 : R - 1 = k - R := by omega
          rw [e4, e1, termLift]
          unfold cohortEdge
          rw [if_neg h1, if_neg h2, if_neg h4, if_pos h5]
          show liftC (cohortUpd s.inp k _ (R + j)) (cohortUpd s.live k _ (R + j)) = _
          simp only [cohortUpd_apply, setOne]
          by_cases hj1 : j = k - R
          · rw [if_pos hj1, if_pos (by omega), if_pos (by omega)]
          · rw [if_neg hj1, if_neg (by omega), if_neg (by omega)]
            rfl
      · rw [if_neg h3]
        unfold cohortEdge
        rw [if_neg h1, if_neg h2, if_neg (by omega), if_neg (by omega)]
        rfl

/-- **One lane edge on the source block.** Consumer: `L3.PacketMomentU`. -/
theorem laneSrc (R : Nat) (s : CohortLane) (k : Nat) :
    srcLane (cohortEdge R s k) =
      if k < R then srcStepAt R (decide (winOf R s 0 = { i := .e, c := .off })) (srcLane s) k
      else srcLane s := by
  funext j
  by_cases h1 : k + 1 < R
  · rw [if_pos (by omega)]
    unfold srcStepAt
    rw [if_pos h1]
    have hp := pipeLift (decide (k = 0)) (s.out k) (s.out (k + 1))
    unfold cohortEdge
    rw [if_pos h1]
    show tokOf (cohortUpd (cohortUpd s.out k _) (k + 1) _ j) = _
    simp only [cohortUpd_apply, srcSetTwo]
    have ea : srcLane s k = tokOf (s.out k) := rfl
    have eb : srcLane s (k + 1) = tokOf (s.out (k + 1)) := rfl
    rw [ea, eb, hp]
    by_cases hj1 : j = k
    · subst hj1; simp
    · by_cases hj2 : j = k + 1
      · subst hj2; simp
      · simp [hj1, hj2, srcLane]
  · by_cases h2 : k + 1 = R
    · rw [if_pos (by omega)]
      unfold srcStepAt
      rw [if_neg h1]
      have e0 : winOf R s 0 = liftC (s.inp (k + 1)) (s.live (k + 1)) := by
        unfold winOf; rw [Nat.add_zero, h2]
      rw [e0]
      have hl := (portLift (s.out k) (s.inp (k + 1)) (s.live (k + 1))).1
      unfold cohortEdge
      rw [if_neg h1, if_pos h2]
      show tokOf (cohortUpd s.out k _ j) = _
      simp only [cohortUpd_apply, srcSetOne]
      have ea : srcLane s k = tokOf (s.out k) := rfl
      rw [ea, hl]
      by_cases hj : j = k
      · subst hj; simp
      · simp [hj, srcLane]
    · rw [if_neg (by omega)]
      unfold cohortEdge
      rw [if_neg h1, if_neg h2]
      by_cases h3 : k + 1 < 2 * R
      · rw [if_pos h3]; rfl
      · rw [if_neg h3]
        by_cases h4 : k + 1 = 2 * R
        · rw [if_pos h4]; rfl
        · rw [if_neg h4]

/-- An acceptance happens on the port edge, with a sampled token at the source terminal and an
empty carry-free border. Consumer: `L3.PacketMomentU`. -/
theorem laneAccept (R : Nat) (s : CohortLane) (k : Nat) (t : Bool)
    (h : laneMove R s k = .accept t) :
    k + 1 = R ∧ (srcLane s k).isD = true ∧ winOf R s 0 = { i := .e, c := .off } := by
  unfold laneMove at h
  by_cases h1 : k + 1 < R
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : k + 1 = R
    · rw [if_pos h2] at h
      unfold portMove at h
      by_cases hc : ((srcLane s k).isD && decide (winOf R s 0 = { i := .e, c := .off })) = true
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact ⟨h2, hc.1, hc.2⟩
      · rw [if_neg hc] at h; cases h
    · rw [if_neg h2] at h
      by_cases h3 : k < 2 * R
      · rw [if_pos h3] at h; cases h
      · rw [if_neg h3] at h; cases h

/-- A port move on the port edge is cleanup or acceptance; elsewhere the move is a frame or a
window edge. Consumer: `L3.PacketMomentU`. -/
theorem laneMovePort (R : Nat) (s : CohortLane) (k : Nat) (h : k + 1 = R) :
    laneMove R s k = portMove (winOf R s) (srcLane s k) := by
  unfold laneMove
  rw [if_neg (by omega), if_pos h]

/-- Off the port edge and the window, a lane edge is a frame. Consumer: `L3.PacketMomentU`. -/
theorem laneMoveInternal (R : Nat) (s : CohortLane) (k : Nat) (h : k + 1 < R) :
    laneMove R s k = .frame := by
  unfold laneMove; rw [if_pos h]

/-- Window edge `p` is lane edge `R + p`. Consumer: `L3.PacketMomentU`. -/
theorem laneMoveEdge (R : Nat) (s : CohortLane) (p : Nat) (hp : p < R) :
    laneMove R s (R + p) = .edge p := by
  unfold laneMove
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1; omega

/-! ### The pure Q7 lemmas, move by move -/

/-- A legal move is a window step. Consumer: `moveInv`. -/
theorem moveStep (r : Nat) (cells : Nat → Cell) (m : WMove) (hm : m.Ok r) :
    Step r cells (wApply r cells m) := by
  cases m with
  | frame => exact Step.frame
  | edge p => exact edgeStep_step r cells p hm
  | clean => exact Step.clean
  | accept t => exact Step.accept t

/-- The window invariants of the U phase. Consumer: `L3.PacketMomentU`. -/
structure WinInv (r : Nat) (cells : Nat → Cell) (d : Nat → Prop) : Prop where
  inv : Inv r cells
  ni : NoInh r cells
  bar : Barrier r cells
  cov : Cover r cells d
  lt : ∀ u, d u → u < r

/-- **The invariants are kept by every legal move.** Consumer: `L3.PacketMomentU`. -/
theorem moveInv (r : Nat) (hr : 2 ≤ r) (cells : Nat → Cell) (d : Nat → Prop) (m : WMove)
    (hm : m.Ok r) (h : WinInv r cells d) :
    WinInv r (wApply r cells m) (moveColour r cells m d) := by
  have hs := moveStep r cells m hm
  refine ⟨inv_step r hr _ _ h.inv hs, noInh_step r _ _ h.ni hs,
    barrier_step r hr _ _ h.bar h.ni hs, ?_, fun u hu => hu.1⟩
  cases m with
  | edge p => exact cover_edge_step r p hr hm cells d h.inv h.ni h.cov
  | frame => exact cover_port r hr _ _ d h.inv h.ni h.cov (Or.inl rfl)
  | clean => exact cover_port r hr _ _ d h.inv h.ni h.cov (Or.inr (Or.inl rfl))
  | accept t => exact cover_port r hr _ _ d h.inv h.ni h.cov (Or.inr (Or.inr ⟨t, rfl⟩))

/-- **The active charge does not rise** while a settled input stands in the window.
Consumer: `L3.PacketMomentU`. -/
theorem moveCharge (r : Nat) (hr : 2 ≤ r) (cells : Nat → Cell) (d : Nat → Prop) (m : WMove)
    (hm : m.Ok r) (h : WinInv r cells d) (hex : ∃ j, j < r ∧ (cells j).i.isS = true) :
    charge r (act r (wApply r cells m) (moveColour r cells m d)) ≤ charge r (act r cells d) := by
  unfold moveColour
  cases m with
  | frame =>
      refine act_same_case _ _ _ d none ?_ (fun k hk => hk) (fun m hm => hm)
      intro k hk
      exact ((act_iff _ _ d k).1 hk).2.1
  | edge p =>
      have hp : p < r := hm
      show charge r (act r (edgeStep r cells p) (colourGen r cells (edgeStep r cells p) d (some p)))
        ≤ _
      by_cases hp1 : p + 1 < r
      · unfold edgeStep; rw [if_pos hp1]
        exact edge_charge _ _ d p hp1 h.inv h.ni h.cov
      · unfold edgeStep; rw [if_neg hp1]
        have e : r - 1 = p := by omega
        rw [e]
        exact term_charge _ _ d p (by omega) (by omega) h.inv h.ni h.bar hex
  | clean => exact port_charge _ hr _ _ d h.inv h.ni (Or.inl rfl)
  | accept t => exact port_charge _ hr _ _ d h.inv h.ni (Or.inr ⟨t, rfl⟩)

/-- Port moves create no front. Consumer: `movePot`. -/
theorem portNoX (r : Nat) (cells : Nat → Cell) (m : WMove) (hm : ∀ p, m ≠ .edge p) :
    ∀ k, (wApply r cells m k).i = .x → (cells k).i = .x := by
  intro k hk
  cases m with
  | frame => exact hk
  | edge p => exact absurd rfl (hm p)
  | clean =>
      unfold wApply setOne at hk
      by_cases h1 : k = 0
      · subst h1
        simp only [if_true] at hk
        unfold portClean at hk
        by_cases hc : (cells 0).c = .off
        · simp [hc] at hk; exact hk
        · simp [hc] at hk
      · simp [h1] at hk; exact hk
  | accept t =>
      unfold wApply setOne at hk
      by_cases h1 : k = 0
      · subst h1
        simp only [if_true] at hk
        unfold portAccept at hk
        by_cases hc : cells 0 = { i := .e, c := .off }
        · rw [if_pos hc] at hk
          split at hk <;> simp at hk
        · rw [if_neg hc] at hk; exact hk
      · simp [h1] at hk; exact hk

/-- **The lexicographic front potential `A (3r+1) + M` does not rise.**
Consumer: `L3.PacketMomentU`. -/
theorem movePot (r : Nat) (hr : 2 ≤ r) (cells : Nat → Cell) (d : Nat → Prop) (m : WMove)
    (hm : m.Ok r) (h : WinInv r cells d) (hex : ∃ j, j < r ∧ (cells j).i.isS = true) :
    Pot r (wApply r cells m) (moveColour r cells m d) ≤ Pot r cells d := by
  have hch := moveCharge r hr cells d m hm h hex
  unfold Pot
  cases m with
  | edge p =>
      have hp : p < r := hm
      unfold moveColour at hch ⊢
      show charge r (act r (edgeStep r cells p)
          (colourGen r cells (edgeStep r cells p) d (some p))) * (3 * r + 1) +
        Mn r (edgeStep r cells p) (colourGen r cells (edgeStep r cells p) d (some p)) ≤ _
      change charge r (act r (edgeStep r cells p)
          (colourGen r cells (edgeStep r cells p) d (some p))) ≤ _ at hch
      by_cases hp1 : p + 1 < r
      · unfold edgeStep at hch ⊢; rw [if_pos hp1] at hch ⊢
        have hep := edge_pot _ _ d p hp1 h.inv h.ni
        refine pot_le_of _ _ _ _ _ (Mn_le _ _ _) ?_
        rcases hep with h1 | h1
        · exact Or.inl h1
        · exact Or.inr ⟨hch, h1⟩
      · unfold edgeStep at hch ⊢; rw [if_neg hp1] at hch ⊢
        have e : r - 1 = p := by omega
        rw [e] at hch ⊢
        have hep := term_pot _ _ d p (by omega) (by omega) h.inv h.ni h.bar hex
        refine pot_le_of _ _ _ _ _ (Mn_le _ _ _) ?_
        rcases hep with h1 | h1
        · exact Or.inl h1
        · exact Or.inr ⟨hch, h1⟩
  | frame =>
      exact pot_le_of _ _ _ _ _ (Mn_le _ _ _)
        (Or.inr ⟨hch, port_pot r cells _ d (portNoX r cells .frame (fun p h => by cases h))⟩)
  | clean =>
      exact pot_le_of _ _ _ _ _ (Mn_le _ _ _)
        (Or.inr ⟨hch, port_pot r cells _ d (portNoX r cells .clean (fun p h => by cases h))⟩)
  | accept t =>
      exact pot_le_of _ _ _ _ _ (Mn_le _ _ _)
        (Or.inr ⟨hch, port_pot r cells _ d (portNoX r cells (.accept t) (fun p h => by cases h))⟩)

/-- **A front edge lowers the front potential.** Consumer: `L3.PacketMomentU`. -/
theorem moveFront (r : Nat) (hr : 2 ≤ r) (cells : Nat → Cell) (d : Nat → Prop) (p : Nat)
    (hp : p < r) (h : WinInv r cells d) (hex : ∃ j, j < r ∧ (cells j).i.isS = true)
    (hxx : (cells p).i = .x) :
    Pot r (wApply r cells (.edge p)) (moveColour r cells (.edge p) d) + 1 ≤ Pot r cells d := by
  have hch := moveCharge r hr cells d (.edge p) hp h hex
  unfold Pot
  unfold moveColour at hch ⊢
  show charge r (act r (edgeStep r cells p)
      (colourGen r cells (edgeStep r cells p) d (some p))) * (3 * r + 1) +
    Mn r (edgeStep r cells p) (colourGen r cells (edgeStep r cells p) d (some p)) + 1 ≤ _
  change charge r (act r (edgeStep r cells p)
      (colourGen r cells (edgeStep r cells p) d (some p))) ≤ _ at hch
  by_cases hp1 : p + 1 < r
  · unfold edgeStep at hch ⊢; rw [if_pos hp1] at hch ⊢
    have hep := front_edge_pot _ _ d p hp1 h.inv h.ni hxx
    refine pot_lt_of _ _ _ _ _ (Mn_le _ _ _) ?_
    rcases hep with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hch, h1⟩
  · unfold edgeStep at hch ⊢; rw [if_neg hp1] at hch ⊢
    have e : r - 1 = p := by omega
    rw [e] at hch ⊢
    have hep := front_term_pot _ _ d p (by omega) h.inv h.ni hxx
    exact pot_lt_of _ _ _ _ _ (Mn_le _ _ _) (Or.inr ⟨hch, hep⟩)

end L3.PacketMomentWindow

#print axioms L3.PacketMomentWindow.laneWin
#print axioms L3.PacketMomentWindow.laneSrc
#print axioms L3.PacketMomentWindow.laneAccept
#print axioms L3.PacketMomentWindow.moveInv
#print axioms L3.PacketMomentWindow.moveCharge
#print axioms L3.PacketMomentWindow.movePot
#print axioms L3.PacketMomentWindow.moveFront

import Leader.L3.Bank.RepairDigitPacketMomentWindow

/-!
# The Q7 supply potential on the e-packet lane

At zero front debt the window satisfies the Q7 front-free environment `FEnv`, and the Q7
supply potential `Th = Gv + dist` (window measure plus source distance, the distance dropped
while a carry consumes) is read on the lane as `thL`.

* `moveGood`: a window move at zero front debt lowers the active charge or is a good step
  (measure not raised, a consuming carry keeps consuming) and keeps the debt zero;
* `laneDist`: a lane edge does not raise the source distance, except an acceptance of the
  sampled token standing at the source terminal;
* `laneTh`: every lane edge lowers the charge or keeps the debt zero without raising `thL`;
* `laneThStrict`: some lane edge lowers the charge or lowers `thL` strictly (Q7
  `nominate_pure`, `dist_step_drop`, `gv_accept`).
-/

namespace L3.PacketMomentSupply

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open Classical
open L3.MarkedCells
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.PacketMomentRows
open L3.PacketMomentWindow

/-- The supply potential of a lane: the window measure plus the source distance unless a
carry consumes (Q7 `Th`). Consumer: `L3.PacketMomentU.uStage`. -/
noncomputable def thL (R : Nat) (s : CohortLane) : Nat :=
  Gv R (winOf R s) + (if ConsAt R (winOf R s) then 0 else dist R (srcLane s))

/-- The supply potential is at most `2R^2 + R + 2`. Consumer: `L3.PacketMomentU`. -/
theorem thL_le (R : Nat) (hR : 1 ≤ R) (s : CohortLane) : thL R s ≤ 2 * (R * R) + R + 2 := by
  have h1 := Gv_tight R (winOf R s) hR
  have h2 := dist_le R (srcLane s)
  unfold thL
  split <;> omega

/-- The front-free environment at zero front debt. Consumer: `moveGood`, `laneThStrict`. -/
theorem fenvOf (r : Nat) (cells : Nat → Cell) (d : Nat → Prop) (h : WinInv r cells d)
    (hex : ∃ j, j < r ∧ (cells j).i.isS = true) (hM : Mn r cells d = 0) : FEnv r cells :=
  { inv := h.inv, ni := h.ni, bar := h.bar, ex := hex, nx := (mn_zero_facts _ _ _ hM).1 }

/-- **A move at zero front debt.** Consumer: `laneTh`. -/
theorem moveGood (r : Nat) (hr : 3 ≤ r) (cells : Nat → Cell) (d : Nat → Prop) (m : WMove)
    (hm : m.Ok r) (h : WinInv r cells d) (hex : ∃ j, j < r ∧ (cells j).i.isS = true)
    (hM : Mn r cells d = 0) :
    charge r (act r (wApply r cells m) (moveColour r cells m d)) < charge r (act r cells d) ∨
    (Mn r (wApply r cells m) (moveColour r cells m d) = 0 ∧
      GoodNext r cells (wApply r cells m)) := by
  have hch := moveCharge r (by omega) cells d m hm h hex
  have hpot := movePot r (by omega) cells d m hm h hex
  by_cases hlt : charge r (act r (wApply r cells m) (moveColour r cells m d)) <
      charge r (act r cells d)
  · exact Or.inl hlt
  right
  have heqA : charge r (act r (wApply r cells m) (moveColour r cells m d)) =
      charge r (act r cells d) := by omega
  have hM' : Mn r (wApply r cells m) (moveColour r cells m d) = 0 := by
    unfold Pot at hpot; rw [heqA] at hpot; omega
  refine ⟨hM', ?_⟩
  have hfe := fenvOf r cells d h hex hM
  obtain ⟨hnx', hd'⟩ := mn_zero_facts _ _ _ hM'
  obtain ⟨_, hd0⟩ := mn_zero_facts _ _ _ hM
  have hnlt : ¬ At r (wApply r cells m) < At r cells := by
    rw [← charge_eq_At r _ _ hd', ← charge_eq_At r cells d hd0]; exact hlt
  have hgp := good_port r cells hfe (by omega)
  cases m with
  | frame => exact (hgp true).1
  | clean => exact (hgp true).2.1
  | accept t => exact (hgp t).2.2
  | edge p =>
      have hp : p < r := hm
      by_cases hp1 : p + 1 < r
      · have he : wApply r cells (.edge p) = EdgeRes r p cells := by
          show edgeStep r cells p = _
          unfold edgeStep EdgeRes; rw [if_pos hp1]
        rw [he] at hnx' hnlt ⊢
        rcases edge_gv r p cells hfe hp1 hnx' with h1 | h1
        · exact absurd h1 hnlt
        · exact h1
      · have he : wApply r cells (.edge p) = TermRes r cells := by
          show edgeStep r cells p = _
          unfold edgeStep TermRes; rw [if_neg hp1]
        rw [he] at hnx' ⊢
        rcases term_gv r cells hfe (by omega) hnx' with h1 | ⟨h1, hnc⟩
        · rw [show TermRes r cells = cells from h1]; exact ⟨Nat.le_refl _, fun hh => hh⟩
        · have h1' : Gv r (TermRes r cells) + 1 = Gv r cells := h1
          exact ⟨by omega, fun hh => absurd hh hnc⟩

/-- **The source distance along a lane edge.** Consumer: `laneTh`. -/
theorem laneDist (R : Nat) (hR : 3 ≤ R) (s : CohortLane) (k : Nat) :
    dist R (srcLane (cohortEdge R s k)) ≤ dist R (srcLane s) ∨
    (dist R (srcLane s) = 0 ∧ ∃ t, laneMove R s k = .accept t) := by
  rw [laneSrc]
  by_cases hk : k < R
  · rw [if_pos hk]
    by_cases hd : dist R (srcLane s) = 0
    · rcases dist_zero_step R hR (srcLane s)
        (decide (winOf R s 0 = { i := .e, c := .off })) k hk hd with h1 | ⟨h1, h2⟩
      · left; omega
      · right
        refine ⟨hd, decide (srcLane s k = .dt), ?_⟩
        rw [laneMovePort R s k h1]
        unfold portMove
        have hD := (dist_zero_iff R (by omega) (srcLane s)).1 hd
        rw [show R - 1 = k by omega] at hD
        have hc : winOf R s 0 = { i := .e, c := .off } := of_decide_eq_true h2
        rw [if_pos (by simp [hD, hc])]
    · left; exact dist_step_le R hR _ _ (SrcStep.edge k hk _) hd
  · rw [if_neg hk]; left; exact Nat.le_refl _

/-- Acceptance into an empty carry-free border writes the pending packet.
Consumer: `laneTh`, `laneThStrict`. -/
theorem acceptCell (r : Nat) (cells : Nat → Cell) (t : Bool)
    (hc0 : cells 0 = { i := .e, c := .off }) :
    wApply r cells (.accept t) =
      setOne cells 0 { i := (if t = true then Inp.pt else Inp.pn), c := .off } := by
  show setOne cells 0 (portAccept t (cells 0)) = _
  unfold portAccept; rw [if_pos hc0]

/-- **One lane edge at zero front debt.** Either the active charge falls, or the debt stays
zero and the supply potential does not rise, strictly when the measure falls or the source
distance falls while nothing is consumed. Consumer: `laneThStrict`, `L3.PacketMomentU`. -/
theorem laneTh (R : Nat) (hR : 3 ≤ R) (s : CohortLane) (d : Nat → Prop) (k : Nat)
    (h : WinInv R (winOf R s) d) (hex : ∃ j, j < R ∧ (winOf R s j).i.isS = true)
    (hM : Mn R (winOf R s) d = 0) :
    charge R (act R (winOf R (cohortEdge R s k))
        (moveColour R (winOf R s) (laneMove R s k) d)) < charge R (act R (winOf R s) d) ∨
    (Mn R (winOf R (cohortEdge R s k)) (moveColour R (winOf R s) (laneMove R s k) d) = 0 ∧
      thL R (cohortEdge R s k) ≤ thL R s ∧
      ((Gv R (winOf R (cohortEdge R s k)) < Gv R (winOf R s) ∨
        (¬ ConsAt R (winOf R s) ∧
          dist R (srcLane (cohortEdge R s k)) < dist R (srcLane s))) →
        thL R (cohortEdge R s k) < thL R s)) := by
  have hfe := fenvOf R (winOf R s) d h hex hM
  rw [laneWin R s k]
  rcases moveGood R hR (winOf R s) d (laneMove R s k) (laneMoveOk R s k) h hex hM with
    h1 | ⟨hM', g⟩
  · exact Or.inl h1
  right
  refine ⟨hM', ?_⟩
  unfold thL
  rw [laneWin R s k]
  rcases laneDist R hR s k with hd | ⟨hd0, t, hacc⟩
  · exact ⟨th_le_good _ _ _ _ _ g hd, th_lt_good _ _ _ _ _ g hd⟩
  · obtain ⟨_, _, hc0⟩ := laneAccept R s k t hacc
    rw [hacc, acceptCell R (winOf R s) t hc0]
    have hp' : (if t = true then Inp.pt else Inp.pn).isP = true := by cases t <;> rfl
    have hg2 := gv_accept R (winOf R s) hfe (by omega) _ hp' hc0
    have hdl := dist_le R (srcLane (cohortEdge R s k))
    rw [hd0]
    by_cases hc : ConsAt R (winOf R s)
    · rw [if_pos (hg2.1.2 hc), if_pos hc, hg2.2.1 hc]
      refine ⟨Nat.le_refl _, fun hcond => ?_⟩
      rcases hcond with h1 | ⟨h1, _⟩
      · omega
      · exact absurd hc h1
    · have hc' : ¬ ConsAt R (setOne (winOf R s) 0
          { i := (if t = true then Inp.pt else Inp.pn), c := .off }) :=
        fun hh => hc (hg2.1.1 hh)
      rw [if_neg hc', if_neg hc]
      have := hg2.2.2 hc
      exact ⟨by omega, fun _ => by omega⟩

/-- A lane edge whose window result lowers the settled charge or the measure.
Consumer: `laneThStrict`. -/
theorem strictOfRes (R : Nat) (hR : 3 ≤ R) (s : CohortLane) (d : Nat → Prop) (k : Nat)
    (h : WinInv R (winOf R s) d) (hex : ∃ j, j < R ∧ (winOf R s j).i.isS = true)
    (hM : Mn R (winOf R s) d = 0) (Res : Nat → Cell)
    (hRes : winOf R (cohortEdge R s k) = Res)
    (hdrop : At R Res < At R (winOf R s) ∨ Gv R Res + 1 ≤ Gv R (winOf R s)) :
    charge R (act R (winOf R (cohortEdge R s k))
        (moveColour R (winOf R s) (laneMove R s k) d)) < charge R (act R (winOf R s) d) ∨
    (Mn R (winOf R (cohortEdge R s k)) (moveColour R (winOf R s) (laneMove R s k) d) = 0 ∧
      thL R (cohortEdge R s k) < thL R s) := by
  rcases laneTh R hR s d k h hex hM with h1 | ⟨hM', _, hc⟩
  · exact Or.inl h1
  · obtain ⟨_, hd'⟩ := mn_zero_facts _ _ _ hM'
    obtain ⟨_, hd0⟩ := mn_zero_facts _ _ _ hM
    rcases hdrop with hlt | hlt
    · left
      rw [charge_eq_At _ _ _ hd', charge_eq_At _ _ _ hd0, hRes]; exact hlt
    · right
      exact ⟨hM', hc (Or.inl (by rw [hRes]; omega))⟩

/-- **A strict drop at zero front debt.** Some lane edge lowers the active charge, or keeps
the debt zero and lowers the supply potential. Consumer: `L3.PacketMomentU`. -/
theorem laneThStrict (R : Nat) (hR : 3 ≤ R) (s : CohortLane) (d : Nat → Prop)
    (h : WinInv R (winOf R s) d) (hex : ∃ j, j < R ∧ (winOf R s j).i.isS = true)
    (hM : Mn R (winOf R s) d = 0) :
    ∃ k, k < 2 * R ∧
      (charge R (act R (winOf R (cohortEdge R s k))
          (moveColour R (winOf R s) (laneMove R s k) d)) < charge R (act R (winOf R s) d) ∨
      (Mn R (winOf R (cohortEdge R s k)) (moveColour R (winOf R s) (laneMove R s k) d) = 0 ∧
        thL R (cohortEdge R s k) < thL R s)) := by
  have hfe := fenvOf R (winOf R s) d h hex hM
  rcases nominate_pure R (winOf R s) hfe (by omega) with
    ⟨p, hp1, _, hdrop⟩ | ⟨_, hdrop⟩ | ⟨hc0, hnc⟩
  · refine ⟨R + p, by omega, strictOfRes R hR s d (R + p) h hex hM (EdgeRes R p (winOf R s)) ?_ hdrop⟩
    rw [laneWin, laneMoveEdge R s p (by omega)]
    show edgeStep R (winOf R s) p = _
    unfold edgeStep EdgeRes; rw [if_pos hp1]
  · refine ⟨R + (R - 1), by omega,
      strictOfRes R hR s d (R + (R - 1)) h hex hM (TermRes R (winOf R s)) ?_ (Or.inr hdrop)⟩
    rw [laneWin, laneMoveEdge R s (R - 1) (by omega)]
    show edgeStep R (winOf R s) (R - 1) = _
    unfold edgeStep TermRes; rw [if_neg (by omega)]
  · by_cases hd : dist R (srcLane s) = 0
    · have hD := (dist_zero_iff R (by omega) (srcLane s)).1 hd
      have hmv : laneMove R s (R - 1) = .accept (decide (srcLane s (R - 1) = .dt)) := by
        rw [laneMovePort R s (R - 1) (by omega)]
        unfold portMove
        rw [if_pos (by simp [hD, hc0])]
      refine ⟨R - 1, by omega, ?_⟩
      rcases laneTh R hR s d (R - 1) h hex hM with h1 | ⟨hM', _, hc⟩
      · exact Or.inl h1
      · right
        refine ⟨hM', hc (Or.inl ?_)⟩
        rw [laneWin, hmv, acceptCell R (winOf R s) _ hc0]
        have hp' : (if decide (srcLane s (R - 1) = .dt) = true then Inp.pt else Inp.pn).isP =
            true := by
          cases decide (srcLane s (R - 1) = .dt) <;> rfl
        have := (gv_accept R (winOf R s) hfe (by omega) _ hp' hc0).2.2 hnc
        omega
    · obtain ⟨hidx, hlt⟩ := dist_step_drop R hR (srcLane s)
        (decide (winOf R s 0 = { i := .e, c := .off })) hd
      refine ⟨srcIdx R (srcLane s), by omega, ?_⟩
      rcases laneTh R hR s d (srcIdx R (srcLane s)) h hex hM with h1 | ⟨hM', _, hc⟩
      · exact Or.inl h1
      · right
        refine ⟨hM', hc (Or.inr ⟨hnc, ?_⟩)⟩
        rw [laneSrc, if_pos hidx]
        omega

end L3.PacketMomentSupply

#print axioms L3.PacketMomentSupply.moveGood
#print axioms L3.PacketMomentSupply.laneDist
#print axioms L3.PacketMomentSupply.laneTh
#print axioms L3.PacketMomentSupply.laneThStrict

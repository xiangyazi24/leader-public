import Leader.L3.StageM.Queue
import Leader.L3.Width.PacketMomentQueue

/-!
# Stage M (R10c, Lemma e-max): the masked queue clause along the coupled chain

The fourth clause on the masked lane (`L3.StageMQueue`) along every coupled letter at a boundary
reference. `MaskQ x G χ` is `QueueLane` of the masked lane `maskL R (lane of x) G` with the lane
ghost atoms and the recorded delimiter exports of the audit of `x`. The four coupled rows are the
rows of `L3.WidthPacketMomentQueue` (`widthQueueFar`, `widthQueueTargetFin`,
`widthQueueTargetTerm`, `widthQueueExport`) with the lane rows replaced by the masked ones; the
real lane need not be in the packet-order class (inherited contents are arbitrary), the masked
lane is (`maskOrder`, from the ghost invariant `NewBar`).

`MaskInv` bundles the layout, the frame order, the ghost (`GhostOf`, `Inv` of the ghost window,
`NewBar`) and `MaskQ`; `maskInvStep` keeps it along every letter with the ghost moved by `gstep`.

Consumer: the Stage M assembly (the simulation of the coupled chain by the ghost lane chain
`gnext`, and the `PacketQueue` clause of `WidthLaneCutC` at the stop).
-/

namespace L3.StageMQueueCoupled

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open L3
open L3.MarkedCells
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.Correspondence
open L3.GhostBridge
open L3.WidthDigit
open L3.DigitPacketRelease
open L3.DigitPacketOrder
open L3.DigitPacketTransport
open L3.DigitPacketQueue
open L3.DigitPacketQueueStep
open L3.DigitPacketQueueRows
open L3.DigitPacketQueueExport
open L3.WidthWave
open L3.WidthPacketMoment
open L3.PacketMomentWindow
open L3.StageMOldRank
open L3.StageMGhostLane
open L3.StageMMasked
open L3.StageMQueue

variable {n : Nat}

/-- **The masked queue clause at a coupled state.** Consumer: every row below, `MaskInv`. -/
def MaskQ (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (root : Fin n)
    (lane : DigitLane) (src R : Nat) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (G : Nat → OCell) (χ : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) : Prop :=
  QueueLane R (maskL R (widthLaneOfState ref.toWidthDigitReference root lane src R x) G)
    (fun q => (laneCells ring root lane src x.2.current q).input)
    (DelExport ring root lane src R x.2) χ

/-- **The far letters** keep the masked clause with the same witness. Consumer:
`maskQueueStep`. -/
theorem maskQueueFar (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
    (hend : src + 2 * R < n) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (j : Nat) (hj : j < n)
    (hfar : j + 1 < src + R ∨ src + 2 * R ≤ j) (G : Nat → OCell)
    (χ : Nat → DigitExport _ n) (h : MaskQ ring ref root lane src R x G χ) :
    MaskQ ring ref root lane src R
      (widthDigitAuditNext ref.toWidthDigitReference x (digitSite ring root j))
      (gstep R (widthLaneOfState ref.toWidthDigitReference root lane src R x) G
        (cohortEdgeOf root src R (digitSite ring root j))) χ := by
  have hlane := (widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R
    hR hsrc hend x hx (digitSite ring root j)).2
  have hinp : ∀ q, R ≤ q → q < 2 * R →
      (maskL R (cohortLaneStep R (widthLaneOfState ref.toWidthDigitReference root lane src R x)
        (cohortEdgeOf root src R (digitSite ring root j)))
        (gstep R (widthLaneOfState ref.toWidthDigitReference root lane src R x) G
          (cohortEdgeOf root src R (digitSite ring root j)))).inp q =
      (maskL R (widthLaneOfState ref.toWidthDigitReference root lane src R x) G).inp q := by
    intro q _ _
    unfold cohortEdgeOf
    rw [cohortIdxSite ring root j hj]
    by_cases hin : src ≤ j ∧ j < src + 2 * R
    · rw [if_pos hin]
      show (maskL R (cohortEdge R (widthLaneOfState ref.toWidthDigitReference root lane src R x)
        (j - src)) (oApply R G (laneMove R (widthLaneOfState ref.toWidthDigitReference root lane
          src R x) (j - src)))).inp q = _
      rw [maskPipe R (j - src) _ G (by omega)]
    · rw [if_neg hin] <;> rfl
  have hA : ∀ q, R ≤ q → q < 2 * R →
      (laneCells ring root lane src (widthDigitAuditNext ref.toWidthDigitReference x
        (digitSite ring root j)).2.current q).input =
      (laneCells ring root lane src x.2.current q).input := by
    intro q hq1 hq2
    have h1 : digitSite ring root (src + q) ≠ digitSite ring root j :=
      siteNe ring root _ _ (by omega) hj (by omega)
    have h2 : digitSite ring root (src + q) ≠ ring.rightNeighbor (digitSite ring root j) := by
      rw [siteSucc]
      by_cases hjn : j + 1 < n
      · exact siteNe ring root _ _ (by omega) hjn (by omega)
      · have hj1 : j + 1 = n := by omega
        intro he
        have e1 := bankRepairDigitSiteVal ring root (src + q)
        have e2 := bankRepairDigitSiteVal ring root (j + 1)
        rw [he, e2, hj1, Nat.add_mod_right] at e1
        have hr := root.isLt
        rw [Nat.mod_eq_of_lt hr] at e1
        by_cases h3 : root.val + (src + q) < n
        · rw [Nat.mod_eq_of_lt h3] at e1; omega
        · rw [Nat.mod_eq_sub_mod (by omega),
            Nat.mod_eq_of_lt (show root.val + (src + q) - n < n by omega)] at e1; omega
    show (laneGhost lane ((digitAuditStep ring (piD (ref.phys x.1)) x.2
      (digitSite ring root j)).current (digitSite ring root (src + q)))).input =
      (laneGhost lane (x.2.current (digitSite ring root (src + q)))).input
    rw [curFar ring (piD (ref.phys x.1)) x.2 _ _ h1 h2]
  have hex : ∀ y, DelExport ring root lane src R (widthDigitAuditNext ref.toWidthDigitReference x
      (digitSite ring root j)).2 y ↔ DelExport ring root lane src R x.2 y := fun y =>
    delExportOff ring root lane src R (piD (ref.phys x.1)) x.2 (digitSite ring root j)
      (siteNe ring root _ _ hj (by omega) (by omega)) y
  unfold MaskQ
  rw [hlane]
  exact queueMaskFrame R _ _ G _ hinp _ _ hA _ _ hex χ h

/-- **The Fin rows on the coupled chain**, masked. Consumer: `maskQueueStep`. -/
theorem maskQueueFin (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
    (hend : src + 2 * R < n) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (k : Nat) (hk1 : R ≤ k)
    (hk2 : k + 1 < 2 * R) (G : Nat → OCell)
    (hg : GhostOf R (widthLaneOfState ref.toWidthDigitReference root lane src R x) G)
    (hnb : NewBar R G) (χ : Nat → DigitExport _ n) (h : MaskQ ring ref root lane src R x G χ) :
    ∃ χ' : Nat → DigitExport _ n, MaskQ ring ref root lane src R
      (widthDigitAuditNext ref.toWidthDigitReference x (digitSite ring root (src + k)))
      (oApply R G (laneMove R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k))
      χ' := by
  have hl := (widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hR
    hsrc hend x hx (digitSite ring root (src + k))).2
  rw [cohortEdgeOfSite ring root src R hend k (by omega)] at hl
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hx
  obtain ⟨-, hroot, hbX, hbY⟩ := widthLeadEdge ref.toWidthDigitReference ref.singletonFixed hn
    root x.1 hL (digitSite ring root (src + k))
  have hbX' : (pairW (piD (ref.phys x.1) (digitSite ring root (src + k))).word
      (piD (ref.phys x.1) (digitSite ring root (src + k + 1))).word).1.beta =
      (piD (ref.phys x.1) (digitSite ring root (src + k))).word.beta := hbX
  have hbY' : (pairW (piD (ref.phys x.1) (digitSite ring root (src + k))).word
      (piD (ref.phys x.1) (digitSite ring root (src + k + 1))).word).2.beta =
      (piD (ref.phys x.1) (digitSite ring root (src + k + 1))).word.beta := hbY
  have hlx := bankRepairDigitSiteNonroot ring root (piD (ref.phys x.1)) hroot (src + k)
    (by omega) (by omega)
  have hly := bankRepairDigitSiteNonroot ring root (piD (ref.phys x.1)) hroot (src + k + 1)
    (by omega) (by omega)
  have hbx : (piD (ref.phys x.1) (digitSite ring root (src + k))).word.beta = decide (k = R) := by
    by_cases hkR : k = R
    · rw [decide_eq_true hkR, hkR]
      exact hbR
    · rw [decide_eq_false hkR]
      exact hbF k (by omega) (by omega) hkR
  have hmX : laneMarkerX lane (piD (ref.phys x.1) (digitSite ring root (src + k)))
      (piD (ref.phys x.1) (digitSite ring root (src + k + 1))) = decide (k = R) := by
    rw [laneMarkerXBeta lane _ _ hbX']
    exact hbx
  have hmy : laneMarkerY lane (piD (ref.phys x.1) (digitSite ring root (src + k)))
      (piD (ref.phys x.1) (digitSite ring root (src + k + 1))) = false := by
    rw [laneMarkerYBeta lane _ _ hbY']
    exact hbF (k + 1) (by omega) (by omega) (by omega)
  obtain ⟨hI, -, -⟩ := rowFinD lane (x.2.clock + 1) (digitSite ring root (src + k))
    (ring.rightNeighbor (digitSite ring root (src + k)))
    (piD (ref.phys x.1) (digitSite ring root (src + k)))
    (piD (ref.phys x.1) (digitSite ring root (src + k + 1)))
    (x.2.current (digitSite ring root (src + k)))
    (x.2.current (digitSite ring root (src + k + 1))) hlx hly hmy
  have key : ∃ χ' : Nat → DigitExport _ n, QueueLane R
      (maskL R (cohortEdge R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k)
        (oApply R G (laneMove R (widthLaneOfState ref.toWidthDigitReference root lane src R x)
          k)))
      (fun q => (laneCells ring root lane src (widthDigitAuditNext ref.toWidthDigitReference x
        (digitSite ring root (src + k))).2.current q).input)
      (DelExport ring root lane src R (widthDigitAuditNext ref.toWidthDigitReference x
        (digitSite ring root (src + k))).2) χ' := by
    refine queueMaskFin R k (widthLaneOfState ref.toWidthDigitReference root lane src R x) G hg
      hnb hk1 hk2 _ _ _ _ χ ?_ ?_ ?_ ?_ h
    · show (laneGhost lane ((digitAuditStep ring (piD (ref.phys x.1)) x.2
        (digitSite ring root (src + k))).current (digitSite ring root (src + k)))).input = _
      rw [curX, show widthLaneOfState ref.toWidthDigitReference root lane src R x =
        cohortProj ring root lane src R (piD (ref.phys x.1)) from rfl,
        projIn ring root lane src R _ k hk1 (by omega),
        projLive ring root lane src R _ k hk1 (by omega),
        projIn ring root lane src R _ (k + 1) (by omega) hk2,
        projLive ring root lane src R _ (k + 1) (by omega) hk2, ← hmX]
      exact congrArg Prod.fst hI
    · show (laneGhost lane ((digitAuditStep ring (piD (ref.phys x.1)) x.2
        (digitSite ring root (src + k))).current
          (ring.rightNeighbor (digitSite ring root (src + k))))).input = _
      rw [curY ring (by omega), show widthLaneOfState ref.toWidthDigitReference root lane src R x =
        cohortProj ring root lane src R (piD (ref.phys x.1)) from rfl,
        projIn ring root lane src R _ k hk1 (by omega),
        projLive ring root lane src R _ k hk1 (by omega),
        projIn ring root lane src R _ (k + 1) (by omega) hk2,
        projLive ring root lane src R _ (k + 1) (by omega) hk2, ← hmX]
      exact congrArg Prod.snd hI
    · intro q hq e1 e2
      show (laneGhost lane ((digitAuditStep ring (piD (ref.phys x.1)) x.2
        (digitSite ring root (src + k))).current (digitSite ring root (src + q)))).input =
        (laneGhost lane (x.2.current (digitSite ring root (src + q)))).input
      rw [curFar ring (piD (ref.phys x.1)) x.2 _ _
        (siteNe ring root _ _ (by omega) (by omega) (by omega))
        (siteNe ring root (src + q) (src + k + 1) (by omega) (by omega) (by omega))]
    · exact fun y => delExportOff ring root lane src R (piD (ref.phys x.1)) x.2
        (digitSite ring root (src + k)) (siteNe ring root _ _ (by omega) (by omega) (by omega)) y
  obtain ⟨χ', hq⟩ := key
  refine ⟨χ', ?_⟩
  unfold MaskQ
  rw [hl]
  exact hq

/-- **The terminal row on the coupled chain**, masked. Consumer: `maskQueueStep`. -/
theorem maskQueueTerm (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
    (hend : src + 2 * R < n) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (k : Nat)
    (hk : k + 1 = 2 * R) (G : Nat → OCell)
    (hg : GhostOf R (widthLaneOfState ref.toWidthDigitReference root lane src R x) G)
    (χ : Nat → DigitExport _ n) (h : MaskQ ring ref root lane src R x G χ) :
    ∃ χ' : Nat → DigitExport _ n, MaskQ ring ref root lane src R
      (widthDigitAuditNext ref.toWidthDigitReference x (digitSite ring root (src + k)))
      (oApply R G (laneMove R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k))
      χ' := by
  have hl := (widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hR
    hsrc hend x hx (digitSite ring root (src + k))).2
  rw [cohortEdgeOfSite ring root src R hend k (by omega)] at hl
  have key : ∃ χ' : Nat → DigitExport _ n, QueueLane R
      (maskL R (cohortEdge R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k)
        (oApply R G (laneMove R (widthLaneOfState ref.toWidthDigitReference root lane src R x)
          k)))
      (fun q => (laneCells ring root lane src (widthDigitAuditNext ref.toWidthDigitReference x
        (digitSite ring root (src + k))).2.current q).input)
      (DelExport ring root lane src R (widthDigitAuditNext ref.toWidthDigitReference x
        (digitSite ring root (src + k))).2) χ' := by
    refine queueMaskTerm R k hk (widthLaneOfState ref.toWidthDigitReference root lane src R x) G
      hg _ _ _ _ χ ?_ ?_ h
    · intro q hq
      show (laneGhost lane ((digitAuditStep ring (piD (ref.phys x.1)) x.2
        (digitSite ring root (src + k))).current (digitSite ring root (src + q)))).input =
        (laneGhost lane (x.2.current (digitSite ring root (src + q)))).input
      rw [curFar ring (piD (ref.phys x.1)) x.2 _ _
        (siteNe ring root _ _ (by omega) (by omega) (by omega))
        (siteNe ring root (src + q) (src + k + 1) (by omega) (by omega) (by omega))]
    · exact fun y => delExportOff ring root lane src R (piD (ref.phys x.1)) x.2
        (digitSite ring root (src + k)) (siteNe ring root _ _ (by omega) (by omega) (by omega)) y
  obtain ⟨χ', hq⟩ := key
  refine ⟨χ', ?_⟩
  unfold MaskQ
  rw [hl]
  exact hq

/-- **The export row on the coupled chain**, masked: an accepted export, stamped `clock + 1`,
becomes the leftmost masked pending packet. Consumer: `maskQueueStep`. -/
theorem maskQueueExport (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
    (hend : src + 2 * R < n) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (k : Nat) (hk : k + 1 = R)
    (hfo : AuditFrameOrder x.2) (G : Nat → OCell)
    (hg : GhostOf R (widthLaneOfState ref.toWidthDigitReference root lane src R x) G)
    (hnb : NewBar R G) (χ : Nat → DigitExport _ n) (h : MaskQ ring ref root lane src R x G χ) :
    ∃ χ' : Nat → DigitExport _ n, MaskQ ring ref root lane src R
      (widthDigitAuditNext ref.toWidthDigitReference x (digitSite ring root (src + k)))
      (oApply R G (laneMove R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k))
      χ' := by
  subst hk
  have hl := (widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src (k + 1)
    hR hsrc hend x hx (digitSite ring root (src + k))).2
  rw [cohortEdgeOfSite ring root src (k + 1) hend k (by omega)] at hl
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hx
  obtain ⟨-, hroot, hbX, hbY⟩ := widthLeadEdge ref.toWidthDigitReference ref.singletonFixed hn
    root x.1 hL (digitSite ring root (src + k))
  have hbX' : (pairW (piD (ref.phys x.1) (digitSite ring root (src + k))).word
      (piD (ref.phys x.1) (digitSite ring root (src + (k + 1)))).word).1.beta =
      (piD (ref.phys x.1) (digitSite ring root (src + k))).word.beta := hbX
  have hbY' : (pairW (piD (ref.phys x.1) (digitSite ring root (src + k))).word
      (piD (ref.phys x.1) (digitSite ring root (src + (k + 1)))).word).2.beta =
      (piD (ref.phys x.1) (digitSite ring root (src + (k + 1)))).word.beta := hbY
  have hlx := bankRepairDigitSiteNonroot ring root (piD (ref.phys x.1)) hroot (src + k)
    (by omega) (by omega)
  have hly := bankRepairDigitSiteNonroot ring root (piD (ref.phys x.1)) hroot (src + (k + 1))
    (by omega) (by omega)
  have hmx : laneMarkerX lane (piD (ref.phys x.1) (digitSite ring root (src + k)))
      (piD (ref.phys x.1) (digitSite ring root (src + (k + 1)))) = false := by
    rw [laneMarkerXBeta lane _ _ hbX']
    exact hbF k (by omega) (by omega) (by omega)
  have hmy : laneMarkerY lane (piD (ref.phys x.1) (digitSite ring root (src + k)))
      (piD (ref.phys x.1) (digitSite ring root (src + (k + 1)))) = true := by
    rw [laneMarkerYBeta lane _ _ hbY']
    exact hbR
  obtain ⟨hrow, -⟩ := rowDelD lane (x.2.clock + 1) (digitSite ring root (src + k))
    (ring.rightNeighbor (digitSite ring root (src + k)))
    (piD (ref.phys x.1) (digitSite ring root (src + k)))
    (piD (ref.phys x.1) (digitSite ring root (src + (k + 1))))
    (x.2.current (digitSite ring root (src + k)))
    (x.2.current (digitSite ring root (src + (k + 1)))) hlx hly hmx hmy
  have hexp := delExportedD lane (x.2.clock + 1) (digitSite ring root (src + k))
    (ring.rightNeighbor (digitSite ring root (src + k)))
    (piD (ref.phys x.1) (digitSite ring root (src + k)))
    (piD (ref.phys x.1) (digitSite ring root (src + (k + 1))))
    (x.2.current (digitSite ring root (src + k)))
    (x.2.current (digitSite ring root (src + (k + 1)))) hlx hly hmx hmy
  have pO := projOut ring root lane src (k + 1) (piD (ref.phys x.1)) k (by omega)
  have pI := projIn ring root lane src (k + 1) (piD (ref.phys x.1)) (k + 1) (Nat.le_refl _)
    (by omega)
  have pL := projLive ring root lane src (k + 1) (piD (ref.phys x.1)) (k + 1) (Nat.le_refl _)
    (by omega)
  rw [← pO, ← pI, ← pL] at hrow hexp
  have he : digitSite ring root (src + k) = digitSite ring root (src + (k + 1 - 1)) := by
    rw [Nat.add_sub_cancel]
  have key : ∃ χ' : Nat → DigitExport _ n, QueueLane (k + 1)
      (maskL (k + 1) (cohortEdge (k + 1) (cohortProj ring root lane src (k + 1)
          (piD (ref.phys x.1))) k)
        (oApply (k + 1) G (laneMove (k + 1) (cohortProj ring root lane src (k + 1)
          (piD (ref.phys x.1))) k)))
      (fun q => (laneCells ring root lane src (widthDigitAuditNext ref.toWidthDigitReference x
        (digitSite ring root (src + k))).2.current q).input)
      (DelExport ring root lane src (k + 1) (widthDigitAuditNext ref.toWidthDigitReference x
        (digitSite ring root (src + k))).2) χ' := by
    refine queueMaskDel (k + 1) k rfl (cohortProj ring root lane src (k + 1) (piD (ref.phys x.1)))
      G hg hnb _ _ _ _ χ (x.2.clock + 1) ?_ ?_ ?_ ?_ h
    · intro q hq1 hq2
      show (laneGhost lane ((digitAuditStep ring (piD (ref.phys x.1)) x.2
        (digitSite ring root (src + k))).current (digitSite ring root (src + q)))).input =
        (laneGhost lane (x.2.current (digitSite ring root (src + q)))).input
      rw [curFar ring (piD (ref.phys x.1)) x.2 _ _
        (siteNe ring root _ _ (by omega) (by omega) (by omega))
        (siteNe ring root (src + q) (src + k + 1) (by omega) (by omega) (by omega))]
    · intro y hy
      have := delExportClock ring root lane src (k + 1) x.2 hfo y hy
      omega
    · intro hd
      refine ⟨fun hl0 hp => ?_, fun y => ?_⟩
      · show (laneGhost lane ((digitAuditStep ring (piD (ref.phys x.1)) x.2
          (digitSite ring root (src + k))).current
            (ring.rightNeighbor (digitSite ring root (src + k))))).input =
          (laneGhost lane (x.2.current (digitSite ring root (src + (k + 1))))).input
        rw [curY ring (by omega)]
        exact (congrArg Prod.snd hrow).trans (delGhostKeep _ _ _ _ _ _
          (fun h' => absurd (hl0.symm.trans h') (by decide)) hd hp)
      · refine (delExportStep ring root lane src (k + 1) (piD (ref.phys x.1)) x.2 _ he y).trans ?_
        refine ⟨fun hy => hy.elim id (fun hN => ?_), Or.inl⟩
        have hexp' : (digitReceiptLane lane (svcAt ring (piD (ref.phys x.1)) x.2
            (digitSite ring root (src + k)))).exported.isSome =
            delAccept ((cohortProj ring root lane src (k + 1) (piD (ref.phys x.1))).out k)
              ((cohortProj ring root lane src (k + 1) (piD (ref.phys x.1))).inp (k + 1))
              ((cohortProj ring root lane src (k + 1) (piD (ref.phys x.1))).live (k + 1)) := hexp
        rw [hN.2.2.1, hd] at hexp'
        exact absurd hexp' (by simp)
    · intro hd
      obtain ⟨T, hD, hiy, hky'⟩ := delAcceptCases _ _ _ hd
      rw [pO] at hD
      rw [pI] at hiy
      rw [pL] at hky'
      obtain ⟨ex, e1, e2, e3, e4, e5, e6, -, e8⟩ := recordDeliveryD lane (x.2.clock + 1)
        (digitSite ring root (src + k)) (ring.rightNeighbor (digitSite ring root (src + k)))
        (piD (ref.phys x.1) (digitSite ring root (src + k)))
        (piD (ref.phys x.1) (digitSite ring root (src + (k + 1))))
        (x.2.current (digitSite ring root (src + k)))
        (x.2.current (digitSite ring root (src + (k + 1)))) hlx hly hmy hD hiy hky'
      have e1' : (digitReceiptLane lane (svcAt ring (piD (ref.phys x.1)) x.2
          (digitSite ring root (src + k)))).exported = some ex := e1
      refine ⟨ex, e3, ?_, fun y => ?_⟩
      · show (laneGhost lane ((digitAuditStep ring (piD (ref.phys x.1)) x.2
          (digitSite ring root (src + k))).current
            (ring.rightNeighbor (digitSite ring root (src + k))))).input = ex.operand
        rw [curY ring (by omega)]
        exact e8.trans e2.symm
      · refine (delExportStep ring root lane src (k + 1) (piD (ref.phys x.1)) x.2 _ he y).trans ?_
        refine or_congr Iff.rfl ⟨fun hN => Option.some.inj (hN.2.2.1.symm.trans e1'), ?_⟩
        intro hy
        rw [hy]
        exact ⟨e3, e5, e1', e4, e6⟩
  obtain ⟨χ', hq⟩ := key
  refine ⟨χ', ?_⟩
  unfold MaskQ
  rw [hl]
  exact hq

/-- **The step of the masked clause.** Every coupled letter, from a layout state with ordered
audit frames and the ghost invariants, carries `MaskQ` with the ghost moved by `gstep`.
Consumer: `maskInvStep`. -/
theorem maskQueueStep (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
    (hend : src + 2 * R < n) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (hfo : AuditFrameOrder x.2)
    (G : Nat → OCell)
    (hg : GhostOf R (widthLaneOfState ref.toWidthDigitReference root lane src R x) G)
    (hnb : NewBar R G) (χ : Nat → DigitExport _ n) (h : MaskQ ring ref root lane src R x G χ)
    (e : Fin n) :
    ∃ χ' : Nat → DigitExport _ n, MaskQ ring ref root lane src R
      (widthDigitAuditNext ref.toWidthDigitReference x e)
      (gstep R (widthLaneOfState ref.toWidthDigitReference root lane src R x) G
        (cohortEdgeOf root src R e)) χ' := by
  obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  by_cases hfar : j + 1 < src + R ∨ src + 2 * R ≤ j
  · exact ⟨χ, maskQueueFar ring ref hn root lane src R hR hsrc hend x hx j hj hfar G χ h⟩
  · obtain ⟨k, rfl⟩ : ∃ k, j = src + k := ⟨j - src, by omega⟩
    rw [cohortEdgeOfSite ring root src R hend k (by omega)]
    by_cases h1 : k + 1 = R
    · exact maskQueueExport ring ref hn root lane src R hR hsrc hend x hx k h1 hfo G hg hnb χ h
    · by_cases h2 : k + 1 = 2 * R
      · exact maskQueueTerm ring ref hn root lane src R hR hsrc hend x hx k h2 G hg χ h
      · exact maskQueueFin ring ref hn root lane src R hR hsrc hend x hx k (by omega)
          (by omega) G hg hnb χ h

/-- **The Stage M run invariant**: layout, ordered audit frames, the ghost of the lane with its
invariants, and the masked queue clause. Consumer: the Stage M assembly. -/
def MaskInv (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (root : Fin n)
    (lane : DigitLane) (src R : Nat) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (G : Nat → OCell) : Prop :=
  WidthCohortLayout ref.toWidthDigitReference root src R x.1 ∧ AuditFrameOrder x.2 ∧
    GhostOf R (widthLaneOfState ref.toWidthDigitReference root lane src R x) G ∧
    Inv R (cellsOf G) ∧ NewBar R G ∧ ∃ χ, MaskQ ring ref root lane src R x G χ

/-- **The run invariant along every coupled letter**, the ghost moved by `gstep`. Consumer: the
Stage M assembly. -/
theorem maskInvStep (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
    (hend : src + 2 * R < n) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (G : Nat → OCell) (h : MaskInv ring ref root lane src R x G) (e : Fin n) :
    MaskInv ring ref root lane src R (widthDigitAuditNext ref.toWidthDigitReference x e)
      (gstep R (widthLaneOfState ref.toWidthDigitReference root lane src R x) G
        (cohortEdgeOf root src R e)) := by
  obtain ⟨hx, hfo, hg, hi, hnb, χ, hq⟩ := h
  obtain ⟨h1, h2⟩ := widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R
    hR hsrc hend x hx e
  refine ⟨h1, auditFrameOrderStep ring (piD (ref.phys x.1)) x.2 e hfo, ?_,
    ghostInvStep R hR _ G hi _, ?_,
    maskQueueStep ring ref hn root lane src R hR hsrc hend x hx hfo G hg hnb χ hq e⟩
  · rw [h2]
    exact ghostOfStep R _ G hg _
  · cases cohortEdgeOf root src R e with
    | none => exact hnb
    | some k => exact newBarStep R G _ (laneMoveOk R _ k) hnb

/-- **Start**: at any layout state with ordered audit frames, the entrance ghost satisfies the run
invariant. Consumer: the Stage M assembly. -/
theorem maskInvInit (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (root : Fin n)
    (lane : DigitLane) (src R : Nat) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1)
    (hfo : AuditFrameOrder x.2) :
    MaskInv ring ref root lane src R x
      (ghostInit R (widthLaneOfState ref.toWidthDigitReference root lane src R x)) :=
  ⟨hx, hfo, ghostInitOf R _, ghostInitInv R _, newBarInit R _,
    fun _ => ⟨0, lane, root, root, none, ⟨0, compileAdvice_topA_pos _⟩, false⟩,
    queueMaskInit R _ _ _ _⟩

end L3.StageMQueueCoupled

#print axioms L3.StageMQueueCoupled.maskQueueFar
#print axioms L3.StageMQueueCoupled.maskQueueFin
#print axioms L3.StageMQueueCoupled.maskQueueTerm
#print axioms L3.StageMQueueCoupled.maskQueueExport
#print axioms L3.StageMQueueCoupled.maskQueueStep
#print axioms L3.StageMQueueCoupled.maskInvStep
#print axioms L3.StageMQueueCoupled.maskInvInit

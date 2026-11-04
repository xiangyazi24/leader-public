import Leader.L3.Bank.RepairDigitPacketQueueExport
import Leader.L3.Width.PacketMomentTransport
import Leader.L3.Width.DigitBoundary

/-!
# Lemma e-packet at a boundary reference: the reached-state queue invariant on the coupled chain

Generic form of the coupled rows of the reached-state invariant `PacketQueue` (repair.tex
1300-1326) at an arbitrary `WidthBoundaryReference`: `widthOrderCoupled`
(`L3.DigitPacketTransport.orderCoupled`), `widthQueueFar` (`L3.DigitPacketQueueStep.queueFar`),
`widthQueueTargetFin`, `widthQueueTargetTerm` (`L3.DigitPacketQueueRows`), `widthQueueExport`,
`widthQueueStep`, `widthPacketQueueStep` (`L3.DigitPacketQueueExport`). Mechanical port:
`BankReferenceState ring hbank` -> `ref.State`, `z.val.1` -> `ref.phys z`, `CohortLayout` ->
`WidthCohortLayout`, `laneOfState` -> `widthLaneOfState`, `laneStep` -> `widthLaneStep`,
`bankRepairDigitLeadBankEdge` -> `L3.WidthWave.widthLeadEdge` (with `ref.singletonFixed`); the lane
rows and the audit lemmas are used as they are. Consumer: the attempt class at a boundary
reference (`L3.WidthPacketMomentAttempt.widthAttemptInvStep`).
-/

namespace L3.WidthPacketMomentQueue

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open L3
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

variable {n : Nat}

/-- **The packet-order invariant along one coupled letter.** Consumer: `orderCoupledWord`. -/
theorem widthOrderCoupled (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n) (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R)
    (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1)
    (ho : PacketOrder R (widthLaneOfState ref.toWidthDigitReference root lane src R x)) (e : Fin n) :
    WidthCohortLayout ref.toWidthDigitReference root src R (widthDigitAuditNext (ref.toWidthDigitReference) x e).1 ∧
      PacketOrder R (widthLaneOfState ref.toWidthDigitReference root lane src R
        (widthDigitAuditNext (ref.toWidthDigitReference) x e)) := by
  obtain ⟨h1, h2⟩ := widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hR hsrc hend x hx e
  refine ⟨h1, ?_⟩
  rw [h2]
  obtain ⟨m, hm⟩ := ho
  cases cohortEdgeOf root src R e with
  | none => exact ⟨m, hm⟩
  | some k => exact orderStep R m k _ hR hm

/-- **The far edges.** On the coupled chain, a letter at offset `j` whose endpoints are both off
the target and which is not the delimiter edge preserves the clause with the same `χ`: source
motion inside the pair (`src ≤ j`, `j + 1 < src + R`), everything left of the pair, and everything
at or after the next delimiter. Consumer: `widthQueueStep` (the composed step of the clause). -/
theorem widthQueueFar (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (j : Nat) (hj : j < n)
    (hfar : j + 1 < src + R ∨ src + 2 * R ≤ j) (χ : Nat → DigitExport _ n)
    (h : QueueAt ring root lane src R (piD (ref.phys x.1)) x.2 χ) :
    QueueAt ring root lane src R
      (piD (ref.phys (widthDigitAuditNext (ref.toWidthDigitReference) x
        (digitSite ring root j)).1))
      (widthDigitAuditNext (ref.toWidthDigitReference) x (digitSite ring root j)).2 χ := by
  have hlane := (widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hR hsrc hend x hx (digitSite ring root j)).2
  -- the lane's target cells do not move
  have hinp : ∀ q, R ≤ q → q < 2 * R →
      (widthLaneOfState ref.toWidthDigitReference root lane src R
        (widthDigitAuditNext (ref.toWidthDigitReference) x
          (digitSite ring root j))).inp q = (widthLaneOfState ref.toWidthDigitReference root lane src R x).inp q := by
    intro q _ _
    rw [hlane]
    unfold cohortEdgeOf
    rw [cohortIdxSite ring root j hj]
    by_cases hin : src ≤ j ∧ j < src + 2 * R
    · rw [if_pos hin]
      show (cohortEdge R _ (j - src)).inp q = _
      rw [(edgePipe R (j - src) _ (by omega)).1]
    · rw [if_neg hin]
      rfl
  refine queueFrame ring root lane src R _ _ _ _ χ hinp ?_ ?_ h
  · intro q hq1 hq2
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
    show (laneGhost lane ((digitAuditStep ring (piD (ref.phys x.1)) x.2 (digitSite ring root j)).current
      (digitSite ring root (src + q)))).input = (laneGhost lane (x.2.current
      (digitSite ring root (src + q)))).input
    rw [curFar ring (piD (ref.phys x.1)) x.2 _ _ h1 h2]
  · intro y
    exact delExportOff ring root lane src R (piD (ref.phys x.1)) x.2 (digitSite ring root j)
      (siteNe ring root _ _ hj (by omega) (by omega)) y

/-- **The Fin rows on the coupled chain.** A letter at offset `src + k`, `R ≤ k`, `k + 1 < 2R`,
from a layout state in the packet-order class, carries the clause (with a shifted witness).
Consumer: `L3.DigitPacketQueueExport.queueStep`. -/
theorem widthQueueTargetFin (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (k : Nat) (hk1 : R ≤ k) (hk2 : k + 1 < 2 * R)
    (ho : PacketOrder R (widthLaneOfState ref.toWidthDigitReference root lane src R x)) (χ : Nat → DigitExport _ n)
    (h : QueueAt ring root lane src R (piD (ref.phys x.1)) x.2 χ) :
    ∃ χ' : Nat → DigitExport _ n, QueueAt ring root lane src R
      (piD (ref.phys (widthDigitAuditNext (ref.toWidthDigitReference) x
        (digitSite ring root (src + k))).1))
      (widthDigitAuditNext (ref.toWidthDigitReference) x
        (digitSite ring root (src + k))).2 χ' := by
  obtain ⟨m, hm⟩ := ho
  have hl := (widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hR hsrc hend x hx
    (digitSite ring root (src + k))).2
  rw [cohortEdgeOfSite ring root src R hend k (by omega)] at hl
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hx
  obtain ⟨-, hroot, hbX, hbY⟩ := widthLeadEdge ref.toWidthDigitReference ref.singletonFixed hn root x.1 hL
    (digitSite ring root (src + k))
  have hbX' : (pairW (piD (ref.phys x.1) (digitSite ring root (src + k))).word
      (piD (ref.phys x.1) (digitSite ring root (src + k + 1))).word).1.beta =
      (piD (ref.phys x.1) (digitSite ring root (src + k))).word.beta := hbX
  have hbY' : (pairW (piD (ref.phys x.1) (digitSite ring root (src + k))).word
      (piD (ref.phys x.1) (digitSite ring root (src + k + 1))).word).2.beta =
      (piD (ref.phys x.1) (digitSite ring root (src + k + 1))).word.beta := hbY
  have hlx := bankRepairDigitSiteNonroot ring root (piD (ref.phys x.1)) hroot (src + k) (by omega)
    (by omega)
  have hly := bankRepairDigitSiteNonroot ring root (piD (ref.phys x.1)) hroot (src + k + 1) (by omega)
    (by omega)
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
  rw [queueAtIff] at h
  refine (exists_congr fun χ' => queueAtIff ring root lane src R _ _ χ').2 ?_
  have hlane : cohortProj ring root lane src R
      (piD (ref.phys (widthDigitAuditNext (ref.toWidthDigitReference) x
        (digitSite ring root (src + k))).1)) =
      cohortEdge R (cohortProj ring root lane src R (piD (ref.phys x.1))) k := hl
  rw [hlane]
  refine queueLaneFin R k m _ hk1 hk2 hm _ _ _ _ χ ?_ ?_ ?_ ?_ h
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

/-- **The terminal row on the coupled chain.** A letter at offset `src + 2R - 1` carries the
clause with the same witness. Consumer: `L3.DigitPacketQueueExport.queueStep`. -/
theorem widthQueueTargetTerm (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (k : Nat) (hk : k + 1 = 2 * R)
    (χ : Nat → DigitExport _ n) (h : QueueAt ring root lane src R (piD (ref.phys x.1)) x.2 χ) :
    ∃ χ' : Nat → DigitExport _ n, QueueAt ring root lane src R
      (piD (ref.phys (widthDigitAuditNext (ref.toWidthDigitReference) x
        (digitSite ring root (src + k))).1))
      (widthDigitAuditNext (ref.toWidthDigitReference) x
        (digitSite ring root (src + k))).2 χ' := by
  have hl := (widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hR hsrc hend x hx
    (digitSite ring root (src + k))).2
  rw [cohortEdgeOfSite ring root src R hend k (by omega)] at hl
  rw [queueAtIff] at h
  refine (exists_congr fun χ' => queueAtIff ring root lane src R _ _ χ').2 ?_
  have hlane : cohortProj ring root lane src R
      (piD (ref.phys (widthDigitAuditNext (ref.toWidthDigitReference) x
        (digitSite ring root (src + k))).1)) =
      cohortEdge R (cohortProj ring root lane src R (piD (ref.phys x.1))) k := hl
  rw [hlane]
  refine queueLaneTerm R k hk _ _ _ _ _ χ ?_ ?_ h
  · intro q hq
    show (laneGhost lane ((digitAuditStep ring (piD (ref.phys x.1)) x.2
      (digitSite ring root (src + k))).current (digitSite ring root (src + q)))).input =
      (laneGhost lane (x.2.current (digitSite ring root (src + q)))).input
    rw [curFar ring (piD (ref.phys x.1)) x.2 _ _
      (siteNe ring root _ _ (by omega) (by omega) (by omega))
      (siteNe ring root (src + q) (src + k + 1) (by omega) (by omega) (by omega))]
  · exact fun y => delExportOff ring root lane src R (piD (ref.phys x.1)) x.2
      (digitSite ring root (src + k)) (siteNe ring root _ _ (by omega) (by omega) (by omega)) y

/-- **The export row on the coupled chain.** The delimiter letter at offset `src + R - 1`, from a
layout state in the packet-order class with ordered audit frames, carries the clause; an accepted
export, stamped `clock + 1`, becomes the leftmost pending packet. Consumer: `widthQueueStep`. -/
theorem widthQueueExport (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (k : Nat) (hk : k + 1 = R)
    (ho : PacketOrder R (widthLaneOfState ref.toWidthDigitReference root lane src R x)) (hfo : AuditFrameOrder x.2)
    (χ : Nat → DigitExport _ n) (h : QueueAt ring root lane src R (piD (ref.phys x.1)) x.2 χ) :
    ∃ χ' : Nat → DigitExport _ n, QueueAt ring root lane src R
      (piD (ref.phys (widthDigitAuditNext (ref.toWidthDigitReference) x
        (digitSite ring root (src + k))).1))
      (widthDigitAuditNext (ref.toWidthDigitReference) x
        (digitSite ring root (src + k))).2 χ' := by
  subst hk
  obtain ⟨m, hm0⟩ := ho
  have hm : OrderAt (k + 1) (cohortProj ring root lane src (k + 1) (piD (ref.phys x.1))) m := hm0
  have hl := (widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src (k + 1) hR hsrc hend x hx
    (digitSite ring root (src + k))).2
  rw [cohortEdgeOfSite ring root src (k + 1) hend k (by omega)] at hl
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hx
  obtain ⟨-, hroot, hbX, hbY⟩ := widthLeadEdge ref.toWidthDigitReference ref.singletonFixed hn root x.1 hL
    (digitSite ring root (src + k))
  have hbX' : (pairW (piD (ref.phys x.1) (digitSite ring root (src + k))).word
      (piD (ref.phys x.1) (digitSite ring root (src + (k + 1)))).word).1.beta =
      (piD (ref.phys x.1) (digitSite ring root (src + k))).word.beta := hbX
  have hbY' : (pairW (piD (ref.phys x.1) (digitSite ring root (src + k))).word
      (piD (ref.phys x.1) (digitSite ring root (src + (k + 1)))).word).2.beta =
      (piD (ref.phys x.1) (digitSite ring root (src + (k + 1)))).word.beta := hbY
  have hlx := bankRepairDigitSiteNonroot ring root (piD (ref.phys x.1)) hroot (src + k) (by omega)
    (by omega)
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
  have pI := projIn ring root lane src (k + 1) (piD (ref.phys x.1)) (k + 1) (Nat.le_refl _) (by omega)
  have pL := projLive ring root lane src (k + 1) (piD (ref.phys x.1)) (k + 1) (Nat.le_refl _)
    (by omega)
  rw [← pO, ← pI, ← pL] at hrow hexp
  have hky : (cohortProj ring root lane src (k + 1) (piD (ref.phys x.1))).live (k + 1) = true →
      (cohortProj ring root lane src (k + 1) (piD (ref.phys x.1))).inp (k + 1) = .E := fun hl' =>
    ((orderPaper (k + 1) m _ hm).2 (k + 1) (Nat.le_refl _) (by omega) hl').1
  have he : digitSite ring root (src + k) = digitSite ring root (src + (k + 1 - 1)) := by
    rw [Nat.add_sub_cancel]
  rw [queueAtIff] at h
  refine (exists_congr fun χ' => queueAtIff ring root lane src (k + 1) _ _ χ').2 ?_
  have hlane : cohortProj ring root lane src (k + 1)
      (piD (ref.phys (widthDigitAuditNext (ref.toWidthDigitReference) x
        (digitSite ring root (src + k))).1)) =
      cohortEdge (k + 1) (cohortProj ring root lane src (k + 1) (piD (ref.phys x.1))) k := hl
  rw [hlane]
  refine queueLaneDel (k + 1) k m rfl _ hm _ _ _ _ χ (x.2.clock + 1) ?_ ?_ ?_ ?_ h
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
    refine ⟨fun hp => ?_, fun y => ?_⟩
    · show (laneGhost lane ((digitAuditStep ring (piD (ref.phys x.1)) x.2
        (digitSite ring root (src + k))).current
          (ring.rightNeighbor (digitSite ring root (src + k))))).input =
        (laneGhost lane (x.2.current (digitSite ring root (src + (k + 1))))).input
      rw [curY ring (by omega)]
      exact (congrArg Prod.snd hrow).trans (delGhostKeep _ _ _ _ _ _ hky hd hp)
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

/-! ### Every coupled letter, every coupled word -/

/-- **The step of the fourth clause.** Every coupled letter, from a layout state in the
packet-order class with ordered audit frames, carries `QueueAt` (with a new witness).
Consumer: `widthPacketQueueStep`. -/
theorem widthQueueStep (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (hfo : AuditFrameOrder x.2)
    (ho : PacketOrder R (widthLaneOfState ref.toWidthDigitReference root lane src R x))
    (χ : Nat → DigitExport _ n) (h : QueueAt ring root lane src R (piD (ref.phys x.1)) x.2 χ)
    (e : Fin n) :
    ∃ χ' : Nat → DigitExport _ n, QueueAt ring root lane src R
      (piD (ref.phys (widthDigitAuditNext (ref.toWidthDigitReference) x e).1))
      (widthDigitAuditNext (ref.toWidthDigitReference) x e).2 χ' := by
  obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  by_cases hfar : j + 1 < src + R ∨ src + 2 * R ≤ j
  · exact ⟨χ, widthQueueFar ring ref hn root lane src R hR hsrc hend x hx j hj hfar χ h⟩
  · obtain ⟨k, rfl⟩ : ∃ k, j = src + k := ⟨j - src, by omega⟩
    by_cases h1 : k + 1 = R
    · exact widthQueueExport ring ref hn root lane src R hR hsrc hend x hx k h1 ho hfo χ h
    · by_cases h2 : k + 1 = 2 * R
      · exact widthQueueTargetTerm ring ref hn root lane src R hR hsrc hend x hx k h2 χ h
      · exact widthQueueTargetFin ring ref hn root lane src R hR hsrc hend x hx k (by omega)
          (by omega) ho χ h

/-- **The reached-state invariant with its ghost clause along one coupled letter**, with the
layout and the frame order. Consumer: `packetQueueWord`. -/
theorem widthPacketQueueStep (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (hfo : AuditFrameOrder x.2)
    (hq : PacketQueue ring root lane src R (piD (ref.phys x.1)) x.2) (e : Fin n) :
    WidthCohortLayout ref.toWidthDigitReference root src R
        (widthDigitAuditNext (ref.toWidthDigitReference) x e).1 ∧
      AuditFrameOrder (widthDigitAuditNext (ref.toWidthDigitReference) x e).2 ∧
      PacketQueue ring root lane src R
        (piD (ref.phys (widthDigitAuditNext (ref.toWidthDigitReference) x e).1))
        (widthDigitAuditNext (ref.toWidthDigitReference) x e).2 := by
  obtain ⟨ho, χ, h⟩ := hq
  obtain ⟨h1, h2⟩ := widthOrderCoupled ring ref hn root lane src R hR hsrc hend x hx ho e
  obtain ⟨χ', h'⟩ := widthQueueStep ring ref hn root lane src R hR hsrc hend x hx hfo ho χ h e
  exact ⟨h1, auditFrameOrderStep ring (piD (ref.phys x.1)) x.2 e hfo, h2, χ', h'⟩

end L3.WidthPacketMomentQueue

#print axioms L3.WidthPacketMomentQueue.widthOrderCoupled
#print axioms L3.WidthPacketMomentQueue.widthQueueFar
#print axioms L3.WidthPacketMomentQueue.widthQueueTargetFin
#print axioms L3.WidthPacketMomentQueue.widthQueueTargetTerm
#print axioms L3.WidthPacketMomentQueue.widthQueueExport
#print axioms L3.WidthPacketMomentQueue.widthQueueStep
#print axioms L3.WidthPacketMomentQueue.widthPacketQueueStep

import Leader.L3.Bank.RepairDigitPacketMomentGroupLabels
import Leader.L3.Width.PacketMomentLayout

/-!
# Lemma e-packet at a boundary reference: the audit ghosts and the labels of one pair lane

Generic form of the audit-ghost layer of the e-packet chain (`L3.PacketMomentCells`, the coupled
part of `L3.PacketMomentLabels`, and `L3.PacketMomentGroupLabels` after its lane lemmas) at an
arbitrary `WidthBoundaryReference` (whose `singletonFixed` field is the `hfix` of
`L3.WidthWave.widthLeadEdge`). Mechanical port: `BankReferenceState ring hbank` -> `ref.State`,
`bankWidthDigitReference ring hn hbank` -> `ref.toWidthDigitReference`, `z.val.1` -> `ref.phys z`,
`CohortLayout` -> `WidthCohortLayout`, `laneOfState` -> `widthLaneOfState`,
`bankRepairDigitLeadBankEdge` -> `widthLeadEdge`, `laneStep` -> `widthLaneStep`, the BANK phases
-> `L3.WidthPacketMoment.widthWinAlignedStep`, `widthPrepCut`, `widthVMomentAt`; the coupled
declarations get the prefix `width`; the lane-level declarations (`LabelOk`, `SampledAt`,
`sigNext`, `LabExport`, the row lemmas, `momentKeepUntil`, `momentWeaken`, `labTrialRun`) are
used as they are. `bankPrepLabMomentCheck` and `bankGroupSamplesCheck` check the port at BANK.
Carry (I3) is not ported here.
-/

namespace L3.WidthPacketMomentAudit

set_option autoImplicit false
set_option linter.unusedSectionVars false

open L3
open L3.PacketMoment
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.Correspondence
open L3.GhostBridge
open L3.WidthDigit
open L3.DigitPacketTransport
open L3.PacketMomentRelease
open L3.MarkedCells
open L3.PacketMomentWindow
open L3.PacketMomentAlign
open L3.PacketMomentPending
open L3.PacketMomentU
open L3.PacketMomentRetire
open L3.PacketMomentV
open L3.PacketMomentVSerial
open L3.PacketMomentPrep
open L3.PacketMomentFinish
open L3.PacketMomentSites
open L3.PacketMomentLabels
open L3.PacketMomentQueueLabels
open L3.PacketMomentTrialLabels
open L3.PacketMomentGroupLabels
open L3.WidthWave
open L3.WidthPacketMoment

section Ported

variable {n : Nat} (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
  (root : Fin n) (lane : DigitLane) (src R : Nat)

include hn

/-- The next coupled state. Consumer: every step lemma of this module. -/
abbrev widthNxt (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n) : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n :=
  widthDigitAuditNext (ref.toWidthDigitReference) x e

/-- The stamp of a letter at pair offset `k`. Consumer: `widthCellsPipe`, `widthCellsDel`,
`widthCellsFin`, `widthCellsTerm`, `widthCellsRead`. -/
abbrev widthStampAt (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (k : Nat) : DigitStamp n :=
  DigitStamp.mk (x.2.clock + 1) (digitSite ring root (src + k)) lane

/-- **A pair edge leaves the other cells' ghosts alone.** Consumer: the per-cell invariants. -/
theorem widthCellsFar (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (k : Nat) (hk : k < 2 * R) (q : Nat) (hq : q < 2 * R) (h1 : q ≠ k) (h2 : q ≠ k + 1) :
    laneCells ring root lane src (widthNxt ring ref x (digitSite ring root (src + k))).2.current q =
      laneCells ring root lane src x.2.current q := by
  show laneGhost lane ((digitAuditStep ring (piD (ref.phys x.1)) x.2
    (digitSite ring root (src + k))).current (digitSite ring root (src + q))) = _
  rw [curFar]
  · rfl
  · intro he
    exact h1 (by have := bankRepairDigitSiteInj ring root (by omega) (by omega) he; omega)
  · intro he
    rw [← bankRepairDigitSiteSucc] at he
    exact h2 (by have := bankRepairDigitSiteInj ring root (by omega) (by omega) he; omega)

/-- The two ghosts of a pair edge come from the service receipt. Consumer: `widthCellsPipe`,
`widthCellsDel`, `widthCellsFin`, `widthCellsTerm`. -/
theorem widthCellsXY (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (k : Nat) :
    laneCells ring root lane src (widthNxt ring ref x (digitSite ring root (src + k))).2.current k =
      laneGhost lane (svcAt ring (piD (ref.phys x.1)) x.2 (digitSite ring root (src + k))).x ∧
    laneCells ring root lane src (widthNxt ring ref x (digitSite ring root (src + k))).2.current
        (k + 1) =
      laneGhost lane (svcAt ring (piD (ref.phys x.1)) x.2 (digitSite ring root (src + k))).y := by
  constructor
  · show laneGhost lane ((digitAuditStep ring (piD (ref.phys x.1)) x.2
      (digitSite ring root (src + k))).current (digitSite ring root (src + k))) = _
    rw [curX]
  · show laneGhost lane ((digitAuditStep ring (piD (ref.phys x.1)) x.2
      (digitSite ring root (src + k))).current (digitSite ring root (src + (k + 1)))) = _
    rw [show digitSite ring root (src + (k + 1)) =
      ring.rightNeighbor (digitSite ring root (src + k)) from rfl, curY ring (by omega)]

/-- The layout facts at a pair edge: no leader at either end, and the border bits. Consumer:
`widthCellsPipe`, `widthCellsDel`, `widthCellsFin`, `widthCellsTerm`, `widthCellsRead`. -/
theorem widthEdgeFacts (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (k : Nat) (hk : k < 2 * R) :
    (piD (ref.phys x.1) (digitSite ring root (src + k))).word.native.l = false ∧
    (piD (ref.phys x.1) (digitSite ring root (src + k + 1))).word.native.l = false ∧
    laneMarkerX lane (piD (ref.phys x.1) (digitSite ring root (src + k)))
        (piD (ref.phys x.1) (digitSite ring root (src + k + 1))) = decide (k = 0 ∨ k = R) ∧
    laneMarkerY lane (piD (ref.phys x.1) (digitSite ring root (src + k)))
        (piD (ref.phys x.1) (digitSite ring root (src + k + 1))) = decide (k + 1 = R ∨ k + 1 = 2 * R) := by
  have hn5 : 5 ≤ n := by omega
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hx
  obtain ⟨-, hroot, hbX, hbY⟩ := widthLeadEdge ref.toWidthDigitReference ref.singletonFixed hn5 root x.1 hL
    (digitSite ring root (src + k))
  have hbX' : (pairW (piD (ref.phys x.1) (digitSite ring root (src + k))).word
      (piD (ref.phys x.1) (digitSite ring root (src + k + 1))).word).1.beta =
      (piD (ref.phys x.1) (digitSite ring root (src + k))).word.beta := hbX
  have hbY' : (pairW (piD (ref.phys x.1) (digitSite ring root (src + k))).word
      (piD (ref.phys x.1) (digitSite ring root (src + k + 1))).word).2.beta =
      (piD (ref.phys x.1) (digitSite ring root (src + k + 1))).word.beta := hbY
  refine ⟨bankRepairDigitSiteNonroot ring root (piD (ref.phys x.1)) hroot (src + k) (by omega)
    (by omega), bankRepairDigitSiteNonroot ring root (piD (ref.phys x.1)) hroot (src + k + 1) (by omega)
    (by omega), ?_, ?_⟩
  · rw [laneMarkerXBeta lane _ _ hbX']
    by_cases h0 : k = 0
    · subst h0; rw [decide_eq_true (Or.inl rfl)]; exact hb0
    · by_cases hkR : k = R
      · subst hkR; rw [decide_eq_true (Or.inr rfl)]; exact hbR
      · rw [decide_eq_false (by omega)]; exact hbF k (by omega) (by omega) hkR
  · rw [laneMarkerYBeta lane _ _ hbY']
    by_cases h1 : k + 1 = R
    · rw [decide_eq_true (Or.inl h1), show src + k + 1 = src + R by omega]; exact hbR
    · by_cases h2 : k + 1 = 2 * R
      · rw [decide_eq_true (Or.inr h2), show src + k + 1 = src + 2 * R by omega]; exact hb2R
      · rw [decide_eq_false (by omega)]; exact hbF (k + 1) (by omega) (by omega) h1

/-- **A Pipe edge on the two source ghosts.** Consumer: the per-cell invariants. -/
theorem widthCellsPipe (_hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (k : Nat) (h1 : k + 1 < R) :
    ((laneCells ring root lane src (widthNxt ring ref x (digitSite ring root (src + k))).2.current
        k).out,
      (laneCells ring root lane src (widthNxt ring ref x (digitSite ring root (src + k))).2.current
        (k + 1)).out) =
    ghostPipe (widthStampAt ring ref root lane src x k) (decide (k = 0))
      ((widthLaneOfState ref.toWidthDigitReference root lane src R x).out k)
      ((widthLaneOfState ref.toWidthDigitReference root lane src R x).out (k + 1))
      (laneCells ring root lane src x.2.current k).out
      (laneCells ring root lane src x.2.current (k + 1)).out := by
  obtain ⟨hlx, hly, hmX, hmY⟩ := widthEdgeFacts ring ref hn root lane src R hsrc hend x hx k (by omega)
  obtain ⟨hx', hy'⟩ := widthCellsXY ring ref hn root lane src x k
  rw [hx', hy', show widthLaneOfState ref.toWidthDigitReference root lane src R x =
      cohortProj ring root lane src R (piD (ref.phys x.1)) from rfl,
    projOut ring root lane src R _ k (by omega), projOut ring root lane src R _ (k + 1) h1]
  have hm0 : decide (k = 0) = laneMarkerX lane (piD (ref.phys x.1) (digitSite ring root (src + k)))
      (piD (ref.phys x.1) (digitSite ring root (src + k + 1))) := by
    rw [hmX]; by_cases h0 : k = 0 <;> simp [h0] <;> omega
  rw [hm0]
  exact rowPipeD lane (x.2.clock + 1) (digitSite ring root (src + k))
    (ring.rightNeighbor (digitSite ring root (src + k)))
    (piD (ref.phys x.1) (digitSite ring root (src + k))) (piD (ref.phys x.1) (digitSite ring root (src + k + 1)))
    (x.2.current (digitSite ring root (src + k)))
    (x.2.current (digitSite ring root (src + k + 1))) hlx hly
    (by rw [hmY]; simp; omega)

/-- **The delivery edge on the port output and the border input.** Consumer: the per-cell
invariants. -/
theorem widthCellsDel (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (k : Nat) (h2 : k + 1 = R) :
    ((laneCells ring root lane src (widthNxt ring ref x (digitSite ring root (src + k))).2.current
        k).out,
      (laneCells ring root lane src (widthNxt ring ref x (digitSite ring root (src + k))).2.current
        (k + 1)).input) =
    ghostDel (widthStampAt ring ref root lane src x k)
      ((widthLaneOfState ref.toWidthDigitReference root lane src R x).out k)
      ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp (k + 1))
      ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live (k + 1))
      (laneCells ring root lane src x.2.current k).out
      (laneCells ring root lane src x.2.current (k + 1)).input ∧
    (laneCells ring root lane src (widthNxt ring ref x (digitSite ring root (src + k))).2.current
        (k + 1)).carry = (laneCells ring root lane src x.2.current (k + 1)).carry := by
  obtain ⟨hlx, hly, hmX, hmY⟩ := widthEdgeFacts ring ref hn root lane src R hsrc hend x hx k (by omega)
  obtain ⟨hx', hy'⟩ := widthCellsXY ring ref hn root lane src x k
  rw [hx', hy', show widthLaneOfState ref.toWidthDigitReference root lane src R x =
      cohortProj ring root lane src R (piD (ref.phys x.1)) from rfl,
    projOut ring root lane src R _ k (by omega),
    projIn ring root lane src R _ (k + 1) (by omega) (by omega),
    projLive ring root lane src R _ (k + 1) (by omega) (by omega)]
  exact rowDelD lane (x.2.clock + 1) (digitSite ring root (src + k))
    (ring.rightNeighbor (digitSite ring root (src + k)))
    (piD (ref.phys x.1) (digitSite ring root (src + k))) (piD (ref.phys x.1) (digitSite ring root (src + k + 1)))
    (x.2.current (digitSite ring root (src + k)))
    (x.2.current (digitSite ring root (src + k + 1))) hlx hly
    (by rw [hmX]; simp; omega) (by rw [hmY]; simp; omega)

/-- **An input-motion edge on the two target input ghosts.** Consumer: the per-cell
invariants. -/
theorem widthCellsFin (_hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (k : Nat) (hk : R ≤ k) (h3 : k + 1 < 2 * R) :
    ((laneCells ring root lane src (widthNxt ring ref x (digitSite ring root (src + k))).2.current
        k).input,
      (laneCells ring root lane src (widthNxt ring ref x (digitSite ring root (src + k))).2.current
        (k + 1)).input) =
    ghostFinIn (decide (k = R))
      ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp k)
      ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live k)
      ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp (k + 1))
      ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live (k + 1))
      (laneCells ring root lane src x.2.current k).input
      (laneCells ring root lane src x.2.current (k + 1)).input := by
  obtain ⟨hlx, hly, hmX, hmY⟩ := widthEdgeFacts ring ref hn root lane src R hsrc hend x hx k (by omega)
  obtain ⟨hx', hy'⟩ := widthCellsXY ring ref hn root lane src x k
  obtain ⟨hI, -, -⟩ := rowFinD lane (x.2.clock + 1) (digitSite ring root (src + k))
    (ring.rightNeighbor (digitSite ring root (src + k)))
    (piD (ref.phys x.1) (digitSite ring root (src + k))) (piD (ref.phys x.1) (digitSite ring root (src + k + 1)))
    (x.2.current (digitSite ring root (src + k)))
    (x.2.current (digitSite ring root (src + k + 1))) hlx hly (by rw [hmY]; simp; omega)
  have hm0 : laneMarkerX lane (piD (ref.phys x.1) (digitSite ring root (src + k)))
      (piD (ref.phys x.1) (digitSite ring root (src + k + 1))) = decide (k = R) := by
    rw [hmX]; by_cases h0 : k = R <;> simp [h0] <;> omega
  rw [hm0] at hI
  rw [hx', hy', show widthLaneOfState ref.toWidthDigitReference root lane src R x =
      cohortProj ring root lane src R (piD (ref.phys x.1)) from rfl,
    projIn ring root lane src R _ k hk (by omega), projLive ring root lane src R _ k hk (by omega),
    projIn ring root lane src R _ (k + 1) (by omega) h3,
    projLive ring root lane src R _ (k + 1) (by omega) h3]
  exact hI

/-- **The terminal edge on the last target input ghost.** Consumer: the per-cell invariants. -/
theorem widthCellsTerm (_hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (k : Nat) (h4 : k + 1 = 2 * R) :
    (laneCells ring root lane src (widthNxt ring ref x (digitSite ring root (src + k))).2.current
        k).input =
    ghostTermIn ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp k)
      ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live k)
      (laneCells ring root lane src x.2.current k).input := by
  obtain ⟨hlx, hly, hmX, hmY⟩ := widthEdgeFacts ring ref hn root lane src R hsrc hend x hx k (by omega)
  obtain ⟨hx', -⟩ := widthCellsXY ring ref hn root lane src x k
  obtain ⟨t1, -⟩ := rowTermD lane (x.2.clock + 1) (digitSite ring root (src + k))
    (ring.rightNeighbor (digitSite ring root (src + k)))
    (piD (ref.phys x.1) (digitSite ring root (src + k))) (piD (ref.phys x.1) (digitSite ring root (src + k + 1)))
    (x.2.current (digitSite ring root (src + k)))
    (x.2.current (digitSite ring root (src + k + 1))) hlx hly
    (by rw [hmX]; simp; omega) (by rw [hmY]; simp; omega)
  rw [hx', show widthLaneOfState ref.toWidthDigitReference root lane src R x =
      cohortProj ring root lane src R (piD (ref.phys x.1)) from rfl,
    projIn ring root lane src R _ k (by omega) (by omega),
    projLive ring root lane src R _ k (by omega) (by omega)]
  exact t1

/-- **A read on a source edge records its sample**, with the stamp of the letter and the border
bit as tail. Consumer: the per-cell invariants (fresh labels). -/
theorem widthCellsRead (_hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (k : Nat) (h1 : k + 1 ≤ R)
    (hU : (widthLaneOfState ref.toWidthDigitReference root lane src R x).out k = .U) :
    ∃ smp : DigitSample (compileAdvice (ceilLogTwo n)) n, smp.id = widthStampAt ring ref root lane src x k ∧
      smp.tail = decide (k = 0) ∧
      DigitRecordedSample (widthNxt ring ref x (digitSite ring root (src + k))).2 smp := by
  obtain ⟨hlx, hly, hmX, -⟩ := widthEdgeFacts ring ref hn root lane src R hsrc hend x hx k (by omega)
  rw [show widthLaneOfState ref.toWidthDigitReference root lane src R x =
      cohortProj ring root lane src R (piD (ref.phys x.1)) from rfl,
    projOut ring root lane src R _ k (by omega)] at hU
  obtain ⟨smp, hid, htl, hrec⟩ := freshSample ring (piD (ref.phys x.1)) x.2
    (digitSite ring root (src + k)) lane hlx hly hU
  have hmX' : laneMarkerX lane (piD (ref.phys x.1) (digitSite ring root (src + k)))
      (piD (ref.phys x.1) (ring.rightNeighbor (digitSite ring root (src + k)))) =
      decide (k = 0 ∨ k = R) := hmX
  refine ⟨smp, hid, ?_, hrec⟩
  rw [htl, hmX']
  by_cases h0 : k = 0 <;> simp [h0] <;> omega

/-- **A letter off the pair** leaves every tracked output ghost alone, and every ghost but the
entry cell's. Consumer: the per-cell invariants. -/
theorem widthCellsOff (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (e : Fin n) (he : cohortEdgeOf root src R e = none)
    (q : Nat) (hq : q < 2 * R) :
    (laneCells ring root lane src (widthNxt ring ref x e).2.current q).out =
        (laneCells ring root lane src x.2.current q).out ∧
      (q ≠ 0 → laneCells ring root lane src (widthNxt ring ref x e).2.current q =
        laneCells ring root lane src x.2.current q) := by
  have hn5 : 5 ≤ n := by omega
  obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  have hin : ¬ (src ≤ j ∧ j < src + 2 * R) := by
    intro h
    unfold cohortEdgeOf at he
    rw [cohortIdxSite ring root j hj, if_pos h] at he
    cases he
  have farNe : ∀ q, q < 2 * R → src + q ≠ j → src + q ≠ j + 1 →
      laneCells ring root lane src (widthNxt ring ref x (digitSite ring root j)).2.current q =
      laneCells ring root lane src x.2.current q := by
    intro q hq n1 n2
    show laneGhost lane ((digitAuditStep ring (piD (ref.phys x.1)) x.2
      (digitSite ring root j)).current (digitSite ring root (src + q))) = _
    rw [curFar]
    · rfl
    · intro he
      exact n1 (bankRepairDigitSiteInj ring root (by omega) hj he)
    · intro he
      rw [← bankRepairDigitSiteSucc] at he
      by_cases hjn : j + 1 < n
      · exact n2 (bankRepairDigitSiteInj ring root (by omega) hjn he)
      · rw [show j + 1 = n by omega, bankRepairDigitSiteN] at he
        have := bankRepairDigitSiteInj ring root (k := src + q) (m := 0) (by omega) (by omega) he
        omega
  by_cases h1 : j + 1 = src ∧ q = 0
  · obtain ⟨h1, rfl⟩ := h1
    refine ⟨?_, fun h => absurd rfl h⟩
    obtain ⟨hL, hb0, -, -, -⟩ := hx
    obtain ⟨-, hroot, -, hbY⟩ := widthLeadEdge ref.toWidthDigitReference ref.singletonFixed hn5 root x.1 hL
      (digitSite ring root j)
    have hbY' : (pairW (piD (ref.phys x.1) (digitSite ring root j)).word
        (piD (ref.phys x.1) (digitSite ring root (j + 1))).word).2.beta =
        (piD (ref.phys x.1) (digitSite ring root (j + 1))).word.beta := hbY
    have hlx := bankRepairDigitSiteNonroot ring root (piD (ref.phys x.1)) hroot j (by omega) (by omega)
    have hly := bankRepairDigitSiteNonroot ring root (piD (ref.phys x.1)) hroot (j + 1) (by omega)
      (by omega)
    have hmy : laneMarkerY lane (piD (ref.phys x.1) (digitSite ring root j))
        (piD (ref.phys x.1) (digitSite ring root (j + 1))) = true := by
      rw [laneMarkerYBeta lane _ _ hbY', h1]
      exact hb0
    show (laneGhost lane ((digitAuditStep ring (piD (ref.phys x.1)) x.2
      (digitSite ring root j)).current (digitSite ring root (src + 0)))).out = _
    rw [show digitSite ring root (src + 0) = ring.rightNeighbor (digitSite ring root j) by
      rw [← h1]; rfl, curY ring (by omega)]
    refine (rowEntryD lane (x.2.clock + 1) (digitSite ring root j)
      (ring.rightNeighbor (digitSite ring root j)) (piD (ref.phys x.1) (digitSite ring root j))
      (piD (ref.phys x.1) (digitSite ring root (j + 1))) (x.2.current (digitSite ring root j))
      (x.2.current (digitSite ring root (j + 1))) hlx hly hmy).trans ?_
    unfold laneCells
    rw [← h1]
  · have hfar := farNe q hq (by omega) (by omega)
    exact ⟨by rw [hfar], fun _ => hfar⟩


/-- **`LabelOk` is kept by every coupled letter.** Consumer: `widthLabAlignCoupled`, `widthLabPreCoupled`,
the pending join (I2). -/
theorem widthLabelOkStep (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (σ : Nat → Option Nat) (e : Fin n)
    (h : LabelOk ring root lane src R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ x.2) :
    LabelOk ring root lane src R (widthLaneOfState ref.toWidthDigitReference root lane src R (widthNxt ring ref x e))
      (sigNext R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ (cohortEdgeOf root src R e))
      (widthNxt ring ref x e).2 := by
  have hls : widthLaneOfState ref.toWidthDigitReference root lane src R (widthNxt ring ref x e) =
      cohortLaneStep R (widthLaneOfState ref.toWidthDigitReference root lane src R x) (cohortEdgeOf root src R e) :=
    (widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hR hsrc hend x hx e).2
  have hmono : ∀ a v, SampledAt ring root lane src R x.2 a v →
      SampledAt ring root lane src R (widthNxt ring ref x e).2 a v :=
    fun a v hs => sampledStep ring root lane src R (piD (ref.phys x.1)) x.2 e a v hs
  obtain ⟨hS, hT⟩ := h
  rw [hls]
  rcases hE : cohortEdgeOf root src R e with _ | k
  · have hoff := widthCellsOff ring ref hn root lane src R hR hsrc hend x hx e hE
    refine ⟨fun j hj T v hD hv => ?_, fun j hj1 hj2 v hp hv => ?_⟩
    · rw [(hoff j (by omega)).1]
      exact hmono _ _ (hS j hj T v hD hv)
    · rw [(hoff j (by omega)).2 (by omega)]
      exact hmono _ _ (hT j hj1 hj2 v hp hv)
  · obtain ⟨hk, rfl⟩ := edgeOfSome ring root src R e k hE
    simp only [cohortLaneStep, sigNext]
    have far : ∀ q, q < 2 * R → q ≠ k → q ≠ k + 1 →
        laneCells ring root lane src (widthNxt ring ref x (digitSite ring root (src + k))).2.current
          q = laneCells ring root lane src x.2.current q :=
      fun q hq h1 h2 => widthCellsFar ring ref hn root lane src R hend x k hk q hq h1 h2
    by_cases h1 : k + 1 < R
    · -- Pipe edge
      have hout : (cohortEdge R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k).out =
          cohortUpd (cohortUpd (widthLaneOfState ref.toWidthDigitReference root lane src R x).out k
            (bankRepairDigitPipeStep (decide (k = 0)) ((widthLaneOfState ref.toWidthDigitReference root lane src R x).out k)
              ((widthLaneOfState ref.toWidthDigitReference root lane src R x).out (k + 1))).1) (k + 1)
            (bankRepairDigitPipeStep (decide (k = 0)) ((widthLaneOfState ref.toWidthDigitReference root lane src R x).out k)
              ((widthLaneOfState ref.toWidthDigitReference root lane src R x).out (k + 1))).2 := by
        unfold cohortEdge; rw [if_pos h1]
      have hinp : (cohortEdge R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k).inp =
          (widthLaneOfState ref.toWidthDigitReference root lane src R x).inp := by
        unfold cohortEdge; rw [if_pos h1]
      have hsig : sigStep R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ k =
          sigPipe k ((widthLaneOfState ref.toWidthDigitReference root lane src R x).out k)
            ((widthLaneOfState ref.toWidthDigitReference root lane src R x).out (k + 1)) σ := by
        unfold sigStep; rw [if_pos h1]
      have hg := widthCellsPipe ring ref hn root lane src R hR hsrc hend x hx k h1
      have hg1 := congrArg Prod.fst hg
      have hg2 := congrArg Prod.snd hg
      dsimp only at hg1 hg2
      have hpl := pipeLab (SampledAt ring root lane src R (widthNxt ring ref x
          (digitSite ring root (src + k))).2) k (widthStampAt ring ref root lane src x k)
        (decide (k = 0)) ((widthLaneOfState ref.toWidthDigitReference root lane src R x).out k)
        ((widthLaneOfState ref.toWidthDigitReference root lane src R x).out (k + 1)) σ
        (laneCells ring root lane src x.2.current k).out
        (laneCells ring root lane src x.2.current (k + 1)).out
        (fun T v hD hv => hmono _ _ (hS k (by omega) T v hD hv))
        (fun T v hD hv => hmono _ _ (hS (k + 1) h1 T v hD hv))
        (fun hU => by
          obtain ⟨smp, hid, htl, hrec⟩ :=
            widthCellsRead ring ref hn root lane src R hR hsrc hend x hx k (by omega) hU
          exact ⟨by omega, smp, by rw [hid], by rw [hid], by rw [hid], htl, hrec⟩)
      refine ⟨fun j hj T v hD hv => ?_, fun j hj1 hj2 v hp hv => ?_⟩
      · rw [hout] at hD
        rw [hsig] at hv
        by_cases hjk : j = k
        · subst hjk
          rw [updNe _ _ _ _ (by omega), updAt] at hD
          rw [hg1]
          exact hpl.1 T v hD hv
        · by_cases hjk1 : j = k + 1
          · subst hjk1
            rw [updAt] at hD
            rw [hg2]
            exact hpl.2 T v hD hv
          · rw [updNe _ _ _ _ hjk1, updNe _ _ _ _ hjk] at hD
            rw [sigPipeOther _ _ _ _ _ hjk hjk1] at hv
            rw [far j (by omega) hjk hjk1]
            exact hmono _ _ (hS j hj T v hD hv)
      · rw [hinp] at hp
        rw [hsig, sigPipeOther _ _ _ _ _ (by omega) (by omega)] at hv
        rw [far j hj2 (by omega) (by omega)]
        exact hmono _ _ (hT j hj1 hj2 v hp hv)
    · by_cases h2 : k + 1 = R
      · -- Delivery edge
        have hout : (cohortEdge R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k).out =
            cohortUpd (widthLaneOfState ref.toWidthDigitReference root lane src R x).out k
              (bankRepairDigitDelStep ((widthLaneOfState ref.toWidthDigitReference root lane src R x).out k)
                ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp (k + 1))
                ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live (k + 1))).1 := by
          unfold cohortEdge; rw [if_neg h1, if_pos h2]
        have hinp : (cohortEdge R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k).inp =
            cohortUpd (widthLaneOfState ref.toWidthDigitReference root lane src R x).inp (k + 1)
              (bankRepairDigitDelStep ((widthLaneOfState ref.toWidthDigitReference root lane src R x).out k)
                ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp (k + 1))
                ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live (k + 1))).2.1 := by
          unfold cohortEdge; rw [if_neg h1, if_pos h2]
        have hsig : sigStep R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ k =
            sigDel k ((widthLaneOfState ref.toWidthDigitReference root lane src R x).out k)
              ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp (k + 1))
              ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live (k + 1)) σ := by
          unfold sigStep; rw [if_neg h1, if_pos h2]
        obtain ⟨hg, -⟩ := widthCellsDel ring ref hn root lane src R hR hsrc hend x hx k h2
        have hg1 := congrArg Prod.fst hg
        have hg2 := congrArg Prod.snd hg
        dsimp only at hg1 hg2
        have hdl := delLab (SampledAt ring root lane src R (widthNxt ring ref x
            (digitSite ring root (src + k))).2) k (widthStampAt ring ref root lane src x k)
          ((widthLaneOfState ref.toWidthDigitReference root lane src R x).out k)
          ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp (k + 1))
          ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live (k + 1)) σ
          (laneCells ring root lane src x.2.current k).out
          (laneCells ring root lane src x.2.current (k + 1)).input
          (fun T v hD hv => hmono _ _ (hS k (by omega) T v hD hv))
          (fun v hp hv => hmono _ _ (hT (k + 1) (by omega) (by omega) v hp hv))
          (fun hU => by
            obtain ⟨smp, hid, htl, hrec⟩ :=
              widthCellsRead ring ref hn root lane src R hR hsrc hend x hx k (by omega) hU
            exact ⟨by omega, smp, by rw [hid], by rw [hid], by rw [hid], htl, hrec⟩)
        refine ⟨fun j hj T v hD hv => ?_, fun j hj1 hj2 v hp hv => ?_⟩
        · rw [hout] at hD
          rw [hsig] at hv
          by_cases hjk : j = k
          · subst hjk
            rw [updAt] at hD
            rw [hg1]
            exact hdl.1 T v hD hv
          · rw [updNe _ _ _ _ hjk] at hD
            rw [sigDelOther _ _ _ _ _ _ hjk (by omega)] at hv
            rw [far j (by omega) hjk (by omega)]
            exact hmono _ _ (hS j hj T v hD hv)
        · rw [hinp] at hp
          rw [hsig] at hv
          by_cases hjk1 : j = k + 1
          · subst hjk1
            rw [updAt] at hp
            rw [hg2]
            exact hdl.2 v hp hv
          · rw [updNe _ _ _ _ hjk1] at hp
            rw [sigDelOther _ _ _ _ _ _ (by omega) hjk1] at hv
            rw [far j hj2 (by omega) hjk1]
            exact hmono _ _ (hT j hj1 hj2 v hp hv)
      · by_cases h3 : k + 1 < 2 * R
        · -- Input-motion edge
          have hout : (cohortEdge R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k).out =
              (widthLaneOfState ref.toWidthDigitReference root lane src R x).out := by
            unfold cohortEdge; rw [if_neg h1, if_neg h2, if_pos h3]
          have hinp : (cohortEdge R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k).inp =
              cohortUpd (cohortUpd (widthLaneOfState ref.toWidthDigitReference root lane src R x).inp k
                (bankRepairDigitFinStep (decide (k = R))
                  ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp k)
                  ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live k)
                  ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp (k + 1))
                  ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live (k + 1))).1) (k + 1)
                (bankRepairDigitFinStep (decide (k = R))
                  ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp k)
                  ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live k)
                  ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp (k + 1))
                  ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live (k + 1))).2.2.1 := by
            unfold cohortEdge; rw [if_neg h1, if_neg h2, if_pos h3]
          have hsig : sigStep R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ k =
              sigFin k ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp k)
                ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live k)
                ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp (k + 1))
                ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live (k + 1)) σ := by
            unfold sigStep; rw [if_neg h1, if_neg h2, if_pos h3]
          have hg := widthCellsFin ring ref hn root lane src R hR hsrc hend x hx k (by omega) h3
          have hg1 := congrArg Prod.fst hg
          have hg2 := congrArg Prod.snd hg
          dsimp only [ghostFinIn] at hg1 hg2
          have hfl := finLab (SampledAt ring root lane src R (widthNxt ring ref x
              (digitSite ring root (src + k))).2) k (decide (k = R))
            ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp k)
            ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live k)
            ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp (k + 1))
            ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live (k + 1)) σ
            (laneCells ring root lane src x.2.current k).input
            (laneCells ring root lane src x.2.current (k + 1)).input
            (fun v hp hv => hmono _ _ (hT k (by omega) (by omega) v hp hv))
            (fun v hp hv => hmono _ _ (hT (k + 1) (by omega) h3 v hp hv))
          refine ⟨fun j hj T v hD hv => ?_, fun j hj1 hj2 v hp hv => ?_⟩
          · rw [hout] at hD
            rw [hsig, sigFinLow _ _ _ _ _ _ _ (by omega)] at hv
            rw [far j (by omega) (by omega) (by omega)]
            exact hmono _ _ (hS j hj T v hD hv)
          · rw [hinp] at hp
            rw [hsig] at hv
            by_cases hjk : j = k
            · subst hjk
              rw [updNe _ _ _ _ (by omega), updAt] at hp
              rw [hg1]
              exact hfl.1 v hp hv
            · by_cases hjk1 : j = k + 1
              · subst hjk1
                rw [updAt] at hp
                rw [hg2]
                exact hfl.2 v hp hv
              · rw [updNe _ _ _ _ hjk1, updNe _ _ _ _ hjk] at hp
                rw [sigFinLow _ _ _ _ _ _ _ hjk1] at hv
                rw [far j hj2 hjk hjk1]
                exact hmono _ _ (hT j hj1 hj2 v hp hv)
        · -- Terminal edge
          have h4 : k + 1 = 2 * R := by omega
          have hout : (cohortEdge R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k).out =
              (widthLaneOfState ref.toWidthDigitReference root lane src R x).out := by
            unfold cohortEdge; rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
          have hinp : (cohortEdge R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k).inp =
              cohortUpd (widthLaneOfState ref.toWidthDigitReference root lane src R x).inp k
                (cohortTermStep ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp k)
                  ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live k)).1 := by
            unfold cohortEdge; rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
          have hsig : sigStep R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ k = σ := by
            unfold sigStep; rw [if_neg h1, if_neg h2, if_neg h3]
          have hg := widthCellsTerm ring ref hn root lane src R hR hsrc hend x hx k h4
          have htl := termLab (SampledAt ring root lane src R (widthNxt ring ref x
              (digitSite ring root (src + k))).2) k
            ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp k)
            ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live k) σ
            (laneCells ring root lane src x.2.current k).input
            (fun v hp hv => hmono _ _ (hT k (by omega) (by omega) v hp hv))
          refine ⟨fun j hj T v hD hv => ?_, fun j hj1 hj2 v hp hv => ?_⟩
          · rw [hout] at hD
            rw [hsig] at hv
            rw [far j (by omega) (by omega) (by omega)]
            exact hmono _ _ (hS j hj T v hD hv)
          · rw [hinp] at hp
            rw [hsig] at hv
            by_cases hjk : j = k
            · subst hjk
              rw [updAt] at hp
              rw [hg]
              exact htl v hp hv
            · rw [updNe _ _ _ _ hjk] at hp
              rw [far j hj2 hjk (by omega)]
              exact hmono _ _ (hT j hj1 hj2 v hp hv)


/-- **I1 on the coupled chain.** With aligned labels `SiteAlign a` and `LabelOk`, a coupled
letter either exports nothing and keeps both, or exports, delivering into the border input a
recorded sample of the audit **taken at source cell `src + a`** (tail bit `a = 0`), after which
the labels are aligned at `a - 1` (or `R - 1` after the tail). Consumer: the pending join (I2),
the aligned completion (`DigitCompletion`). -/
theorem widthLabAlignCoupled (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (σ : Nat → Option Nat) (a : Nat) (e : Fin n)
    (hA : SiteAlign R a (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ)
    (hL : LabelOk ring root lane src R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ x.2) :
    LabelOk ring root lane src R (widthLaneOfState ref.toWidthDigitReference root lane src R (widthNxt ring ref x e))
        (sigNext R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ (cohortEdgeOf root src R e))
        (widthNxt ring ref x e).2 ∧
      ((SiteAlign R a (widthLaneOfState ref.toWidthDigitReference root lane src R (widthNxt ring ref x e))
          (sigNext R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ (cohortEdgeOf root src R e)) ∧
        ∀ B, ¬ LabExport R (widthLaneOfState ref.toWidthDigitReference root lane src R x)
          (cohortEdgeOf root src R e) B) ∨
      (∃ B, LabExport R (widthLaneOfState ref.toWidthDigitReference root lane src R x) (cohortEdgeOf root src R e) B ∧
        SampledAt ring root lane src R (widthNxt ring ref x e).2
          (laneCells ring root lane src (widthNxt ring ref x e).2.current R).input a ∧
        SiteAlign R (if a = 0 then R - 1 else a - 1)
          (widthLaneOfState ref.toWidthDigitReference root lane src R (widthNxt ring ref x e))
          (sigNext R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ (cohortEdgeOf root src R e)))) := by
  have hL' := widthLabelOkStep ring ref hn root lane src R hR hsrc hend x hx σ e hL
  have hls : widthLaneOfState ref.toWidthDigitReference root lane src R (widthNxt ring ref x e) =
      cohortLaneStep R (widthLaneOfState ref.toWidthDigitReference root lane src R x) (cohortEdgeOf root src R e) :=
    (widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hR hsrc hend x hx e).2
  refine ⟨hL', ?_⟩
  rcases hE : cohortEdgeOf root src R e with _ | k
  · left
    rw [hls, hE]
    exact ⟨hA, fun B hB => by cases hB.1⟩
  · rw [hE] at hL'
    rw [hls, hE]
    rcases siteAlignStep R a hR _ σ k hA with ⟨hA', hne⟩ | ⟨B, hex, _, hlab, hA'⟩
    · left
      refine ⟨hA', fun B hB => ?_⟩
      obtain ⟨hk, hex⟩ := hB
      simp only [Option.some.injEq] at hk
      subst hk
      exact hne B hex
    · right
      have hk : k = R - 1 := by have := hex.1; omega
      subst hk
      refine ⟨B, ⟨rfl, hex⟩, ?_, hA'⟩
      have hp : pendIn ((widthLaneOfState ref.toWidthDigitReference root lane src R (widthNxt ring ref x e)).inp R) =
          true := by
        rw [hls, hE]
        simp only [cohortLaneStep]
        rw [hex.2.2.2.1]
        rfl
      exact hL'.2 R (by omega) (by omega) a hp hlab

/-- **The distinguished tail on the coupled chain.** Before alignment (`SitePre m`), every
coupled letter keeps `LabelOk`; an export shrinks the prefix, and the export at the empty prefix
delivers a recorded sample **taken at source cell `src`** with the tail bit set, after which the
labels are aligned at `R - 1`. Consumer: the distinguished-tail phase, then `widthLabAlignCoupled`. -/
theorem widthLabPreCoupled (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (σ : Nat → Option Nat) (m : Nat) (e : Fin n)
    (hP : SitePre R m (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ)
    (hL : LabelOk ring root lane src R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ x.2) :
    LabelOk ring root lane src R (widthLaneOfState ref.toWidthDigitReference root lane src R (widthNxt ring ref x e))
        (sigNext R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ (cohortEdgeOf root src R e))
        (widthNxt ring ref x e).2 ∧
      ((SitePre R m (widthLaneOfState ref.toWidthDigitReference root lane src R (widthNxt ring ref x e))
          (sigNext R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ (cohortEdgeOf root src R e)) ∧
        ∀ B, ¬ LabExport R (widthLaneOfState ref.toWidthDigitReference root lane src R x)
          (cohortEdgeOf root src R e) B) ∨
      (∃ B, LabExport R (widthLaneOfState ref.toWidthDigitReference root lane src R x) (cohortEdgeOf root src R e) B ∧
        (m = 0 → SampledAt ring root lane src R (widthNxt ring ref x e).2
            (laneCells ring root lane src (widthNxt ring ref x e).2.current R).input 0 ∧
          SiteAlign R (R - 1) (widthLaneOfState ref.toWidthDigitReference root lane src R (widthNxt ring ref x e))
            (sigNext R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ (cohortEdgeOf root src R e))) ∧
        (0 < m → SitePre R (m - 1) (widthLaneOfState ref.toWidthDigitReference root lane src R (widthNxt ring ref x e))
            (sigNext R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ (cohortEdgeOf root src R e))))) := by
  have hL' := widthLabelOkStep ring ref hn root lane src R hR hsrc hend x hx σ e hL
  have hls : widthLaneOfState ref.toWidthDigitReference root lane src R (widthNxt ring ref x e) =
      cohortLaneStep R (widthLaneOfState ref.toWidthDigitReference root lane src R x) (cohortEdgeOf root src R e) :=
    (widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hR hsrc hend x hx e).2
  refine ⟨hL', ?_⟩
  rcases hE : cohortEdgeOf root src R e with _ | k
  · left
    rw [hls, hE]
    exact ⟨hP, fun B hB => by cases hB.1⟩
  · rw [hE] at hL'
    rw [hls, hE]
    rcases sitePreStep R m hR _ σ k hP with ⟨hP', hne⟩ | ⟨B, hex, h0, hpos⟩
    · left
      refine ⟨hP', fun B hB => ?_⟩
      obtain ⟨hk, hex⟩ := hB
      simp only [Option.some.injEq] at hk
      subst hk
      exact hne B hex
    · right
      have hk : k = R - 1 := by have := hex.1; omega
      subst hk
      refine ⟨B, ⟨rfl, hex⟩, fun hm => ?_, hpos⟩
      obtain ⟨hlab0, hA'⟩ := h0 hm
      refine ⟨?_, hA'⟩
      have hp : pendIn ((widthLaneOfState ref.toWidthDigitReference root lane src R (widthNxt ring ref x e)).inp R) =
          true := by
        rw [hls, hE]
        simp only [cohortLaneStep]
        rw [hex.2.2.2.1]
        rfl
      have hlab : sigNext R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ (some (R - 1)) R =
          some 0 := by
        simp only [sigNext]
        rcases siteStep R hR _ σ (R - 1) hP.1 with ⟨-, hne⟩ | ⟨-, -, hne⟩ | ⟨B', -, -, hl⟩
        · exact absurd hex (hne B)
        · exact absurd hex (hne B)
        · rw [hl, hlab0]
      exact hL'.2 R (by omega) (by omega) 0 hp hlab


/-! ### The coupled label invariants -/

/-- The labelled aligned source. Consumer: the phases up to the mobile-free cut. -/
def WidthSrcLabAt (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    Prop :=
  ∃ σ, LabelOk ring root lane src R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ x.2 ∧
    SrcLab R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ

/-- The labelled distinguished-tail phase. Consumer: the start of `WidthSrcLabAt`. -/
def WidthPreLabAt (m : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ σ, LabelOk ring root lane src R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ x.2 ∧
    PreLab R m (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ

/-- The labelled aligned queue. Consumer: `widthPrepLabCut`. -/
def WidthWinLabAt (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    Prop :=
  ∃ σ, LabelOk ring root lane src R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ x.2 ∧
    WinLab R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ

/-- The labelled renewal trial at index `m`, or its target with the settled labels. Consumer:
`widthTrialLabMoment`, `widthGroupSamples`. -/
def WidthTrialLabAt (m : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ σ, LabelOk ring root lane src R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ x.2 ∧
    LabRun R m (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ ∧
    (LabTrial R m (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ ∨
      VTAt R m (widthLaneOfState ref.toWidthDigitReference root lane src R x))

/-- The lane and the labels of one coupled letter. Consumer: the coupled keep lemmas. -/
theorem widthLaneLab (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (e : Fin n) :
    WidthCohortLayout ref.toWidthDigitReference root src R (widthNxt ring ref x e).1 ∧
      widthLaneOfState ref.toWidthDigitReference root lane src R (widthNxt ring ref x e) =
        cohortLaneStep R (widthLaneOfState ref.toWidthDigitReference root lane src R x) (cohortEdgeOf root src R e) :=
  widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hR hsrc hend x hx e

/-- **The labelled aligned source on the coupled chain.** Consumer: the phases up to the
mobile-free cut. -/
theorem widthSrcLabCoupled (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (h : WidthCohortLayout ref.toWidthDigitReference root src R x.1 ∧ WidthSrcLabAt ring ref root lane src R x) :
    WidthCohortLayout ref.toWidthDigitReference root src R (widthNxt ring ref x e).1 ∧
      WidthSrcLabAt ring ref root lane src R (widthNxt ring ref x e) := by
  obtain ⟨hx, σ, hL, hs⟩ := h
  obtain ⟨h1, h2⟩ := widthLaneLab ring ref hn root lane src R hR hsrc hend x hx e
  refine ⟨h1, _, widthLabelOkStep ring ref hn root lane src R hR hsrc hend x hx σ e hL, ?_⟩
  rw [h2]
  cases cohortEdgeOf root src R e with
  | none => exact hs
  | some k => exact srcLabStep R hR _ σ k hs

/-- **The labelled distinguished-tail phase on the coupled chain**: kept without an export; an
export shrinks the prefix; the export at the empty prefix starts `WidthSrcLabAt`. Consumer: the start
of `WidthSrcLabAt`. -/
theorem widthPreLabCoupled (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (m : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (h : WidthPreLabAt ring ref root lane src R m x) :
    WidthCohortLayout ref.toWidthDigitReference root src R (widthNxt ring ref x e).1 ∧
      (WidthPreLabAt ring ref root lane src R m (widthNxt ring ref x e) ∨
        (m = 0 ∧ WidthSrcLabAt ring ref root lane src R (widthNxt ring ref x e)) ∨
        (0 < m ∧ WidthPreLabAt ring ref root lane src R (m - 1) (widthNxt ring ref x e))) := by
  obtain ⟨σ, hL, hs⟩ := h
  obtain ⟨h1, h2⟩ := widthLaneLab ring ref hn root lane src R hR hsrc hend x hx e
  have hL' := widthLabelOkStep ring ref hn root lane src R hR hsrc hend x hx σ e hL
  refine ⟨h1, ?_⟩
  unfold WidthPreLabAt WidthSrcLabAt
  rw [h2] at hL' ⊢
  revert hL'
  cases cohortEdgeOf root src R e with
  | none => exact fun hL' => Or.inl ⟨σ, hL', hs⟩
  | some k =>
      intro hL'
      rcases preLabStep R m hR _ σ k hs with ⟨hs', _⟩ | ⟨B, _, h0, hpos⟩
      · exact Or.inl ⟨_, hL', hs'⟩
      · by_cases hm : m = 0
        · exact Or.inr (Or.inl ⟨hm, _, hL', h0 hm⟩)
        · exact Or.inr (Or.inr ⟨by omega, _, hL', hpos (by omega)⟩)

/-- **The labelled aligned queue on the coupled chain** (with the window invariants). Consumer:
`widthPrepLabCut`. -/
theorem widthWinLabCoupled (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (h : WidthCohortLayout ref.toWidthDigitReference root src R x.1 ∧
      WinAligned R (widthLaneOfState ref.toWidthDigitReference root lane src R x) ∧
      WidthWinLabAt ring ref root lane src R x) :
    WidthCohortLayout ref.toWidthDigitReference root src R (widthNxt ring ref x e).1 ∧
      WinAligned R (widthLaneOfState ref.toWidthDigitReference root lane src R (widthNxt ring ref x e)) ∧
      WidthWinLabAt ring ref root lane src R (widthNxt ring ref x e) := by
  obtain ⟨hx, hw, σ, hL, hs⟩ := h
  obtain ⟨h1, hw'⟩ := widthWinAlignedStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hsrc hend hR x e ⟨hx, hw⟩
  obtain ⟨-, h2⟩ := widthLaneLab ring ref hn root lane src R hR hsrc hend x hx e
  refine ⟨h1, hw', _, widthLabelOkStep ring ref hn root lane src R hR hsrc hend x hx σ e hL, ?_⟩
  rw [h2]
  cases cohortEdgeOf root src R e with
  | none => exact hs
  | some k => exact winLabStep R hR _ σ k hs hw.2

/-- **The labelled renewal trial on the coupled chain**, kept off its target. Consumer:
`widthTrialLabMoment`. -/
theorem widthTrialLabCoupled (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (m : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (h : WidthCohortLayout ref.toWidthDigitReference root src R x.1 ∧ WidthTrialLabAt ring ref root lane src R m x)
    (hnt : ¬ VTAt R m (widthLaneOfState ref.toWidthDigitReference root lane src R x)) :
    WidthCohortLayout ref.toWidthDigitReference root src R (widthNxt ring ref x e).1 ∧
      WidthTrialLabAt ring ref root lane src R m (widthNxt ring ref x e) := by
  obtain ⟨hx, σ, hL, _, ht⟩ := h
  have ht' : LabTrial R m (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ := by
    rcases ht with ht | ht
    · exact ht
    · exact absurd ht hnt
  obtain ⟨h1, h2⟩ := widthLaneLab ring ref hn root lane src R (by omega) hsrc hend x hx e
  have hL' := widthLabelOkStep ring ref hn root lane src R (by omega) hsrc hend x hx σ e hL
  refine ⟨h1, ?_⟩
  unfold WidthTrialLabAt
  rw [h2] at hL' ⊢
  revert hL'
  cases cohortEdgeOf root src R e with
  | none => exact fun hL' => ⟨σ, hL', labTrialRun ht', Or.inl ht'⟩
  | some k =>
      intro hL'
      rcases labTrialStep R m hR _ σ k ht' with ⟨hv, hr⟩ | ht''
      · exact ⟨_, hL', hr, Or.inr hv⟩
      · exact ⟨_, hL', labTrialRun ht'', Or.inl ht''⟩

/-! ### The phases with labels -/

/-- **Phases U and retirement with labels.** From a layout state with the aligned queue, the
window invariants and the labelled aligned queue, the packet-only cut is reached keeping all of
them, with the bound of `prepCutCoupled`. Consumer: `widthPrepLabMoment`. -/
theorem widthPrepLabCut (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat) (hN : n < N)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1)
    (hs : WinAligned R (widthLaneOfState ref.toWidthDigitReference root lane src R x))
    (hl : WidthWinLabAt ring ref root lane src R x) :
    MomentBoundQ (widthDigitAuditNext (ref.toWidthDigitReference))
      (fun y => (PacketOnly R (widthLaneOfState ref.toWidthDigitReference root lane src R y) ∧
        (WidthCohortLayout ref.toWidthDigitReference root src R y.1 ∧
          WinAligned R (widthLaneOfState ref.toWidthDigitReference root lane src R y))) ∧
        (WidthCohortLayout ref.toWidthDigitReference root src R y.1 ∧
          WinAligned R (widthLaneOfState ref.toWidthDigitReference root lane src R y) ∧
          WidthWinLabAt ring ref root lane src R y)) N
      (N ^ uBudget R * N ^ (2 * R)) ((N - n) ^ uBudget R * (N - n) ^ (2 * R)) x :=
  momentKeep _ _ _ N _ _
    (fun y e h => widthWinLabCoupled ring ref hn root lane src R (by omega) hsrc hend y e h) x
    ⟨hx, hs, hl⟩ (widthPrepCut ref.toWidthDigitReference ref.singletonFixed hn root lane src R hsrc hend N hN hR x hx hs)

/-- **The labelled trial reaches its target with the settled labels**, with the bound of
`vMomentAtCoupled`. Consumer: `widthPrepLabMoment`, the aligned completion. -/
theorem widthTrialLabMoment (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (m : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (σ : Nat → Option Nat)
    (hL : LabelOk ring root lane src R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ x.2)
    (ht : LabTrial R m (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ) :
    MomentBoundQ (widthDigitAuditNext (ref.toWidthDigitReference))
      (fun y => VTAt R m (widthLaneOfState ref.toWidthDigitReference root lane src R y) ∧
        (WidthCohortLayout ref.toWidthDigitReference root src R y.1 ∧ WidthTrialLabAt ring ref root lane src R m y)) N
      (N ^ ((R + 2) * vK R)) ((N - n) ^ ((R + 2) * vK R)) x := by
  have hvi : VIAt R m (widthLaneOfState ref.toWidthDigitReference root lane src R x) := by
    obtain ⟨a, i, hai, hA, hS, hm, _⟩ := ht
    exact ⟨a, i, hai, hA, hS, hm⟩
  exact momentKeepUntil _ _ _ N _ _
    (fun y e h hnt => widthTrialLabCoupled ring ref hn root lane src R hR hsrc hend m y e h hnt) x
    ⟨hx, σ, hL, labTrialRun ht, Or.inl ht⟩
    (widthVMomentAt ref.toWidthDigitReference ref.singletonFixed hn root lane src R hsrc hend N hN hR m x hx hvi)

/-- **U, retirement and the renewal trial with labels.** From a layout state with the aligned
queue, the window invariants and the labelled aligned queue, the trial target `VTAt m` is reached
in `WidthTrialLabAt m` for the index `m` of the packet-only cut, with
`E[z^T] ≤ w^{uBudget R + 2R + (R+2)(2R+2)}`. Consumer: the aligned completion
(`widthGroupSamples` at `m = R - 1`), the per-pair moment. -/
theorem widthPrepLabMoment (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1)
    (hs : WinAligned R (widthLaneOfState ref.toWidthDigitReference root lane src R x))
    (hl : WidthWinLabAt ring ref root lane src R x) :
    MomentBoundQ (widthDigitAuditNext (ref.toWidthDigitReference))
      (fun y => ∃ m, VTAt R m (widthLaneOfState ref.toWidthDigitReference root lane src R y) ∧
        WidthCohortLayout ref.toWidthDigitReference root src R y.1 ∧ WidthTrialLabAt ring ref root lane src R m y) N
      (N ^ uBudget R * N ^ (2 * R) * N ^ ((R + 2) * vK R))
      ((N - n) ^ uBudget R * (N - n) ^ (2 * R) * (N - n) ^ ((R + 2) * vK R)) x := by
  refine momentSeq _ _ _ N _ _ _ _ x
    (Nat.pow_le_pow_left (Nat.sub_le N n) _) (fun y hy => ?_)
    (widthPrepLabCut ring ref hn root lane src R hR hsrc hend N hN x hx hs hl)
  obtain ⟨⟨hP, -⟩, hly, -, σ, hL, a', hA, hLA⟩ := hy
  refine momentWeaken _ _ _ N _ _ (fun z hz => ⟨vIdx R a' 0, hz⟩) y
    (widthTrialLabMoment ring ref hn root lane src R hR hsrc hend N hN (vIdx R a' 0) y hly σ hL
      (labTrialOfPacketOnly R a' _ σ hA hLA hP))

/-! ### The samples of the aligned group -/

/-- **The aligned group holds the samples `src + j`.** At an aligned group reached in the
labelled trial, the input atom of target cell `R + j` is a recorded sample of the audit taken at
source cell `src + j`, on the lane, with tail bit `j = 0`. Consumer: the aligned completion
(`DigitCompletion` of the group's terminal, I3). -/
theorem widthGroupSamples (hR : 1 ≤ R)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hg : AGroup R (widthLaneOfState ref.toWidthDigitReference root lane src R y))
    (ht : WidthTrialLabAt ring ref root lane src R (R - 1) y) (j : Nat) (hj : j < R) :
    SampledAt ring root lane src R y.2 (laneCells ring root lane src y.2.current (R + j)).input j := by
  obtain ⟨σ, hL, hrun, _⟩ := ht
  obtain ⟨hS, hσ⟩ := groupLabels R hR _ σ hg hrun j hj
  refine hL.2 (R + j) (by omega) (by omega) j ?_ hσ
  revert hS
  cases (widthLaneOfState ref.toWidthDigitReference root lane src R y).inp (R + j) <;> simp [isSI, pendIn]

end Ported

/-- **Port check**: at the BANK boundary reference the generic labelled preparation is
`L3.PacketMomentGroupLabels.prepLabMoment`. Consumer: none in the chain; it checks the port. -/
theorem bankPrepLabMomentCheck {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1)
    (hs : WinAligned R (laneOfState ring hbank root lane src R x))
    (hl : WinLabAt ring hbank root lane src R x) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => ∃ m, VTAt R m (laneOfState ring hbank root lane src R y) ∧
        CohortLayout ring hbank root src R y.1 ∧ TrialLabAt ring hbank root lane src R m y) N
      (N ^ uBudget R * N ^ (2 * R) * N ^ ((R + 2) * vK R))
      ((N - n) ^ uBudget R * (N - n) ^ (2 * R) * (N - n) ^ ((R + 2) * vK R)) x :=
  widthPrepLabMoment ring (bankWidthBoundaryReference ring hn hbank) hn root lane src R hR hsrc
    hend N hN x hx hs hl

/-- **Port check**: at the BANK boundary reference the generic group samples are
`L3.PacketMomentGroupLabels.groupSamples`. Consumer: none in the chain; it checks the port. -/
theorem bankGroupSamplesCheck {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 1 ≤ R)
    (y : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hg : AGroup R (laneOfState ring hbank root lane src R y))
    (ht : TrialLabAt ring hbank root lane src R (R - 1) y) (j : Nat) (hj : j < R) :
    SampledAt ring root lane src R y.2 (laneCells ring root lane src y.2.current (R + j)).input j :=
  widthGroupSamples ring (bankWidthBoundaryReference ring hn hbank) hn root lane src R hR y hg ht
    j hj

end L3.WidthPacketMomentAudit

#print axioms L3.WidthPacketMomentAudit.widthCellsFar
#print axioms L3.WidthPacketMomentAudit.widthCellsPipe
#print axioms L3.WidthPacketMomentAudit.widthCellsDel
#print axioms L3.WidthPacketMomentAudit.widthCellsFin
#print axioms L3.WidthPacketMomentAudit.widthCellsTerm
#print axioms L3.WidthPacketMomentAudit.widthCellsRead
#print axioms L3.WidthPacketMomentAudit.widthCellsOff
#print axioms L3.WidthPacketMomentAudit.widthEdgeFacts
#print axioms L3.WidthPacketMomentAudit.widthLabelOkStep
#print axioms L3.WidthPacketMomentAudit.widthLabAlignCoupled
#print axioms L3.WidthPacketMomentAudit.widthLabPreCoupled
#print axioms L3.WidthPacketMomentAudit.widthSrcLabCoupled
#print axioms L3.WidthPacketMomentAudit.widthPreLabCoupled
#print axioms L3.WidthPacketMomentAudit.widthWinLabCoupled
#print axioms L3.WidthPacketMomentAudit.widthTrialLabCoupled
#print axioms L3.WidthPacketMomentAudit.widthPrepLabCut
#print axioms L3.WidthPacketMomentAudit.widthTrialLabMoment
#print axioms L3.WidthPacketMomentAudit.widthPrepLabMoment
#print axioms L3.WidthPacketMomentAudit.widthGroupSamples
#print axioms L3.WidthPacketMomentAudit.bankPrepLabMomentCheck
#print axioms L3.WidthPacketMomentAudit.bankGroupSamplesCheck

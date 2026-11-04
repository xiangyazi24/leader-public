import Leader.L3.Bank.RepairDigitPacketMomentHeldQueue
import Leader.L3.Width.PacketMomentLaneGhosts

/-!
# Lemma e-packet, I2b, at a boundary reference: the held clause over the renewal trial

Generic form of the coupled part of `L3.PacketMomentHeldQueue` (BankRepairDigitPacketMomentHeldQueue)
at an arbitrary `WidthBoundaryReference`, by the port of `L3.WidthPacketMomentAudit` (state type,
`ref.phys`, `WidthCohortLayout`, `widthLaneOfState`, `widthLaneStep`, `widthLeadEdge`, the `width`
cell lemmas, `L3.WidthPacketMoment.widthVAlignAt`): `WidthHeldAt`, `widthHeldExport`,
`widthHeldFinC`, `widthHeldTermC`, `widthHeldStep`, `WidthHeldTrial`, `widthHeldTrialStep`,
`widthHeldTrialMoment`, `widthHeldOfPacketQueue`, `widthHeldGroup`. The lane clause (`held`,
`HeldQ`) and its rows (`heldFin`, `heldTerm`, `heldDel`, `heldSame`, `heldOfPk`, `trialNext`) are
used as they are. Consumer: `L3.WidthPacketMomentGroupCompletion`, `L3.WidthPacketMomentAttempt`.
-/

namespace L3.WidthPacketMomentHeldQueue

set_option autoImplicit false
set_option linter.unusedSimpArgs false
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
open L3.DigitPacketRelease
open L3.DigitPacketOrder
open L3.DigitPacketQueue
open L3.DigitPacketQueueStep
open L3.DigitPacketQueueRows
open L3.DigitPacketQueueExport
open L3.PacketMomentRelease
open L3.PacketMomentU
open L3.PacketMomentPending
open L3.PacketMomentV
open L3.PacketMomentVSerial
open L3.PacketMomentFinish
open L3.PacketMomentCells
open L3.PacketMomentGroupLabels
open L3.PacketMomentTrialEnd
open L3.PacketMomentHeldQueue
open L3.WidthWave
open L3.WidthPacketMoment
open L3.WidthPacketMomentAudit

section Ported

variable {n : Nat} (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
  (root : Fin n) (lane : DigitLane) (src R : Nat)

include hn

/-- **The held clause of a coupled state** with witness `χ`. Consumer: `widthHeldStep`,
`widthHeldTrialMoment`, `widthHeldGroup`. -/
def WidthHeldAt (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (χ : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) : Prop :=
  HeldQ R (widthLaneOfState ref.toWidthDigitReference root lane src R x)
    (fun q => (laneCells ring root lane src x.2.current q).input)
    (DelExport ring root lane src R x.2) χ

/-- **The export row on the coupled chain** (the coupling of
`L3.DigitPacketQueueExport.queueExport`). Consumer: `widthHeldStep`. -/
theorem widthHeldExport (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (k : Nat) (hk : k + 1 = R)
    (hlv : (widthLaneOfState ref.toWidthDigitReference root lane src R x).live R = false)
    (hfo : AuditFrameOrder x.2) (χ : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (h : WidthHeldAt ring ref root lane src R x χ) :
    ∃ χ' : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n,
      WidthHeldAt ring ref root lane src R (widthNxt ring ref x (digitSite ring root (src + k))) χ' := by
  subst hk
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
  have hlv' : (cohortProj ring root lane src (k + 1) (piD (ref.phys x.1))).live (k + 1) = false := hlv
  have he : digitSite ring root (src + k) = digitSite ring root (src + (k + 1 - 1)) := by
    rw [Nat.add_sub_cancel]
  unfold WidthHeldAt
  rw [hl]
  refine heldDel (k + 1) k rfl (cohortProj ring root lane src (k + 1) (piD (ref.phys x.1))) hlv'
    (fun q => (laneCells ring root lane src x.2.current q).input) _
    (DelExport ring root lane src (k + 1) x.2) _ χ (x.2.clock + 1) ?_ ?_ ?_ ?_ h
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
    refine ⟨?_, fun y => ?_⟩
    · show (laneGhost lane ((digitAuditStep ring (piD (ref.phys x.1)) x.2
        (digitSite ring root (src + k))).current
          (ring.rightNeighbor (digitSite ring root (src + k))))).input =
        (laneGhost lane (x.2.current (digitSite ring root (src + (k + 1))))).input
      rw [curY ring (by omega)]
      rw [hlv'] at hd hrow
      exact (congrArg Prod.snd hrow).trans (ghostDelKeep _ _ _ _ _ hd)
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

/-- **The Fin rows on the coupled chain.** Consumer: `widthHeldStep`. -/
theorem widthHeldFinC (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (k : Nat) (hk1 : R ≤ k) (hk2 : k + 1 < 2 * R)
    (i : Nat) (hS : VShape R i (widthLaneOfState ref.toWidthDigitReference root lane src R x))
    (χ : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (h : WidthHeldAt ring ref root lane src R x χ) :
    ∃ χ' : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n,
      WidthHeldAt ring ref root lane src R (widthNxt ring ref x (digitSite ring root (src + k))) χ' := by
  have hl := (widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hR hsrc hend x hx
    (digitSite ring root (src + k))).2
  rw [cohortEdgeOfSite ring root src R hend k (by omega)] at hl
  have hc := widthCellsFin ring ref hn root lane src R hR hsrc hend x hx k hk1 hk2
  unfold WidthHeldAt
  rw [hl]
  exact heldFin R k _ hk1 hk2 i hS
    (fun q => (laneCells ring root lane src x.2.current q).input)
    (fun q => (laneCells ring root lane src
      (widthNxt ring ref x (digitSite ring root (src + k))).2.current q).input)
    (DelExport ring root lane src R x.2) _ χ (congrArg Prod.fst hc) (congrArg Prod.snd hc)
    (fun q hq e1 e2 => congrArg DigitLaneGhost.input
      (widthCellsFar ring ref hn root lane src R hend x k (by omega) q hq e1 e2))
    (fun y => delExportOff ring root lane src R (piD (ref.phys x.1)) x.2
      (digitSite ring root (src + k)) (siteNe ring root _ _ (by omega) (by omega) (by omega)) y) h

/-- **The terminal row on the coupled chain.** Consumer: `widthHeldStep`. -/
theorem widthHeldTermC (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (k : Nat) (hk : k + 1 = 2 * R)
    (hlv : (widthLaneOfState ref.toWidthDigitReference root lane src R x).live k = false)
    (χ : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (h : WidthHeldAt ring ref root lane src R x χ) :
    ∃ χ' : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n,
      WidthHeldAt ring ref root lane src R (widthNxt ring ref x (digitSite ring root (src + k))) χ' := by
  have hl := (widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hR hsrc hend x hx
    (digitSite ring root (src + k))).2
  rw [cohortEdgeOfSite ring root src R hend k (by omega)] at hl
  have hc := widthCellsTerm ring ref hn root lane src R hR hsrc hend x hx k hk
  unfold WidthHeldAt
  rw [hl]
  exact heldTerm R k hk _ hlv
    (fun q => (laneCells ring root lane src x.2.current q).input)
    (fun q => (laneCells ring root lane src
      (widthNxt ring ref x (digitSite ring root (src + k))).2.current q).input)
    (DelExport ring root lane src R x.2) _ χ hc
    (fun q hq => congrArg DigitLaneGhost.input
      (widthCellsFar ring ref hn root lane src R hend x k (by omega) q (by omega) (by omega)
        (by omega)))
    (fun y => delExportOff ring root lane src R (piD (ref.phys x.1)) x.2
      (digitSite ring root (src + k)) (siteNe ring root _ _ (by omega) (by omega) (by omega)) y) h

/-- **The step of the held clause.** Every coupled letter, from a layout state in the trial
shape with ordered audit frames, carries `WidthHeldAt` (with a new witness). Consumer:
`widthHeldTrialStep`. -/
theorem widthHeldStep (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (hfo : AuditFrameOrder x.2) (i : Nat)
    (hS : VShape R i (widthLaneOfState ref.toWidthDigitReference root lane src R x))
    (χ : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (h : WidthHeldAt ring ref root lane src R x χ) (e : Fin n) :
    ∃ χ' : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n,
      WidthHeldAt ring ref root lane src R (widthNxt ring ref x e) χ' := by
  have hl := (widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hR hsrc hend x hx e).2
  rcases hE : cohortEdgeOf root src R e with _ | k
  · -- off the pair
    rw [hE] at hl
    have hne : e ≠ digitSite ring root (src + (R - 1)) := by
      intro he
      rw [he, cohortEdgeOfSite ring root src R hend (R - 1) (by omega)] at hE
      cases hE
    refine ⟨χ, ?_⟩
    unfold WidthHeldAt
    rw [hl]
    exact heldSame R (widthLaneOfState ref.toWidthDigitReference root lane src R x)
      (cohortLaneStep R (widthLaneOfState ref.toWidthDigitReference root lane src R x) none)
      (fun q => (laneCells ring root lane src x.2.current q).input)
      (fun q => (laneCells ring root lane src (widthNxt ring ref x e).2.current q).input)
      (DelExport ring root lane src R x.2) (DelExport ring root lane src R (widthNxt ring ref x e).2)
      χ (fun q _ _ => by rfl)
      (fun q hq1 hq2 _ => congrArg DigitLaneGhost.input
        ((widthCellsOff ring ref hn root lane src R hR hsrc hend x hx e hE q hq2).2 (by omega)))
      (fun y => delExportOff ring root lane src R (piD (ref.phys x.1)) x.2 e hne y) h
  · obtain ⟨hk, rfl⟩ := L3.PacketMomentLabels.edgeOfSome ring root src R e k hE
    by_cases h1 : k + 1 < R
    · -- a source pipe edge
      rw [hE] at hl
      refine ⟨χ, ?_⟩
      unfold WidthHeldAt
      rw [hl]
      have hp := (L3.DigitPacketRelease.edgePipe R k (widthLaneOfState ref.toWidthDigitReference root lane src R x) h1).1
      exact heldSame R (widthLaneOfState ref.toWidthDigitReference root lane src R x)
        (cohortLaneStep R (widthLaneOfState ref.toWidthDigitReference root lane src R x) (some k))
        (fun q => (laneCells ring root lane src x.2.current q).input)
        (fun q => (laneCells ring root lane src
          (widthNxt ring ref x (digitSite ring root (src + k))).2.current q).input)
        (DelExport ring root lane src R x.2)
        (DelExport ring root lane src R (widthNxt ring ref x (digitSite ring root (src + k))).2)
        χ (fun q _ _ => by
          show held ((cohortEdge R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k).inp q) = _
          rw [hp])
        (fun q hq1 hq2 _ => congrArg DigitLaneGhost.input
          (widthCellsFar ring ref hn root lane src R hend x k hk q hq2 (by omega) (by omega)))
        (fun y => delExportOff ring root lane src R (piD (ref.phys x.1)) x.2
          (digitSite ring root (src + k)) (siteNe ring root _ _ (by omega) (by omega) (by omega))
          y) h
    · by_cases h2 : k + 1 = R
      · exact widthHeldExport ring ref hn root lane src R hR hsrc hend x hx k h2
          ((hS.2 R (Nat.le_refl _) (by omega)).1) hfo χ h
      · by_cases h3 : k + 1 = 2 * R
        · exact widthHeldTermC ring ref hn root lane src R hR hsrc hend x hx k h3
            ((hS.2 k (by omega) (by omega)).1) χ h
        · exact widthHeldFinC ring ref hn root lane src R hR hsrc hend x hx k (by omega) (by omega)
            i hS χ h

/-! ### The renewal trial with the held clause -/

/-- The trial at index `m` (or its outcome) with ordered frames and the held clause. Consumer:
`widthHeldTrialMoment`. -/
def WidthHeldTrial (m : Nat)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  WidthCohortLayout ref.toWidthDigitReference root src R y.1 ∧ AuditFrameOrder y.2 ∧
    (VIAt R m (widthLaneOfState ref.toWidthDigitReference root lane src R y) ∨
      VTA R m (widthLaneOfState ref.toWidthDigitReference root lane src R y)) ∧
    ∃ χ, WidthHeldAt ring ref root lane src R y χ

/-- **The held trial is kept off its outcome.** Consumer: `widthHeldTrialMoment`. -/
theorem widthHeldTrialStep (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (m : Nat)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (h : WidthHeldTrial ring ref root lane src R m y)
    (hnt : ¬ VTA R m (widthLaneOfState ref.toWidthDigitReference root lane src R y)) :
    WidthHeldTrial ring ref root lane src R m (widthNxt ring ref y e) := by
  obtain ⟨hy, hfo, ht, χ, hq⟩ := h
  have hvi : VIAt R m (widthLaneOfState ref.toWidthDigitReference root lane src R y) := by
    rcases ht with ht | ht
    · exact ht
    · exact absurd ht hnt
  have hnext := trialNext R m hR _ (cohortEdgeOf root src R e) hvi
  obtain ⟨_, i, _, _, hS, _⟩ := hvi
  obtain ⟨h1, h2⟩ := widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R (by omega) hsrc hend y hy e
  obtain ⟨χ', hq'⟩ := widthHeldStep ring ref hn root lane src R (by omega) hsrc hend y hy hfo i hS
    χ hq e
  refine ⟨h1, auditFrameOrderStep ring (piD (ref.phys y.1)) y.2 e hfo, ?_, χ', hq'⟩
  rw [h2]
  rcases hnext with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- **The renewal trial carries the held clause to its outcome.** From a layout state with
ordered frames, whose lane is a trial state of index `m` and which satisfies the held clause, the
outcome `VTA R m` is reached with the held clause, `E[z^T] ≤ w^{(R+2)(2R+2)}` (the bound of
`vAlignAtCoupled`). Consumer: the aligned completion (`widthHeldGroup` at `m = R - 1`), the race
class. -/
theorem widthHeldTrialMoment (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (m : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (hfo : AuditFrameOrder x.2)
    (hs : VIAt R m (widthLaneOfState ref.toWidthDigitReference root lane src R x))
    (χ : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hq : WidthHeldAt ring ref root lane src R x χ) :
    MomentBoundQ (widthDigitAuditNext (ref.toWidthDigitReference))
      (fun y => VTA R m (widthLaneOfState ref.toWidthDigitReference root lane src R y) ∧
        WidthHeldTrial ring ref root lane src R m y) N
      (N ^ ((R + 2) * vK R)) ((N - n) ^ ((R + 2) * vK R)) x :=
  momentKeepUntil _ _ _ N _ _
    (fun y e h hnt => widthHeldTrialStep ring ref hn root lane src R hR hsrc hend m y e h hnt) x
    ⟨hx, hfo, Or.inl hs, χ, hq⟩
    (widthVAlignAt ref.toWidthDigitReference ref.singletonFixed hn root lane src R hsrc hend N hN hR m x hx hs)

/-! ### Entry and the aligned group -/

/-- **Entry**: at a trial state without settled target cells (the packet-only cut, the cleared
window after the front), the held clause is the moving-packet clause of the reached-state
invariant `PacketQueue`. Consumer: the composition of the trial with
`L3.DigitPacketQueueExport.packetQueueWord`. -/
theorem widthHeldOfPacketQueue
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hS : VShape R 0 (widthLaneOfState ref.toWidthDigitReference root lane src R x))
    (hq : PacketQueue ring root lane src R (piD (ref.phys x.1)) x.2) :
    ∃ χ, WidthHeldAt ring ref root lane src R x χ := by
  obtain ⟨-, χ, h⟩ := hq
  rw [queueAtIff] at h
  refine ⟨χ, heldOfPk R _ _ _ χ (fun q h1 h2 => ?_) h⟩
  have hc : (widthLaneOfState ref.toWidthDigitReference root lane src R x).inp q = .E ∨
      isPI ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp q) = true :=
    (hS.2 q h1 h2).2.2 (by omega)
  revert hc
  cases (widthLaneOfState ref.toWidthDigitReference root lane src R x).inp q <;> simp [isPI, held, pk]

/-- **The aligned group holds a consecutive run of the delimiter stream.** At the aligned group
with the held clause: `χ (R + j)` (`j < R`) is a recorded delimiter export whose operand is the
input atom of target cell `R + j`; the exports are stamped in decreasing order of `j`; and every
recorded delimiter export stamped at or after `χ (2R - 1)` is one of them. Consumer: the aligned
completion (the export clauses of `DigitCompletion`). -/
theorem widthHeldGroup (hR : 1 ≤ R)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hg : AGroup R (widthLaneOfState ref.toWidthDigitReference root lane src R y))
    (χ : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (h : WidthHeldAt ring ref root lane src R y χ) :
    (∀ j, j < R → DelExport ring root lane src R y.2 (χ (R + j)) ∧
      (laneCells ring root lane src y.2.current (R + j)).input = (χ (R + j)).operand) ∧
    (∀ j j', j < j' → j' < R → (χ (R + j')).time < (χ (R + j)).time) ∧
    (∀ ex, DelExport ring root lane src R y.2 ex → (χ (2 * R - 1)).time ≤ ex.time →
      ∃ j, j < R ∧ ex = χ (R + j)) := by
  have hall : ∀ q, R ≤ q → q < 2 * R →
      held ((widthLaneOfState ref.toWidthDigitReference root lane src R y).inp q) = true := by
    intro q h1 h2
    obtain ⟨-, hc⟩ := hg
    by_cases hq : q = R
    · rw [(hc q h1 h2).2.1 (by omega)]; rfl
    · rw [(hc q h1 h2).2.2.1 (by omega)]; rfl
  obtain ⟨c1, c2, c3⟩ := h
  refine ⟨fun j hj => c1 (R + j) (by omega) (by omega) (hall _ (by omega) (by omega)),
    fun j j' hjj hj' => c2 (R + j) (R + j') (by omega) (by omega) (by omega)
      (hall _ (by omega) (by omega)) (hall _ (by omega) (by omega)),
    fun ex hex ht => ?_⟩
  obtain ⟨q', p1, p2, -, p4⟩ := c3 (2 * R - 1) ex (by omega) (by omega)
    (hall _ (by omega) (by omega)) hex ht
  refine ⟨q' - R, by omega, ?_⟩
  rw [p4, show R + (q' - R) = q' by omega]

end Ported

end L3.WidthPacketMomentHeldQueue

#print axioms L3.WidthPacketMomentHeldQueue.widthHeldExport
#print axioms L3.WidthPacketMomentHeldQueue.widthHeldFinC
#print axioms L3.WidthPacketMomentHeldQueue.widthHeldTermC
#print axioms L3.WidthPacketMomentHeldQueue.widthHeldStep
#print axioms L3.WidthPacketMomentHeldQueue.widthHeldTrialStep
#print axioms L3.WidthPacketMomentHeldQueue.widthHeldTrialMoment
#print axioms L3.WidthPacketMomentHeldQueue.widthHeldOfPacketQueue
#print axioms L3.WidthPacketMomentHeldQueue.widthHeldGroup

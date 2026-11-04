import Leader.L3.Bank.RepairDigitPacketMomentCutLabels
import Leader.L3.Width.PacketMomentLaneGhosts

/-!
# Lemma e-packet with a cut at a boundary reference: the labelled samples are taken after the cut

Generic form of the coupled part of `L3.PacketMomentCutLabels` (BankRepairDigitPacketMomentCutLabels)
at an arbitrary `WidthBoundaryReference`, by the port of `L3.WidthPacketMomentAudit`:
`widthStampAfterCut`, `widthLabelCutStep`, `WidthSrcLabAtC`, `WidthPreLabAtC`, `WidthWinLabAtC`,
`WidthTrialLabAtC`, `widthSrcLabCoupledC`, `widthPreLabCoupledC`, `widthWinLabCoupledC`,
`widthTrialLabCoupledC`, `widthGroupSamplesC`, `widthTrialLabOfC`. `AfterCut`, `LabelCut` and
`labelCutNone` are used as they are. Consumer: the SMALL comparison lane (`hcmpMomentSmall`) and
the pre-attempt stage with a cut (`L3.WidthPacketMomentTailLab`).
-/

namespace L3.WidthPacketMomentCutLabels

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
open L3.PacketMomentCells
open L3.PacketMomentLabels
open L3.PacketMomentQueueLabels
open L3.PacketMomentTrialLabels
open L3.PacketMomentGroupLabels

open L3.PacketMomentCutLabels
open L3.WidthWave
open L3.WidthPacketMoment
open L3.WidthPacketMomentAudit

section Ported

variable {n : Nat} (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
  (root : Fin n) (lane : DigitLane) (src R : Nat)

include hn

/-- The fresh sample of a read is stamped `clock + 1`. Consumer: `widthLabelCutStep`. -/
theorem widthStampAfterCut (cut : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hc : cut ≤ x.2.clock) (k : Nat) :
    AfterCut cut (some (DigitAtom.sampled (widthStampAt ring ref root lane src x k))) := by
  intro id hid
  simp only [Option.some.injEq, DigitAtom.sampled.injEq] at hid
  subst hid
  show cut < x.2.clock + 1
  omega

/-- **`LabelCut` is kept by every coupled letter.** Consumer: the `C` coupled invariants. -/
theorem widthLabelCutStep (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (cut : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (σ : Nat → Option Nat) (e : Fin n)
    (h : LabelCut ring root lane src R cut (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ x.2) :
    LabelCut ring root lane src R cut (widthLaneOfState ref.toWidthDigitReference root lane src R (widthNxt ring ref x e))
      (sigNext R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ (cohortEdgeOf root src R e))
      (widthNxt ring ref x e).2 := by

  have hls : widthLaneOfState ref.toWidthDigitReference root lane src R (widthNxt ring ref x e) =
      cohortLaneStep R (widthLaneOfState ref.toWidthDigitReference root lane src R x) (cohortEdgeOf root src R e) :=
    (widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hR hsrc hend x hx e).2
  obtain ⟨hc, hS, hT⟩ := h
  refine ⟨Nat.le_succ_of_le hc, ?_⟩
  rw [hls]
  rcases hE : cohortEdgeOf root src R e with _ | k
  · have hoff := widthCellsOff ring ref hn root lane src R hR hsrc hend x hx e hE
    refine ⟨fun j hj T v hD hv => ?_, fun j hj1 hj2 v hp hv => ?_⟩
    · rw [(hoff j (by omega)).1]
      exact (hS j hj T v hD hv)
    · rw [(hoff j (by omega)).2 (by omega)]
      exact (hT j hj1 hj2 v hp hv)
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
      have hpl := pipeLab (fun a (_ : Nat) => AfterCut cut a) k (widthStampAt ring ref root lane src x k)
        (decide (k = 0)) ((widthLaneOfState ref.toWidthDigitReference root lane src R x).out k)
        ((widthLaneOfState ref.toWidthDigitReference root lane src R x).out (k + 1)) σ
        (laneCells ring root lane src x.2.current k).out
        (laneCells ring root lane src x.2.current (k + 1)).out
        (fun T v hD hv => (hS k (by omega) T v hD hv))
        (fun T v hD hv => (hS (k + 1) h1 T v hD hv))
        (fun _ => widthStampAfterCut ring ref hn root lane src cut x hc k)
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
            exact (hS j hj T v hD hv)
      · rw [hinp] at hp
        rw [hsig, sigPipeOther _ _ _ _ _ (by omega) (by omega)] at hv
        rw [far j hj2 (by omega) (by omega)]
        exact (hT j hj1 hj2 v hp hv)
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
        have hdl := delLab (fun a (_ : Nat) => AfterCut cut a) k (widthStampAt ring ref root lane src x k)
          ((widthLaneOfState ref.toWidthDigitReference root lane src R x).out k)
          ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp (k + 1))
          ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live (k + 1)) σ
          (laneCells ring root lane src x.2.current k).out
          (laneCells ring root lane src x.2.current (k + 1)).input
          (fun T v hD hv => (hS k (by omega) T v hD hv))
          (fun v hp hv => (hT (k + 1) (by omega) (by omega) v hp hv))
          (fun _ => widthStampAfterCut ring ref hn root lane src cut x hc k)
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
            exact (hS j hj T v hD hv)
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
            exact (hT j hj1 hj2 v hp hv)
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
          have hfl := finLab (fun a (_ : Nat) => AfterCut cut a) k (decide (k = R))
            ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp k)
            ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live k)
            ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp (k + 1))
            ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live (k + 1)) σ
            (laneCells ring root lane src x.2.current k).input
            (laneCells ring root lane src x.2.current (k + 1)).input
            (fun v hp hv => (hT k (by omega) (by omega) v hp hv))
            (fun v hp hv => (hT (k + 1) (by omega) h3 v hp hv))
          refine ⟨fun j hj T v hD hv => ?_, fun j hj1 hj2 v hp hv => ?_⟩
          · rw [hout] at hD
            rw [hsig, sigFinLow _ _ _ _ _ _ _ (by omega)] at hv
            rw [far j (by omega) (by omega) (by omega)]
            exact (hS j hj T v hD hv)
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
                exact (hT j hj1 hj2 v hp hv)
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
          have htl := termLab (fun a (_ : Nat) => AfterCut cut a) k
            ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp k)
            ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live k) σ
            (laneCells ring root lane src x.2.current k).input
            (fun v hp hv => (hT k (by omega) (by omega) v hp hv))
          refine ⟨fun j hj T v hD hv => ?_, fun j hj1 hj2 v hp hv => ?_⟩
          · rw [hout] at hD
            rw [hsig] at hv
            rw [far j (by omega) (by omega) (by omega)]
            exact (hS j hj T v hD hv)
          · rw [hinp] at hp
            rw [hsig] at hv
            by_cases hjk : j = k
            · subst hjk
              rw [updAt] at hp
              rw [hg]
              exact htl v hp hv
            · rw [updNe _ _ _ _ hjk] at hp
              rw [far j hj2 hjk (by omega)]
              exact (hT j hj1 hj2 v hp hv)

/-! ### The coupled label invariants with the cut -/

/-- The labelled aligned source after the cut. Consumer: `LaneCutC` (the mobile-free cut). -/
def WidthSrcLabAtC (cut : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ σ, LabelOk ring root lane src R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ x.2 ∧
    LabelCut ring root lane src R cut (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ x.2 ∧
    SrcLab R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ

/-- The labelled distinguished-tail phase after the cut. Consumer: the start of `WidthSrcLabAtC`. -/
def WidthPreLabAtC (cut m : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ σ, LabelOk ring root lane src R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ x.2 ∧
    LabelCut ring root lane src R cut (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ x.2 ∧
    PreLab R m (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ

/-- The labelled aligned queue after the cut. Consumer: `AttemptInvC`. -/
def WidthWinLabAtC (cut : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ σ, LabelOk ring root lane src R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ x.2 ∧
    LabelCut ring root lane src R cut (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ x.2 ∧
    WinLab R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ

/-- The labelled renewal trial after the cut. Consumer: `widthGroupSamplesC`, the trial with the cut. -/
def WidthTrialLabAtC (cut m : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ σ, LabelOk ring root lane src R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ x.2 ∧
    LabelCut ring root lane src R cut (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ x.2 ∧
    LabRun R m (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ ∧
    (LabTrial R m (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ ∨
      VTAt R m (widthLaneOfState ref.toWidthDigitReference root lane src R x))

/-- `srcLabCoupled` with the cut. Consumer: the phases up to the mobile-free cut. -/
theorem widthSrcLabCoupledC (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (cut : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (h : WidthCohortLayout ref.toWidthDigitReference root src R x.1 ∧ WidthSrcLabAtC ring ref root lane src R cut x) :
    WidthCohortLayout ref.toWidthDigitReference root src R (widthNxt ring ref x e).1 ∧
      WidthSrcLabAtC ring ref root lane src R cut (widthNxt ring ref x e) := by
  obtain ⟨hx, σ, hL, hC, hs⟩ := h
  obtain ⟨h1, h2⟩ := widthLaneLab ring ref hn root lane src R hR hsrc hend x hx e
  refine ⟨h1, _, widthLabelOkStep ring ref hn root lane src R hR hsrc hend x hx σ e hL,
    widthLabelCutStep ring ref hn root lane src R hR hsrc hend cut x hx σ e hC, ?_⟩
  rw [h2]
  cases cohortEdgeOf root src R e with
  | none => exact hs
  | some k => exact srcLabStep R hR _ σ k hs

/-- `preLabCoupled` with the cut. Consumer: the start of `WidthSrcLabAtC`. -/
theorem widthPreLabCoupledC (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (cut m : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1)
    (h : WidthPreLabAtC ring ref root lane src R cut m x) :
    WidthCohortLayout ref.toWidthDigitReference root src R (widthNxt ring ref x e).1 ∧
      (WidthPreLabAtC ring ref root lane src R cut m (widthNxt ring ref x e) ∨
        (m = 0 ∧ WidthSrcLabAtC ring ref root lane src R cut (widthNxt ring ref x e)) ∨
        (0 < m ∧ WidthPreLabAtC ring ref root lane src R cut (m - 1) (widthNxt ring ref x e))) := by
  obtain ⟨σ, hL, hC, hs⟩ := h
  obtain ⟨h1, h2⟩ := widthLaneLab ring ref hn root lane src R hR hsrc hend x hx e
  have hL' := widthLabelOkStep ring ref hn root lane src R hR hsrc hend x hx σ e hL
  have hC' := widthLabelCutStep ring ref hn root lane src R hR hsrc hend cut x hx σ e hC
  refine ⟨h1, ?_⟩
  unfold WidthPreLabAtC WidthSrcLabAtC
  rw [h2] at hL' hC' ⊢
  revert hL' hC'
  cases cohortEdgeOf root src R e with
  | none => exact fun hL' hC' => Or.inl ⟨σ, hL', hC', hs⟩
  | some k =>
      intro hL' hC'
      rcases preLabStep R m hR _ σ k hs with ⟨hs', _⟩ | ⟨B, _, h0, hpos⟩
      · exact Or.inl ⟨_, hL', hC', hs'⟩
      · by_cases hm : m = 0
        · exact Or.inr (Or.inl ⟨hm, _, hL', hC', h0 hm⟩)
        · exact Or.inr (Or.inr ⟨by omega, _, hL', hC', hpos (by omega)⟩)

/-- `winLabCoupled` with the cut. Consumer: `attemptInvStepC`. -/
theorem widthWinLabCoupledC (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (cut : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (h : WidthCohortLayout ref.toWidthDigitReference root src R x.1 ∧
      WinAligned R (widthLaneOfState ref.toWidthDigitReference root lane src R x) ∧
      WidthWinLabAtC ring ref root lane src R cut x) :
    WidthCohortLayout ref.toWidthDigitReference root src R (widthNxt ring ref x e).1 ∧
      WinAligned R (widthLaneOfState ref.toWidthDigitReference root lane src R (widthNxt ring ref x e)) ∧
      WidthWinLabAtC ring ref root lane src R cut (widthNxt ring ref x e) := by
  obtain ⟨hx, hw, σ, hL, hC, hs⟩ := h
  obtain ⟨h1, hw'⟩ := widthWinAlignedStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hsrc hend hR x e ⟨hx, hw⟩
  obtain ⟨-, h2⟩ := widthLaneLab ring ref hn root lane src R hR hsrc hend x hx e
  refine ⟨h1, hw', _, widthLabelOkStep ring ref hn root lane src R hR hsrc hend x hx σ e hL,
    widthLabelCutStep ring ref hn root lane src R hR hsrc hend cut x hx σ e hC, ?_⟩
  rw [h2]
  cases cohortEdgeOf root src R e with
  | none => exact hs
  | some k => exact winLabStep R hR _ σ k hs hw.2

/-- `widthTrialLabCoupled` with the cut. Consumer: the trial with the cut. -/
theorem widthTrialLabCoupledC (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (cut m : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (h : WidthCohortLayout ref.toWidthDigitReference root src R x.1 ∧ WidthTrialLabAtC ring ref root lane src R cut m x)
    (hnt : ¬ VTAt R m (widthLaneOfState ref.toWidthDigitReference root lane src R x)) :
    WidthCohortLayout ref.toWidthDigitReference root src R (widthNxt ring ref x e).1 ∧
      WidthTrialLabAtC ring ref root lane src R cut m (widthNxt ring ref x e) := by
  obtain ⟨hx, σ, hL, hC, _, ht⟩ := h
  have ht' : LabTrial R m (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ := by
    rcases ht with ht | ht
    · exact ht
    · exact absurd ht hnt
  obtain ⟨h1, h2⟩ := widthLaneLab ring ref hn root lane src R (by omega) hsrc hend x hx e
  have hL' := widthLabelOkStep ring ref hn root lane src R (by omega) hsrc hend x hx σ e hL
  have hC' := widthLabelCutStep ring ref hn root lane src R (by omega) hsrc hend cut x hx σ e hC
  refine ⟨h1, ?_⟩
  unfold WidthTrialLabAtC
  rw [h2] at hL' hC' ⊢
  revert hL' hC'
  cases cohortEdgeOf root src R e with
  | none => exact fun hL' hC' => ⟨σ, hL', hC', labTrialRun ht', Or.inl ht'⟩
  | some k =>
      intro hL' hC'
      rcases labTrialStep R m hR _ σ k ht' with ⟨hv, hr⟩ | ht''
      · exact ⟨_, hL', hC', hr, Or.inr hv⟩
      · exact ⟨_, hL', hC', labTrialRun ht'', Or.inl ht''⟩

/-- **`widthGroupSamples` with the cut**: at the aligned group reached in `WidthTrialLabAtC c (R - 1)`, the
input atom of target cell `R + j` is the recorded sample at `src + j` and is stamped after `c`.
Consumer: the aligned completion with the cut. -/
theorem widthGroupSamplesC (hR : 1 ≤ R) (cut : Nat)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hg : AGroup R (widthLaneOfState ref.toWidthDigitReference root lane src R y))
    (ht : WidthTrialLabAtC ring ref root lane src R cut (R - 1) y) (j : Nat) (hj : j < R) :
    SampledAt ring root lane src R y.2 (laneCells ring root lane src y.2.current (R + j)).input j ∧
      AfterCut cut (laneCells ring root lane src y.2.current (R + j)).input := by
  obtain ⟨σ, hL, hC, hrun, _⟩ := ht
  obtain ⟨hS, hσ⟩ := groupLabels R hR _ σ hg hrun j hj
  have hp : pendIn ((widthLaneOfState ref.toWidthDigitReference root lane src R y).inp (R + j)) = true := by
    revert hS
    cases (widthLaneOfState ref.toWidthDigitReference root lane src R y).inp (R + j) <;> simp [isSI, pendIn]
  exact ⟨hL.2 (R + j) (by omega) (by omega) j hp hσ, hC.2.2 (R + j) (by omega) (by omega) j hp hσ⟩

/-- The trial with the cut forgets to the trial (cut-`0` route). Consumer: the cut-`0`
corollaries. -/
theorem widthTrialLabOfC (cut m : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthTrialLabAtC ring ref root lane src R cut m x) :
    WidthTrialLabAt ring ref root lane src R m x := by
  obtain ⟨σ, hL, -, hr, ht⟩ := h
  exact ⟨σ, hL, hr, ht⟩

end Ported

end L3.WidthPacketMomentCutLabels

#print axioms L3.WidthPacketMomentCutLabels.widthStampAfterCut
#print axioms L3.WidthPacketMomentCutLabels.widthLabelCutStep
#print axioms L3.WidthPacketMomentCutLabels.widthSrcLabCoupledC
#print axioms L3.WidthPacketMomentCutLabels.widthPreLabCoupledC
#print axioms L3.WidthPacketMomentCutLabels.widthWinLabCoupledC
#print axioms L3.WidthPacketMomentCutLabels.widthTrialLabCoupledC
#print axioms L3.WidthPacketMomentCutLabels.widthGroupSamplesC
#print axioms L3.WidthPacketMomentCutLabels.widthTrialLabOfC

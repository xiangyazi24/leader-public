import Leader.L3.Bank.RepairDigitPacketMomentGroupLabels

/-!
# Lemma e-packet with a cut: the labelled samples are taken after the cut

`L3.PacketMomentLabels.LabelOk` ties the position labels of a pair to recorded samples of the
audit. A `DigitCompletion` with cut `c` (Target.lean) asks every sample of the completion to be
stamped after `c`. The comparison lane restarts the observer at the clock `restart` of the writer
value receipts (repair.tex 1743-1749), so its completions carry cut `restart`.

* `AfterCut c a`: if the atom `a` is a sample, it is stamped after `c`.
* `LabelCut c s σ A`: `c ≤ A.clock`, and every labelled source data packet and every labelled
  pending or settled target input carries an atom `AfterCut c` (same labels as `LabelOk`).
  Kept by every coupled letter (`labelCutStep`: the label rows of `L3.PacketMomentLabels` with the
  predicate `AfterCut c`; a read stamps its fresh sample `clock + 1 > c`), and true with no labels
  (`labelCutNone`).
* `SrcLabAtC`, `PreLabAtC`, `WinLabAtC`, `TrialLabAtC`: the coupled label invariants of
  `L3.PacketMomentGroupLabels` with `LabelCut c` for the same labels; kept as there
  (`srcLabCoupledC`, `preLabCoupledC`, `winLabCoupledC`, `trialLabCoupledC`);
  `groupSamplesC`: at the aligned group the input atom of target cell `R + j` is the sample of
  `groupSamples`, stamped after `c`.

The cut-`0` invariants of `L3.PacketMomentGroupLabels` are the projections forgetting `LabelCut`.
-/

namespace L3.PacketMomentCutLabels

set_option autoImplicit false
set_option linter.unusedSimpArgs false

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

/-- **The atom, if a sample, is stamped after the cut.** Consumer: `LabelCut`, `groupSamplesC`. -/
def AfterCut {n : Nat} (cut : Nat) (a : Option (DigitAtom n)) : Prop :=
  ∀ id : DigitStamp n, a = some (.sampled id) → cut < id.time

section Coupled

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat)

/-- **The labelled atoms are stamped after the cut**, and the cut is not ahead of the audit
clock. Consumer: the `C` coupled invariants below. -/
def LabelCut (cut : Nat) (s : CohortLane) (σ : Nat → Option Nat)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  cut ≤ A.clock ∧
    (∀ j, j < R → ∀ T v, s.out j = .D T → σ j = some v →
      AfterCut cut (laneCells ring root lane src A.current j).out.atom) ∧
    (∀ j, R ≤ j → j < 2 * R → ∀ v, pendIn (s.inp j) = true → σ j = some v →
      AfterCut cut (laneCells ring root lane src A.current j).input)

/-- With no labels. Consumer: the start of the labelled phases after the cut. -/
theorem labelCutNone (cut : Nat) (s : CohortLane) (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hc : cut ≤ A.clock) : LabelCut ring root lane src R cut s (fun _ => none) A :=
  ⟨hc, fun _ _ _ _ _ h => by simp at h, fun _ _ _ _ _ h => by simp at h⟩

/-- The fresh sample of a read is stamped `clock + 1`. Consumer: `labelCutStep`. -/
theorem stampAfterCut (cut : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hc : cut ≤ x.2.clock) (k : Nat) :
    AfterCut cut (some (DigitAtom.sampled (stampAt ring hbank root lane src x k))) := by
  intro id hid
  simp only [Option.some.injEq, DigitAtom.sampled.injEq] at hid
  subst hid
  show cut < x.2.clock + 1
  omega

include hn in
/-- **`LabelCut` is kept by every coupled letter.** Consumer: the `C` coupled invariants. -/
theorem labelCutStep (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (cut : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (σ : Nat → Option Nat) (e : Fin n)
    (h : LabelCut ring root lane src R cut (laneOfState ring hbank root lane src R x) σ x.2) :
    LabelCut ring root lane src R cut (laneOfState ring hbank root lane src R (nxt ring hn hbank x e))
      (sigNext R (laneOfState ring hbank root lane src R x) σ (cohortEdgeOf root src R e))
      (nxt ring hn hbank x e).2 := by

  have hls : laneOfState ring hbank root lane src R (nxt ring hn hbank x e) =
      cohortLaneStep R (laneOfState ring hbank root lane src R x) (cohortEdgeOf root src R e) :=
    (laneStep ring hn hbank root lane src R hR hsrc hend x hx e).2
  obtain ⟨hc, hS, hT⟩ := h
  refine ⟨Nat.le_succ_of_le hc, ?_⟩
  rw [hls]
  rcases hE : cohortEdgeOf root src R e with _ | k
  · have hoff := cellsOff ring hn hbank root lane src R hR hsrc hend x hx e hE
    refine ⟨fun j hj T v hD hv => ?_, fun j hj1 hj2 v hp hv => ?_⟩
    · rw [(hoff j (by omega)).1]
      exact (hS j hj T v hD hv)
    · rw [(hoff j (by omega)).2 (by omega)]
      exact (hT j hj1 hj2 v hp hv)
  · obtain ⟨hk, rfl⟩ := edgeOfSome ring root src R e k hE
    simp only [cohortLaneStep, sigNext]
    have far : ∀ q, q < 2 * R → q ≠ k → q ≠ k + 1 →
        laneCells ring root lane src (nxt ring hn hbank x (digitSite ring root (src + k))).2.current
          q = laneCells ring root lane src x.2.current q :=
      fun q hq h1 h2 => cellsFar ring hn hbank root lane src R hend x k hk q hq h1 h2
    by_cases h1 : k + 1 < R
    · -- Pipe edge
      have hout : (cohortEdge R (laneOfState ring hbank root lane src R x) k).out =
          cohortUpd (cohortUpd (laneOfState ring hbank root lane src R x).out k
            (bankRepairDigitPipeStep (decide (k = 0)) ((laneOfState ring hbank root lane src R x).out k)
              ((laneOfState ring hbank root lane src R x).out (k + 1))).1) (k + 1)
            (bankRepairDigitPipeStep (decide (k = 0)) ((laneOfState ring hbank root lane src R x).out k)
              ((laneOfState ring hbank root lane src R x).out (k + 1))).2 := by
        unfold cohortEdge; rw [if_pos h1]
      have hinp : (cohortEdge R (laneOfState ring hbank root lane src R x) k).inp =
          (laneOfState ring hbank root lane src R x).inp := by
        unfold cohortEdge; rw [if_pos h1]
      have hsig : sigStep R (laneOfState ring hbank root lane src R x) σ k =
          sigPipe k ((laneOfState ring hbank root lane src R x).out k)
            ((laneOfState ring hbank root lane src R x).out (k + 1)) σ := by
        unfold sigStep; rw [if_pos h1]
      have hg := cellsPipe ring hn hbank root lane src R hR hsrc hend x hx k h1
      have hg1 := congrArg Prod.fst hg
      have hg2 := congrArg Prod.snd hg
      dsimp only at hg1 hg2
      have hpl := pipeLab (fun a (_ : Nat) => AfterCut cut a) k (stampAt ring hbank root lane src x k)
        (decide (k = 0)) ((laneOfState ring hbank root lane src R x).out k)
        ((laneOfState ring hbank root lane src R x).out (k + 1)) σ
        (laneCells ring root lane src x.2.current k).out
        (laneCells ring root lane src x.2.current (k + 1)).out
        (fun T v hD hv => (hS k (by omega) T v hD hv))
        (fun T v hD hv => (hS (k + 1) h1 T v hD hv))
        (fun _ => stampAfterCut ring hbank root lane src cut x hc k)
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
        have hout : (cohortEdge R (laneOfState ring hbank root lane src R x) k).out =
            cohortUpd (laneOfState ring hbank root lane src R x).out k
              (bankRepairDigitDelStep ((laneOfState ring hbank root lane src R x).out k)
                ((laneOfState ring hbank root lane src R x).inp (k + 1))
                ((laneOfState ring hbank root lane src R x).live (k + 1))).1 := by
          unfold cohortEdge; rw [if_neg h1, if_pos h2]
        have hinp : (cohortEdge R (laneOfState ring hbank root lane src R x) k).inp =
            cohortUpd (laneOfState ring hbank root lane src R x).inp (k + 1)
              (bankRepairDigitDelStep ((laneOfState ring hbank root lane src R x).out k)
                ((laneOfState ring hbank root lane src R x).inp (k + 1))
                ((laneOfState ring hbank root lane src R x).live (k + 1))).2.1 := by
          unfold cohortEdge; rw [if_neg h1, if_pos h2]
        have hsig : sigStep R (laneOfState ring hbank root lane src R x) σ k =
            sigDel k ((laneOfState ring hbank root lane src R x).out k)
              ((laneOfState ring hbank root lane src R x).inp (k + 1))
              ((laneOfState ring hbank root lane src R x).live (k + 1)) σ := by
          unfold sigStep; rw [if_neg h1, if_pos h2]
        obtain ⟨hg, -⟩ := cellsDel ring hn hbank root lane src R hR hsrc hend x hx k h2
        have hg1 := congrArg Prod.fst hg
        have hg2 := congrArg Prod.snd hg
        dsimp only at hg1 hg2
        have hdl := delLab (fun a (_ : Nat) => AfterCut cut a) k (stampAt ring hbank root lane src x k)
          ((laneOfState ring hbank root lane src R x).out k)
          ((laneOfState ring hbank root lane src R x).inp (k + 1))
          ((laneOfState ring hbank root lane src R x).live (k + 1)) σ
          (laneCells ring root lane src x.2.current k).out
          (laneCells ring root lane src x.2.current (k + 1)).input
          (fun T v hD hv => (hS k (by omega) T v hD hv))
          (fun v hp hv => (hT (k + 1) (by omega) (by omega) v hp hv))
          (fun _ => stampAfterCut ring hbank root lane src cut x hc k)
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
          have hout : (cohortEdge R (laneOfState ring hbank root lane src R x) k).out =
              (laneOfState ring hbank root lane src R x).out := by
            unfold cohortEdge; rw [if_neg h1, if_neg h2, if_pos h3]
          have hinp : (cohortEdge R (laneOfState ring hbank root lane src R x) k).inp =
              cohortUpd (cohortUpd (laneOfState ring hbank root lane src R x).inp k
                (bankRepairDigitFinStep (decide (k = R))
                  ((laneOfState ring hbank root lane src R x).inp k)
                  ((laneOfState ring hbank root lane src R x).live k)
                  ((laneOfState ring hbank root lane src R x).inp (k + 1))
                  ((laneOfState ring hbank root lane src R x).live (k + 1))).1) (k + 1)
                (bankRepairDigitFinStep (decide (k = R))
                  ((laneOfState ring hbank root lane src R x).inp k)
                  ((laneOfState ring hbank root lane src R x).live k)
                  ((laneOfState ring hbank root lane src R x).inp (k + 1))
                  ((laneOfState ring hbank root lane src R x).live (k + 1))).2.2.1 := by
            unfold cohortEdge; rw [if_neg h1, if_neg h2, if_pos h3]
          have hsig : sigStep R (laneOfState ring hbank root lane src R x) σ k =
              sigFin k ((laneOfState ring hbank root lane src R x).inp k)
                ((laneOfState ring hbank root lane src R x).live k)
                ((laneOfState ring hbank root lane src R x).inp (k + 1))
                ((laneOfState ring hbank root lane src R x).live (k + 1)) σ := by
            unfold sigStep; rw [if_neg h1, if_neg h2, if_pos h3]
          have hg := cellsFin ring hn hbank root lane src R hR hsrc hend x hx k (by omega) h3
          have hg1 := congrArg Prod.fst hg
          have hg2 := congrArg Prod.snd hg
          dsimp only [ghostFinIn] at hg1 hg2
          have hfl := finLab (fun a (_ : Nat) => AfterCut cut a) k (decide (k = R))
            ((laneOfState ring hbank root lane src R x).inp k)
            ((laneOfState ring hbank root lane src R x).live k)
            ((laneOfState ring hbank root lane src R x).inp (k + 1))
            ((laneOfState ring hbank root lane src R x).live (k + 1)) σ
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
          have hout : (cohortEdge R (laneOfState ring hbank root lane src R x) k).out =
              (laneOfState ring hbank root lane src R x).out := by
            unfold cohortEdge; rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
          have hinp : (cohortEdge R (laneOfState ring hbank root lane src R x) k).inp =
              cohortUpd (laneOfState ring hbank root lane src R x).inp k
                (cohortTermStep ((laneOfState ring hbank root lane src R x).inp k)
                  ((laneOfState ring hbank root lane src R x).live k)).1 := by
            unfold cohortEdge; rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
          have hsig : sigStep R (laneOfState ring hbank root lane src R x) σ k = σ := by
            unfold sigStep; rw [if_neg h1, if_neg h2, if_neg h3]
          have hg := cellsTerm ring hn hbank root lane src R hR hsrc hend x hx k h4
          have htl := termLab (fun a (_ : Nat) => AfterCut cut a) k
            ((laneOfState ring hbank root lane src R x).inp k)
            ((laneOfState ring hbank root lane src R x).live k) σ
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
def SrcLabAtC (cut : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ σ, LabelOk ring root lane src R (laneOfState ring hbank root lane src R x) σ x.2 ∧
    LabelCut ring root lane src R cut (laneOfState ring hbank root lane src R x) σ x.2 ∧
    SrcLab R (laneOfState ring hbank root lane src R x) σ

/-- The labelled distinguished-tail phase after the cut. Consumer: the start of `SrcLabAtC`. -/
def PreLabAtC (cut m : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ σ, LabelOk ring root lane src R (laneOfState ring hbank root lane src R x) σ x.2 ∧
    LabelCut ring root lane src R cut (laneOfState ring hbank root lane src R x) σ x.2 ∧
    PreLab R m (laneOfState ring hbank root lane src R x) σ

/-- The labelled aligned queue after the cut. Consumer: `AttemptInvC`. -/
def WinLabAtC (cut : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ σ, LabelOk ring root lane src R (laneOfState ring hbank root lane src R x) σ x.2 ∧
    LabelCut ring root lane src R cut (laneOfState ring hbank root lane src R x) σ x.2 ∧
    WinLab R (laneOfState ring hbank root lane src R x) σ

/-- The labelled renewal trial after the cut. Consumer: `groupSamplesC`, the trial with the cut. -/
def TrialLabAtC (cut m : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ σ, LabelOk ring root lane src R (laneOfState ring hbank root lane src R x) σ x.2 ∧
    LabelCut ring root lane src R cut (laneOfState ring hbank root lane src R x) σ x.2 ∧
    LabRun R m (laneOfState ring hbank root lane src R x) σ ∧
    (LabTrial R m (laneOfState ring hbank root lane src R x) σ ∨
      VTAt R m (laneOfState ring hbank root lane src R x))

include hn in
/-- `srcLabCoupled` with the cut. Consumer: the phases up to the mobile-free cut. -/
theorem srcLabCoupledC (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (cut : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (h : CohortLayout ring hbank root src R x.1 ∧ SrcLabAtC ring hbank root lane src R cut x) :
    CohortLayout ring hbank root src R (nxt ring hn hbank x e).1 ∧
      SrcLabAtC ring hbank root lane src R cut (nxt ring hn hbank x e) := by
  obtain ⟨hx, σ, hL, hC, hs⟩ := h
  obtain ⟨h1, h2⟩ := laneLab ring hn hbank root lane src R hR hsrc hend x hx e
  refine ⟨h1, _, labelOkStep ring hn hbank root lane src R hR hsrc hend x hx σ e hL,
    labelCutStep ring hn hbank root lane src R hR hsrc hend cut x hx σ e hC, ?_⟩
  rw [h2]
  cases cohortEdgeOf root src R e with
  | none => exact hs
  | some k => exact srcLabStep R hR _ σ k hs

include hn in
/-- `preLabCoupled` with the cut. Consumer: the start of `SrcLabAtC`. -/
theorem preLabCoupledC (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (cut m : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (hx : CohortLayout ring hbank root src R x.1)
    (h : PreLabAtC ring hbank root lane src R cut m x) :
    CohortLayout ring hbank root src R (nxt ring hn hbank x e).1 ∧
      (PreLabAtC ring hbank root lane src R cut m (nxt ring hn hbank x e) ∨
        (m = 0 ∧ SrcLabAtC ring hbank root lane src R cut (nxt ring hn hbank x e)) ∨
        (0 < m ∧ PreLabAtC ring hbank root lane src R cut (m - 1) (nxt ring hn hbank x e))) := by
  obtain ⟨σ, hL, hC, hs⟩ := h
  obtain ⟨h1, h2⟩ := laneLab ring hn hbank root lane src R hR hsrc hend x hx e
  have hL' := labelOkStep ring hn hbank root lane src R hR hsrc hend x hx σ e hL
  have hC' := labelCutStep ring hn hbank root lane src R hR hsrc hend cut x hx σ e hC
  refine ⟨h1, ?_⟩
  unfold PreLabAtC SrcLabAtC
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

include hn in
/-- `winLabCoupled` with the cut. Consumer: `attemptInvStepC`. -/
theorem winLabCoupledC (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (cut : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (h : CohortLayout ring hbank root src R x.1 ∧
      WinAligned R (laneOfState ring hbank root lane src R x) ∧
      WinLabAtC ring hbank root lane src R cut x) :
    CohortLayout ring hbank root src R (nxt ring hn hbank x e).1 ∧
      WinAligned R (laneOfState ring hbank root lane src R (nxt ring hn hbank x e)) ∧
      WinLabAtC ring hbank root lane src R cut (nxt ring hn hbank x e) := by
  obtain ⟨hx, hw, σ, hL, hC, hs⟩ := h
  obtain ⟨h1, hw'⟩ := winAlignedCoupled ring hn hbank root lane src R hR hsrc hend x e ⟨hx, hw⟩
  obtain ⟨-, h2⟩ := laneLab ring hn hbank root lane src R hR hsrc hend x hx e
  refine ⟨h1, hw', _, labelOkStep ring hn hbank root lane src R hR hsrc hend x hx σ e hL,
    labelCutStep ring hn hbank root lane src R hR hsrc hend cut x hx σ e hC, ?_⟩
  rw [h2]
  cases cohortEdgeOf root src R e with
  | none => exact hs
  | some k => exact winLabStep R hR _ σ k hs hw.2

include hn in
/-- `trialLabCoupled` with the cut. Consumer: the trial with the cut. -/
theorem trialLabCoupledC (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (cut m : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (h : CohortLayout ring hbank root src R x.1 ∧ TrialLabAtC ring hbank root lane src R cut m x)
    (hnt : ¬ VTAt R m (laneOfState ring hbank root lane src R x)) :
    CohortLayout ring hbank root src R (nxt ring hn hbank x e).1 ∧
      TrialLabAtC ring hbank root lane src R cut m (nxt ring hn hbank x e) := by
  obtain ⟨hx, σ, hL, hC, _, ht⟩ := h
  have ht' : LabTrial R m (laneOfState ring hbank root lane src R x) σ := by
    rcases ht with ht | ht
    · exact ht
    · exact absurd ht hnt
  obtain ⟨h1, h2⟩ := laneLab ring hn hbank root lane src R (by omega) hsrc hend x hx e
  have hL' := labelOkStep ring hn hbank root lane src R (by omega) hsrc hend x hx σ e hL
  have hC' := labelCutStep ring hn hbank root lane src R (by omega) hsrc hend cut x hx σ e hC
  refine ⟨h1, ?_⟩
  unfold TrialLabAtC
  rw [h2] at hL' hC' ⊢
  revert hL' hC'
  cases cohortEdgeOf root src R e with
  | none => exact fun hL' hC' => ⟨σ, hL', hC', labTrialRun ht', Or.inl ht'⟩
  | some k =>
      intro hL' hC'
      rcases labTrialStep R m hR _ σ k ht' with ⟨hv, hr⟩ | ht''
      · exact ⟨_, hL', hC', hr, Or.inr hv⟩
      · exact ⟨_, hL', hC', labTrialRun ht'', Or.inl ht''⟩

/-- **`groupSamples` with the cut**: at the aligned group reached in `TrialLabAtC c (R - 1)`, the
input atom of target cell `R + j` is the recorded sample at `src + j` and is stamped after `c`.
Consumer: the aligned completion with the cut. -/
theorem groupSamplesC (hR : 1 ≤ R) (cut : Nat)
    (y : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hg : AGroup R (laneOfState ring hbank root lane src R y))
    (ht : TrialLabAtC ring hbank root lane src R cut (R - 1) y) (j : Nat) (hj : j < R) :
    SampledAt ring root lane src R y.2 (laneCells ring root lane src y.2.current (R + j)).input j ∧
      AfterCut cut (laneCells ring root lane src y.2.current (R + j)).input := by
  obtain ⟨σ, hL, hC, hrun, _⟩ := ht
  obtain ⟨hS, hσ⟩ := groupLabels R hR _ σ hg hrun j hj
  have hp : pendIn ((laneOfState ring hbank root lane src R y).inp (R + j)) = true := by
    revert hS
    cases (laneOfState ring hbank root lane src R y).inp (R + j) <;> simp [isSI, pendIn]
  exact ⟨hL.2 (R + j) (by omega) (by omega) j hp hσ, hC.2.2 (R + j) (by omega) (by omega) j hp hσ⟩

/-- The trial with the cut forgets to the trial (cut-`0` route). Consumer: the cut-`0`
corollaries. -/
theorem trialLabOfC (cut m : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : TrialLabAtC ring hbank root lane src R cut m x) :
    TrialLabAt ring hbank root lane src R m x := by
  obtain ⟨σ, hL, -, hr, ht⟩ := h
  exact ⟨σ, hL, hr, ht⟩

end Coupled

end L3.PacketMomentCutLabels

#print axioms L3.PacketMomentCutLabels.labelCutNone
#print axioms L3.PacketMomentCutLabels.stampAfterCut
#print axioms L3.PacketMomentCutLabels.labelCutStep
#print axioms L3.PacketMomentCutLabels.srcLabCoupledC
#print axioms L3.PacketMomentCutLabels.preLabCoupledC
#print axioms L3.PacketMomentCutLabels.winLabCoupledC
#print axioms L3.PacketMomentCutLabels.trialLabCoupledC
#print axioms L3.PacketMomentCutLabels.groupSamplesC
#print axioms L3.PacketMomentCutLabels.trialLabOfC

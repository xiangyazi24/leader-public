import Leader.L3.Bank.RepairDigitPacketMomentLabels
import Leader.L3.Bank.RepairDigitPacketMomentTrialLabels
import Leader.L3.Bank.RepairDigitPacketMomentFinish

/-!
# Lemma e-packet, I1 + I2 on the coupled chain: the aligned group holds the samples `src + j`

The position labels (`L3.PacketMomentSites`, `L3.PacketMomentQueueLabels`,
`L3.PacketMomentTrialLabels`) are ghost data beside the coupled BANK x audit chain; `LabelOk`
(`L3.PacketMomentLabels`) ties them to the recorded samples of the audit. The coupled invariants
here quantify the labels away (`∃ σ, LabelOk ∧ …`), so they are predicates of the coupled
state:

* `SrcLabAt` (labelled aligned source), `PreLabAt m` (distinguished-tail phase), `WinLabAt`
  (labelled aligned queue), kept letter by letter (`srcLabCoupled`, `preLabCoupled`,
  `winLabCoupled`);
* `TrialLabAt m` (labelled renewal trial), kept until the trial target `VTAt m`
  (`trialLabCoupled`);
* `prepLabCut`: phases U and retirement reach the packet-only cut keeping `WinLabAt`, with the
  bound of `prepCutCoupled`; `trialLabMoment`: the trial reaches `VTAt m` in `TrialLabAt m`, with
  the bound of `vMomentAtCoupled`; `prepLabMoment`: both composed;
* `groupSamples`: **at the aligned group (`AGroup`, i.e. `VTAt (R - 1)`) reached in
  `TrialLabAt (R - 1)`, the input atom of target cell `R + j` is a recorded sample of the audit,
  taken at source cell `src + j` on the lane, with tail bit `j = 0`.**
-/

namespace L3.PacketMomentGroupLabels

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open L3
open L3.PacketMoment
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.Correspondence
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

/-- **An invariant kept off the target rides along a first hit.** Consumer: `trialLabMoment`. -/
theorem momentKeepUntil {S : Type} {n : Nat} (next : S → Fin n → S) (Q I : S → Prop)
    (N a b : Nat) (hI : ∀ y e, I y → ¬ Q y → I (next y e)) (x : S) (hx : I x)
    (h : MomentBoundQ next Q N a b x) : MomentBoundQ next (fun y => Q y ∧ I y) N a b x :=
  momentSimQ next next (fun y z => y = z ∧ I y) (fun y => Q y ∧ I y) Q N a b
    (fun y z e hyz hn => by
      obtain ⟨rfl, hy⟩ := hyz
      exact ⟨rfl, hI y e hy (fun hq => hn ⟨hq, hy⟩)⟩)
    (fun y z hyz hg => by
      obtain ⟨rfl, hy⟩ := hyz
      exact ⟨hg, hy⟩) x x ⟨rfl, hx⟩ h

/-- A first hit of a stronger target is a first hit of a weaker one. Consumer: `prepLabMoment`. -/
theorem momentWeaken {S : Type} {n : Nat} (next : S → Fin n → S) (P Q : S → Prop) (N a b : Nat)
    (hPQ : ∀ y, P y → Q y) (x : S) (h : MomentBoundQ next P N a b x) :
    MomentBoundQ next Q N a b x :=
  momentSimQ next next (fun y z => y = z) Q P N a b
    (fun y z e hyz _ => by rw [hyz])
    (fun y z hyz hg => by rw [hyz]; exact hPQ z hg) x x rfl h

/-- Consumer: the coupled trial. -/
theorem labTrialRun {R m : Nat} {s : CohortLane} {σ : Nat → Option Nat} (h : LabTrial R m s σ) :
    LabRun R m s σ := by
  obtain ⟨_, _, _, _, _, _, _, h⟩ := h
  exact h

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat)

/-! ### The coupled label invariants -/

/-- The labelled aligned source. Consumer: the phases up to the mobile-free cut. -/
def SrcLabAt (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    Prop :=
  ∃ σ, LabelOk ring root lane src R (laneOfState ring hbank root lane src R x) σ x.2 ∧
    SrcLab R (laneOfState ring hbank root lane src R x) σ

/-- The labelled distinguished-tail phase. Consumer: the start of `SrcLabAt`. -/
def PreLabAt (m : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ σ, LabelOk ring root lane src R (laneOfState ring hbank root lane src R x) σ x.2 ∧
    PreLab R m (laneOfState ring hbank root lane src R x) σ

/-- The labelled aligned queue. Consumer: `prepLabCut`. -/
def WinLabAt (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    Prop :=
  ∃ σ, LabelOk ring root lane src R (laneOfState ring hbank root lane src R x) σ x.2 ∧
    WinLab R (laneOfState ring hbank root lane src R x) σ

/-- The labelled renewal trial at index `m`, or its target with the settled labels. Consumer:
`trialLabMoment`, `groupSamples`. -/
def TrialLabAt (m : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ σ, LabelOk ring root lane src R (laneOfState ring hbank root lane src R x) σ x.2 ∧
    LabRun R m (laneOfState ring hbank root lane src R x) σ ∧
    (LabTrial R m (laneOfState ring hbank root lane src R x) σ ∨
      VTAt R m (laneOfState ring hbank root lane src R x))

include hn in
/-- The lane and the labels of one coupled letter. Consumer: the coupled keep lemmas. -/
theorem laneLab (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (e : Fin n) :
    CohortLayout ring hbank root src R (nxt ring hn hbank x e).1 ∧
      laneOfState ring hbank root lane src R (nxt ring hn hbank x e) =
        cohortLaneStep R (laneOfState ring hbank root lane src R x) (cohortEdgeOf root src R e) :=
  laneStep ring hn hbank root lane src R hR hsrc hend x hx e

include hn in
/-- **The labelled aligned source on the coupled chain.** Consumer: the phases up to the
mobile-free cut. -/
theorem srcLabCoupled (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (h : CohortLayout ring hbank root src R x.1 ∧ SrcLabAt ring hbank root lane src R x) :
    CohortLayout ring hbank root src R (nxt ring hn hbank x e).1 ∧
      SrcLabAt ring hbank root lane src R (nxt ring hn hbank x e) := by
  obtain ⟨hx, σ, hL, hs⟩ := h
  obtain ⟨h1, h2⟩ := laneLab ring hn hbank root lane src R hR hsrc hend x hx e
  refine ⟨h1, _, labelOkStep ring hn hbank root lane src R hR hsrc hend x hx σ e hL, ?_⟩
  rw [h2]
  cases cohortEdgeOf root src R e with
  | none => exact hs
  | some k => exact srcLabStep R hR _ σ k hs

include hn in
/-- **The labelled distinguished-tail phase on the coupled chain**: kept without an export; an
export shrinks the prefix; the export at the empty prefix starts `SrcLabAt`. Consumer: the start
of `SrcLabAt`. -/
theorem preLabCoupled (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (m : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (hx : CohortLayout ring hbank root src R x.1) (h : PreLabAt ring hbank root lane src R m x) :
    CohortLayout ring hbank root src R (nxt ring hn hbank x e).1 ∧
      (PreLabAt ring hbank root lane src R m (nxt ring hn hbank x e) ∨
        (m = 0 ∧ SrcLabAt ring hbank root lane src R (nxt ring hn hbank x e)) ∨
        (0 < m ∧ PreLabAt ring hbank root lane src R (m - 1) (nxt ring hn hbank x e))) := by
  obtain ⟨σ, hL, hs⟩ := h
  obtain ⟨h1, h2⟩ := laneLab ring hn hbank root lane src R hR hsrc hend x hx e
  have hL' := labelOkStep ring hn hbank root lane src R hR hsrc hend x hx σ e hL
  refine ⟨h1, ?_⟩
  unfold PreLabAt SrcLabAt
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

include hn in
/-- **The labelled aligned queue on the coupled chain** (with the window invariants). Consumer:
`prepLabCut`. -/
theorem winLabCoupled (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (h : CohortLayout ring hbank root src R x.1 ∧
      WinAligned R (laneOfState ring hbank root lane src R x) ∧
      WinLabAt ring hbank root lane src R x) :
    CohortLayout ring hbank root src R (nxt ring hn hbank x e).1 ∧
      WinAligned R (laneOfState ring hbank root lane src R (nxt ring hn hbank x e)) ∧
      WinLabAt ring hbank root lane src R (nxt ring hn hbank x e) := by
  obtain ⟨hx, hw, σ, hL, hs⟩ := h
  obtain ⟨h1, hw'⟩ := winAlignedCoupled ring hn hbank root lane src R hR hsrc hend x e ⟨hx, hw⟩
  obtain ⟨-, h2⟩ := laneLab ring hn hbank root lane src R hR hsrc hend x hx e
  refine ⟨h1, hw', _, labelOkStep ring hn hbank root lane src R hR hsrc hend x hx σ e hL, ?_⟩
  rw [h2]
  cases cohortEdgeOf root src R e with
  | none => exact hs
  | some k => exact winLabStep R hR _ σ k hs hw.2

include hn in
/-- **The labelled renewal trial on the coupled chain**, kept off its target. Consumer:
`trialLabMoment`. -/
theorem trialLabCoupled (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (m : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (h : CohortLayout ring hbank root src R x.1 ∧ TrialLabAt ring hbank root lane src R m x)
    (hnt : ¬ VTAt R m (laneOfState ring hbank root lane src R x)) :
    CohortLayout ring hbank root src R (nxt ring hn hbank x e).1 ∧
      TrialLabAt ring hbank root lane src R m (nxt ring hn hbank x e) := by
  obtain ⟨hx, σ, hL, _, ht⟩ := h
  have ht' : LabTrial R m (laneOfState ring hbank root lane src R x) σ := by
    rcases ht with ht | ht
    · exact ht
    · exact absurd ht hnt
  obtain ⟨h1, h2⟩ := laneLab ring hn hbank root lane src R (by omega) hsrc hend x hx e
  have hL' := labelOkStep ring hn hbank root lane src R (by omega) hsrc hend x hx σ e hL
  refine ⟨h1, ?_⟩
  unfold TrialLabAt
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

include hn in
/-- **Phases U and retirement with labels.** From a layout state with the aligned queue, the
window invariants and the labelled aligned queue, the packet-only cut is reached keeping all of
them, with the bound of `prepCutCoupled`. Consumer: `prepLabMoment`. -/
theorem prepLabCut (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat) (hN : n < N)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1)
    (hs : WinAligned R (laneOfState ring hbank root lane src R x))
    (hl : WinLabAt ring hbank root lane src R x) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => (PacketOnly R (laneOfState ring hbank root lane src R y) ∧
        (CohortLayout ring hbank root src R y.1 ∧
          WinAligned R (laneOfState ring hbank root lane src R y))) ∧
        (CohortLayout ring hbank root src R y.1 ∧
          WinAligned R (laneOfState ring hbank root lane src R y) ∧
          WinLabAt ring hbank root lane src R y)) N
      (N ^ uBudget R * N ^ (2 * R)) ((N - n) ^ uBudget R * (N - n) ^ (2 * R)) x :=
  momentKeep _ _ _ N _ _
    (fun y e h => winLabCoupled ring hn hbank root lane src R (by omega) hsrc hend y e h) x
    ⟨hx, hs, hl⟩ (prepCutCoupled ring hn hbank root lane src R hR hsrc hend N hN x hx hs)

include hn in
/-- **The labelled trial reaches its target with the settled labels**, with the bound of
`vMomentAtCoupled`. Consumer: `prepLabMoment`, the aligned completion. -/
theorem trialLabMoment (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (m : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (σ : Nat → Option Nat)
    (hL : LabelOk ring root lane src R (laneOfState ring hbank root lane src R x) σ x.2)
    (ht : LabTrial R m (laneOfState ring hbank root lane src R x) σ) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => VTAt R m (laneOfState ring hbank root lane src R y) ∧
        (CohortLayout ring hbank root src R y.1 ∧ TrialLabAt ring hbank root lane src R m y)) N
      (N ^ ((R + 2) * vK R)) ((N - n) ^ ((R + 2) * vK R)) x := by
  have hvi : VIAt R m (laneOfState ring hbank root lane src R x) := by
    obtain ⟨a, i, hai, hA, hS, hm, _⟩ := ht
    exact ⟨a, i, hai, hA, hS, hm⟩
  exact momentKeepUntil _ _ _ N _ _
    (fun y e h hnt => trialLabCoupled ring hn hbank root lane src R hR hsrc hend m y e h hnt) x
    ⟨hx, σ, hL, labTrialRun ht, Or.inl ht⟩
    (vMomentAtCoupled ring hn hbank root lane src R hR hsrc hend N hN m x hx hvi)

include hn in
/-- **U, retirement and the renewal trial with labels.** From a layout state with the aligned
queue, the window invariants and the labelled aligned queue, the trial target `VTAt m` is reached
in `TrialLabAt m` for the index `m` of the packet-only cut, with
`E[z^T] ≤ w^{uBudget R + 2R + (R+2)(2R+2)}`. Consumer: the aligned completion
(`groupSamples` at `m = R - 1`), the per-pair moment. -/
theorem prepLabMoment (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1)
    (hs : WinAligned R (laneOfState ring hbank root lane src R x))
    (hl : WinLabAt ring hbank root lane src R x) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => ∃ m, VTAt R m (laneOfState ring hbank root lane src R y) ∧
        CohortLayout ring hbank root src R y.1 ∧ TrialLabAt ring hbank root lane src R m y) N
      (N ^ uBudget R * N ^ (2 * R) * N ^ ((R + 2) * vK R))
      ((N - n) ^ uBudget R * (N - n) ^ (2 * R) * (N - n) ^ ((R + 2) * vK R)) x := by
  refine momentSeq _ _ _ N _ _ _ _ x
    (Nat.pow_le_pow_left (Nat.sub_le N n) _) (fun y hy => ?_)
    (prepLabCut ring hn hbank root lane src R hR hsrc hend N hN x hx hs hl)
  obtain ⟨⟨hP, -⟩, hly, -, σ, hL, a', hA, hLA⟩ := hy
  refine momentWeaken _ _ _ N _ _ (fun z hz => ⟨vIdx R a' 0, hz⟩) y
    (trialLabMoment ring hn hbank root lane src R hR hsrc hend N hN (vIdx R a' 0) y hly σ hL
      (labTrialOfPacketOnly R a' _ σ hA hLA hP))

/-! ### The samples of the aligned group -/

/-- **The aligned group holds the samples `src + j`.** At an aligned group reached in the
labelled trial, the input atom of target cell `R + j` is a recorded sample of the audit taken at
source cell `src + j`, on the lane, with tail bit `j = 0`. Consumer: the aligned completion
(`DigitCompletion` of the group's terminal, I3). -/
theorem groupSamples (hR : 1 ≤ R)
    (y : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hg : AGroup R (laneOfState ring hbank root lane src R y))
    (ht : TrialLabAt ring hbank root lane src R (R - 1) y) (j : Nat) (hj : j < R) :
    SampledAt ring root lane src R y.2 (laneCells ring root lane src y.2.current (R + j)).input j := by
  obtain ⟨σ, hL, hrun, _⟩ := ht
  obtain ⟨hS, hσ⟩ := groupLabels R hR _ σ hg hrun j hj
  refine hL.2 (R + j) (by omega) (by omega) j ?_ hσ
  revert hS
  cases (laneOfState ring hbank root lane src R y).inp (R + j) <;> simp [isSI, pendIn]

end L3.PacketMomentGroupLabels

#print axioms L3.PacketMomentGroupLabels.momentKeepUntil
#print axioms L3.PacketMomentGroupLabels.srcLabCoupled
#print axioms L3.PacketMomentGroupLabels.preLabCoupled
#print axioms L3.PacketMomentGroupLabels.winLabCoupled
#print axioms L3.PacketMomentGroupLabels.trialLabCoupled
#print axioms L3.PacketMomentGroupLabels.prepLabCut
#print axioms L3.PacketMomentGroupLabels.trialLabMoment
#print axioms L3.PacketMomentGroupLabels.prepLabMoment
#print axioms L3.PacketMomentGroupLabels.groupSamples

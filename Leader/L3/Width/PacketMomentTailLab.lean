import Leader.L3.Width.PacketMomentTail
import Leader.L3.Width.PacketMomentCutLabels

/-!
# Lemma e-packet before the first attempt: the labelled distinguished tail, in moment form

The target of the distinguished-tail phase as the per-pair assembly consumes it: the labelled
aligned source `WidthSrcLabAt` (`SrcLab` with `LabelOk`, begun at the export of the distinguished
tail). The labelled path is `preLabOfU` with `labelOkNone` at the first state with `U` at source
cell `0`, then `preLabStep`; it becomes `SrcLab` at the distinguished export.

The potential lives on the coupled chain (the label index is a property of the audit):
`widthLabPot = 0` on the target, otherwise `widthLabIdx · W + tailG + 1`, where `widthLabIdx` is the
least labelled prefix index `m` (`WidthPreLabAtC c m`) once the labels have started, and the whole
owed word before (`srcWord`). The within-export part `tailG` and its nominated edges are those of
`L3.WidthPacketMomentTail` (release edge while the border is occupied, head edge while it is free).
New facts: `wordAny` (a letter that exports nothing does not lengthen the owed word, unless it writes
`U` into source cell `0`, where the labels start with the old word as prefix), `widthPreLabExport`
(the coupled labelled step with the export information), `widthLabIdxStep`.

`widthTailLabMoment`: with a cut `c` (labels stamped after `c`; `c = 0` the plain stage, `c =
restart` the comparison lane), from every layout state with clock `≥ c`, `E[z^T] ≤ w^{tailBudget R}`
to `WidthSrcLabAtC c` (with the layout), `tailBudget R = (R² + 1) · 2(R+1)²`, at every `WidthBoundaryReference`;
`bankTailLabMomentCheck` is the BANK instance.
-/

namespace L3.WidthPacketMomentTailLab

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open Classical
open K2ArbitraryElimination.FiniteAccounting
open L3
open L3.PairMoment
open L3.PacketMoment
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.WidthDigit
open L3.DigitPacketRelease
open L3.DigitPacketTransport
open L3.PacketMomentRelease
open L3.PacketMomentAlign
open L3.PacketMomentPrep
open L3.PacketMomentLabels
open L3.PacketMomentTrialLabels
open L3.PacketMomentGroupLabels
open L3.WidthWave
open L3.WidthPacketMoment
open L3.WidthPacketMomentTail
open L3.WidthPacketMomentAudit
open L3.PacketMomentCutLabels
open L3.WidthPacketMomentCutLabels

/-! ### The owed word on any letter -/

/-- `Pre m` bounds `m` by the owed word. Consumer: `widthLabIdxWord`. -/
theorem preLen (R m : Nat) (out : Nat → BankRepairDigitOutSh) (h : Pre R m out) :
    m ≤ (srcWord R out).length := by
  obtain ⟨_, Y, c, hY, hw⟩ := h
  have h1 := congrArg List.length hw
  rw [List.length_append] at h1
  omega

/-- **A letter that exports nothing** does not lengthen the owed word, or it writes `U` into
source cell `0` and the owed word of cells `1, ..., R-1` is at most the old owed word.
Consumer: `widthLabIdxStep`. -/
theorem wordAny (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (k : Nat)
    (hne : ∀ B, ¬ Exported R s k B) :
    (srcWord R (cohortEdge R s k).out).length ≤ (srcWord R s.out).length ∨
      ((cohortEdge R s k).out 0 = .U ∧
        (wSeg R (cohortEdge R s k).out 1 (R - 1)).length ≤ (srcWord R s.out).length) := by
  by_cases hc : CZero s.out
  · rcases srcStep R hR s k hc with ⟨he, _⟩ | ⟨hk0, he⟩ | ⟨B, hex, _⟩
    · left; exact Nat.le_of_eq (congrArg List.length he)
    · right
      subst hk0
      have hc' := c0Step R hR s 0 hc
      have h1 := wordCZero R (by omega) _ hc'
      rw [he] at h1
      have hseg : wSeg R (cohortEdge R s 0).out 1 (R - 1) = srcWord R s.out :=
        (List.append_cancel_right h1).symm
      refine ⟨?_, by rw [hseg]; exact Nat.le_refl _⟩
      rcases hc' with h0 | h0
      · exact h0
      · exfalso
        have hout : (cohortEdge R s 0).out =
            cohortUpd (cohortUpd s.out 0 (bankRepairDigitPipeStep (decide (0 = 0)) (s.out 0)
              (s.out (0 + 1))).1) (0 + 1)
              (bankRepairDigitPipeStep (decide (0 = 0)) (s.out 0) (s.out (0 + 1))).2 := by
          unfold cohortEdge; rw [if_pos (by omega)]
        have h0' : (bankRepairDigitPipeStep (decide (0 = 0)) (s.out 0) (s.out (0 + 1))).1 =
            .D true := by
          have h2 := h0
          rw [hout] at h2
          simpa [cohortUpd] using h2
        have hy : (bankRepairDigitPipeStep (decide (0 = 0)) (s.out 0) (s.out (0 + 1))).2 =
            s.out (0 + 1) := by
          revert h0' hc
          unfold CZero
          rcases s.out 0 with _ | _ | ⟨_ | _⟩ <;> rcases s.out (0 + 1) with _ | _ | ⟨_ | _⟩ <;>
            simp [bankRepairDigitPipeStep]
        have hpt : ∀ j, 1 ≤ j → (cohortEdge R s 0).out j = s.out j := by
          intro j hj
          rw [hout]
          by_cases hj1 : j = 0 + 1
          · subst hj1
            simpa [cohortUpd] using hy
          · simp [cohortUpd, hj1, show j ≠ 0 by omega]
        have hs1 : wSeg R (cohortEdge R s 0).out 1 (R - 1) = wSeg R s.out 1 (R - 1) :=
          wSegCongr R _ _ 1 (R - 1) (fun j hj _ => hpt j hj)
        have hw1 := wordCZero R (by omega) s.out hc
        rw [hs1, hw1] at hseg
        have h3 := congrArg List.length hseg
        simp [blk] at h3 <;> omega
    · exact absurd hex (hne B)
  · rcases freeWord R hR s k hc hne with he | ⟨h0, hl⟩
    · left; exact Nat.le_of_eq (congrArg List.length he)
    · right; exact ⟨h0, hl⟩

section Coupled

variable {n : Nat} (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
  (root : Fin n) (lane : DigitLane) (src R cut : Nat)

/-! ### The labelled index -/

/-- The labels of the distinguished-tail phase have started. Consumer: `widthLabIdx`. -/
def WidthLabbed (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ m, WidthPreLabAtC ring ref root lane src R cut m y

/-- **Exports owed before the labelled distinguished tail**: the least labelled prefix index once
the labels have started, the whole owed word before. Consumer: `widthLabPot`. -/
noncomputable def widthLabIdx (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    Nat :=
  if WidthLabbed ring ref root lane src R cut y then
    leastUpTo (fun m => WidthPreLabAtC ring ref root lane src R cut m y) (R * R)
  else (srcWord R (widthLaneOfState ref.toWidthDigitReference root lane src R y).out).length

/-- **The labelled distinguished-tail potential.** Consumer: `widthTailLabMoment`. -/
noncomputable def widthLabPot (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    Nat :=
  if WidthSrcLabAtC ring ref root lane src R cut y then 0
  else widthLabIdx ring ref root lane src R cut y * tailW R +
    tailG R (widthLaneOfState ref.toWidthDigitReference root lane src R y) + 1

/-- A labelled prefix index is below the owed word. Consumer: `widthLabIdxLe`. -/
theorem widthPreLabLen (m : Nat) (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthPreLabAtC ring ref root lane src R cut m y) :
    m ≤ (srcWord R (widthLaneOfState ref.toWidthDigitReference root lane src R y).out).length := by
  obtain ⟨_, _, _, hP, _⟩ := h
  exact preLen R m _ hP

/-- The index is below every labelled prefix index. Consumer: `widthLabIdxStep`. -/
theorem widthLabIdxLe (hR : 1 ≤ R) (m : Nat)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthPreLabAtC ring ref root lane src R cut m y) : widthLabIdx ring ref root lane src R cut y ≤ m := by
  have hm := Nat.le_trans (widthPreLabLen ring ref root lane src R cut m y h)
    (srcWordLen R hR _)
  unfold widthLabIdx
  rw [if_pos ⟨m, h⟩]
  exact (leastUpToSpec (fun m => WidthPreLabAtC ring ref root lane src R cut m y) (R * R) m hm h).1

/-- At started labels the index is a labelled prefix index. Consumer: `widthLabIdxStep`. -/
theorem widthLabIdxSpec (hR : 1 ≤ R)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthLabbed ring ref root lane src R cut y) :
    WidthPreLabAtC ring ref root lane src R cut (widthLabIdx ring ref root lane src R cut y) y := by
  obtain ⟨m, hm⟩ := h
  have hb := Nat.le_trans (widthPreLabLen ring ref root lane src R cut m y hm) (srcWordLen R hR _)
  unfold widthLabIdx
  rw [if_pos ⟨m, hm⟩]
  exact (leastUpToSpec (fun m => WidthPreLabAtC ring ref root lane src R cut m y) (R * R) m hb hm).2

/-- The index is below the owed word. Consumer: `widthLabIdxStep`, `widthLabPotLe`. -/
theorem widthLabIdxWord (hR : 1 ≤ R)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    widthLabIdx ring ref root lane src R cut y ≤
      (srcWord R (widthLaneOfState ref.toWidthDigitReference root lane src R y).out).length := by
  by_cases h : WidthLabbed ring ref root lane src R cut y
  · exact Nat.le_trans (widthLabIdxLe ring ref root lane src R cut hR _ y
      (widthLabIdxSpec ring ref root lane src R cut hR y h))
      (widthPreLabLen ring ref root lane src R cut _ y (widthLabIdxSpec ring ref root lane src R cut hR y h))
  · unfold widthLabIdx
    rw [if_neg h]
    exact Nat.le_refl _

/-- The potential is within the budget. Consumer: `widthTailLabMoment`. -/
theorem widthLabPotLe (hR : 1 ≤ R) (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    widthLabPot ring ref root lane src R cut y ≤ tailBudget R := by
  unfold widthLabPot
  split
  · exact Nat.zero_le _
  · have h1 : widthLabIdx ring ref root lane src R cut y * tailW R ≤ R * R * tailW R :=
      Nat.mul_le_mul_right _ (Nat.le_trans (widthLabIdxWord ring ref root lane src R cut hR y)
        (srcWordLen R hR _))
    have h2 : (R * R + 1) * tailW R = R * R * tailW R + tailW R := Nat.succ_mul _ _
    have h3 := tailGLe R (widthLaneOfState ref.toWidthDigitReference root lane src R y)
    unfold tailBudget
    omega

include hn

/-- **The labelled step with the export information**: kept without an export of the lane
letter; at an export the prefix shrinks, and the export at the empty prefix starts
`WidthSrcLabAt`. Consumer: `widthLabIdxStep`. -/
theorem widthPreLabExport (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (m : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1)
    (h : WidthPreLabAtC ring ref root lane src R cut m x) :
    (WidthPreLabAtC ring ref root lane src R cut m (widthNxt ring ref x e) ∧
        ∀ k, cohortEdgeOf root src R e = some k →
          ∀ B, ¬ Exported R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k B) ∨
      ((m = 0 → WidthSrcLabAtC ring ref root lane src R cut (widthNxt ring ref x e)) ∧
        (0 < m → WidthPreLabAtC ring ref root lane src R cut (m - 1) (widthNxt ring ref x e))) := by
  obtain ⟨σ, hL, hC, hs⟩ := h
  obtain ⟨_, h2⟩ := widthLaneLab ring ref hn root lane src R hR hsrc hend x hx e
  have hL' := widthLabelOkStep ring ref hn root lane src R hR hsrc hend x hx σ e hL
  have hC' := widthLabelCutStep ring ref hn root lane src R hR hsrc hend cut x hx σ e hC
  unfold WidthPreLabAtC WidthSrcLabAtC
  rw [h2] at hL' hC' ⊢
  revert hL' hC'
  cases hE : cohortEdgeOf root src R e with
  | none => exact fun hL' hC' => Or.inl ⟨⟨σ, hL', hC', hs⟩, fun k hk => by cases hk⟩
  | some k =>
      intro hL' hC'
      rcases preLabStep R m hR _ σ k hs with ⟨hs', hne⟩ | ⟨B, _, h0, hpos⟩
      · exact Or.inl ⟨⟨_, hL', hC', hs'⟩, fun k' hk' => by cases hk'; exact hne⟩
      · exact Or.inr ⟨fun hm => ⟨_, hL', hC', h0 hm⟩, fun hm => ⟨_, hL', hC', hpos hm⟩⟩

/-- **The labelled index never rises, and every export before the target lowers it**, or the
letter reaches `WidthSrcLabAt`. Consumer: `widthLabPotMono`, `widthLabPotDrop`. -/
theorem widthLabIdxStep (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (hclk : cut ≤ x.2.clock) :
    WidthSrcLabAtC ring ref root lane src R cut (widthNxt ring ref x e) ∨
      (widthLabIdx ring ref root lane src R cut (widthNxt ring ref x e) ≤
          widthLabIdx ring ref root lane src R cut x ∧
        ∀ k B, cohortEdgeOf root src R e = some k →
          Exported R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k B →
          widthLabIdx ring ref root lane src R cut (widthNxt ring ref x e) + 1 ≤
            widthLabIdx ring ref root lane src R cut x) := by
  by_cases hlab : WidthLabbed ring ref root lane src R cut x
  · have hP := widthLabIdxSpec ring ref root lane src R cut (by omega) x hlab
    generalize hm : widthLabIdx ring ref root lane src R cut x = m0 at hP
    rcases widthPreLabExport ring ref hn root lane src R cut hR hsrc hend m0 x e hx hP with
      ⟨hP', hne⟩ | ⟨h0, hpos⟩
    · right
      exact ⟨widthLabIdxLe ring ref root lane src R cut (by omega) m0 _ hP',
        fun k B hk hB => absurd hB (hne k hk B)⟩
    · by_cases hm0 : m0 = 0
      · exact Or.inl (h0 hm0)
      · have h3 := widthLabIdxLe ring ref root lane src R cut (by omega) (m0 - 1) _
          (hpos (by omega))
        right
        exact ⟨by omega, fun _ _ _ _ => by omega⟩
  · right
    have ht : widthLabIdx ring ref root lane src R cut x =
        (srcWord R (widthLaneOfState ref.toWidthDigitReference root lane src R x).out).length := by
      unfold widthLabIdx; rw [if_neg hlab]
    rw [ht]
    have hw' := widthLabIdxWord ring ref root lane src R cut (by omega) (widthNxt ring ref x e)
    obtain ⟨_, h2⟩ := widthLaneLab ring ref hn root lane src R hR hsrc hend x hx e
    rw [h2] at hw'
    revert hw'
    cases hE : cohortEdgeOf root src R e with
    | none =>
        intro hw'
        exact ⟨hw', fun k B hk _ => by cases hk⟩
    | some k =>
        intro hw'
        by_cases hex : ∃ B, Exported R (widthLaneOfState ref.toWidthDigitReference root lane src R x)
            k B
        · obtain ⟨B, hB⟩ := hex
          have h3 := congrArg List.length (exportWord R hR _ k B hB)
          simp only [List.length_cons] at h3
          have hw'' : widthLabIdx ring ref root lane src R cut (widthNxt ring ref x e) ≤
              (srcWord R (cohortEdge R (widthLaneOfState ref.toWidthDigitReference root lane src R x)
                k).out).length := hw'
          exact ⟨by omega, fun _ _ _ _ => by omega⟩
        · have hne : ∀ B, ¬ Exported R (widthLaneOfState ref.toWidthDigitReference root lane src R x)
              k B := fun B hB => hex ⟨B, hB⟩
          refine ⟨?_, fun k' B hk' hB => by cases hk'; exact absurd hB (hne B)⟩
          rcases wordAny R hR _ k hne with hl | ⟨h0, hl⟩
          · exact Nat.le_trans hw' hl
          · have hpre : WidthPreLabAtC ring ref root lane src R cut
                (wSeg R (cohortEdge R (widthLaneOfState ref.toWidthDigitReference root lane src R x)
                  k).out 1 (R - 1)).length (widthNxt ring ref x e) := by
              have hclk' : cut ≤ (widthNxt ring ref x e).2.clock :=
                (widthLabelCutStep ring ref hn root lane src R hR hsrc hend cut x hx (fun _ => none) e
                  (labelCutNone ring root lane src R cut _ _ hclk)).1
              refine ⟨fun _ => none, ?_, ?_, ?_⟩
              · rw [h2, hE]
                exact labelOkNone ring root lane src R _ _
              · rw [h2, hE]
                exact labelCutNone ring root lane src R cut _ _ hclk'
              · rw [h2, hE]
                exact preLabOfU R (by omega) _ _ h0
            exact Nat.le_trans (widthLabIdxLe ring ref root lane src R cut (by omega) _ _ hpre) hl

/-- The lane of the next state, and the export of its letter. Consumer: `widthLabPotMono`,
`widthLabPotDrop`. -/
theorem widthLabGStep (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1)
    (hne : ∀ k B, cohortEdgeOf root src R e = some k →
      ¬ Exported R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k B) :
    tailG R (widthLaneOfState ref.toWidthDigitReference root lane src R (widthNxt ring ref x e)) ≤
      tailG R (widthLaneOfState ref.toWidthDigitReference root lane src R x) := by
  obtain ⟨_, h2⟩ := widthLaneLab ring ref hn root lane src R hR hsrc hend x hx e
  rw [h2]
  revert hne
  cases cohortEdgeOf root src R e with
  | none => exact fun _ => Nat.le_refl _
  | some k => exact fun hne => tailGStep R hR _ k (fun B => hne k B rfl)

/-- **No letter raises the potential before the target.** Consumer: `widthTailLabMoment`. -/
theorem widthLabPotMono (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (hclk : cut ≤ x.2.clock)
    (hna : ¬ WidthSrcLabAtC ring ref root lane src R cut x) :
    widthLabPot ring ref root lane src R cut (widthNxt ring ref x e) ≤
      widthLabPot ring ref root lane src R cut x := by
  have hx0 : widthLabPot ring ref root lane src R cut x =
      widthLabIdx ring ref root lane src R cut x * tailW R +
        tailG R (widthLaneOfState ref.toWidthDigitReference root lane src R x) + 1 := by
    unfold widthLabPot; rw [if_neg hna]
  rw [hx0]
  unfold widthLabPot
  split
  · exact Nat.zero_le _
  · next hna' =>
    rcases widthLabIdxStep ring ref hn root lane src R cut hR hsrc hend x e hx hclk with h | ⟨h1, h2⟩
    · exact absurd h hna'
    · by_cases hex : ∃ k B, cohortEdgeOf root src R e = some k ∧
          Exported R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k B
      · obtain ⟨k, B, hk, hB⟩ := hex
        have h3 := h2 k B hk hB
        have h4 := Nat.mul_le_mul_right (tailW R) h3
        rw [Nat.succ_mul] at h4
        have h5 := tailGLe R (widthLaneOfState ref.toWidthDigitReference root lane src R
          (widthNxt ring ref x e))
        omega
      · have hne : ∀ k B, cohortEdgeOf root src R e = some k →
            ¬ Exported R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k B :=
          fun k B hk hB => hex ⟨k, B, hk, hB⟩
        have h4 := Nat.mul_le_mul_right (tailW R) h1
        have h5 := widthLabGStep ring ref hn root lane src R hR hsrc hend x e hx hne
        omega

/-- **A nominated letter lowers the potential before the target**: the release edge while the
border is occupied, the head edge while it is free. Consumer: `widthTailLabMoment`. -/
theorem widthLabPotDrop (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (hclk : cut ≤ x.2.clock)
    (hna : ¬ WidthSrcLabAtC ring ref root lane src R cut x) :
    ∃ e : Fin n, widthLabPot ring ref root lane src R cut (widthNxt ring ref x e) + 1 ≤
      widthLabPot ring ref root lane src R cut x := by
  have hx0 : widthLabPot ring ref root lane src R cut x =
      widthLabIdx ring ref root lane src R cut x * tailW R +
        tailG R (widthLaneOfState ref.toWidthDigitReference root lane src R x) + 1 := by
    unfold widthLabPot; rw [if_neg hna]
  -- a lane edge `k < 2R` whose letter exports or lowers `tailG`
  have hk : ∃ k, k < 2 * R ∧
      ((∃ B, Exported R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k B) ∨
        tailG R (cohortEdge R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k) + 1 ≤
          tailG R (widthLaneOfState ref.toWidthDigitReference root lane src R x)) := by
    generalize widthLaneOfState ref.toWidthDigitReference root lane src R x = s
    by_cases hb : BorderFree R s
    · obtain ⟨k, hk, hd⟩ := headDrop R hR s hb
      refine ⟨k, by omega, ?_⟩
      by_cases hex : ∃ B, Exported R s k B
      · exact Or.inl hex
      · have hne : ∀ B, ¬ Exported R s k B := fun B hB => hex ⟨B, hB⟩
        rcases hd with ⟨B, hB⟩ | hd
        · exact absurd hB (hne B)
        · right
          unfold tailG
          rw [if_pos hb, if_pos (borderKeep R hR s k hb hne)]
          exact hd
    · obtain ⟨k, hk, hd⟩ := edgeDrop R s hR hb
      refine ⟨k, hk, Or.inr ?_⟩
      have h2 : tailG R (cohortEdge R s k) ≤ 2 * R + 1 + releaseWeight R (cohortEdge R s k) := by
        unfold tailG
        split
        · have := headMinLeTwiceR R (cohortEdge R s k).out R
          unfold headPot
          omega
        · exact Nat.le_refl _
      have h3 : tailG R s = 2 * R + 1 + releaseWeight R s := by
        unfold tailG; rw [if_neg hb]
      omega
  obtain ⟨k, hk, hd⟩ := hk
  refine ⟨digitSite ring root (src + k), ?_⟩
  have hE := cohortEdgeOfSite ring root src R hend k hk
  rw [hx0]
  unfold widthLabPot
  split
  · omega
  · next hna' =>
    rcases widthLabIdxStep ring ref hn root lane src R cut hR hsrc hend x _ hx hclk with h | ⟨h1, h2⟩
    · exact absurd h hna'
    · rcases hd with ⟨B, hB⟩ | hd
      · have h3 := h2 k B hE hB
        have h4 := Nat.mul_le_mul_right (tailW R) h3
        rw [Nat.succ_mul] at h4
        have h5 := tailGLe R (widthLaneOfState ref.toWidthDigitReference root lane src R
          (widthNxt ring ref x (digitSite ring root (src + k))))
        omega
      · have h4 := Nat.mul_le_mul_right (tailW R) h1
        obtain ⟨_, hl⟩ := widthLaneLab ring ref hn root lane src R hR hsrc hend x hx
          (digitSite ring root (src + k))
        have h5 : tailG R (widthLaneOfState ref.toWidthDigitReference root lane src R
            (widthNxt ring ref x (digitSite ring root (src + k)))) =
            tailG R (cohortEdge R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k) := by
          rw [hl, hE]; rfl
        omega

/-- **The labelled distinguished-tail phase in moment form at a boundary reference, with a
cut.** From every layout state of the pair whose audit clock is at least `cut`, the labelled
aligned source with the cut `WidthSrcLabAtC cut` (begun at the export of the distinguished tail,
with labels that are the audit's samples, stamped after `cut`) is reached with the layout,
`E[z^T] ≤ w^{tailBudget R}`, `tailBudget R = (R² + 1) · 2(R+1)² ≤ C_R` (`tailBudgetLe`),
`w = N/(N-n)`, uniformly over source values and the audit; every release before the distinguished
export is included. `cut = 0` is the plain stage (`BankPairStageW`, `SrcLabAt` is the projection
forgetting `LabelCut`), `cut = restart` the comparison lane (`CmpPairStageW`). Consumer: the
pre-attempt stage obligation of the per-pair moment (BANK and SMALL, both lanes). -/
theorem widthTailLabMoment (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (hc : cut ≤ x.2.clock) :
    MomentBoundQ (widthDigitAuditNext ref.toWidthDigitReference)
      (fun y => WidthSrcLabAtC ring ref root lane src R cut y ∧
        WidthCohortLayout ref.toWidthDigitReference root src R y.1) N
      (N ^ tailBudget R) ((N - n) ^ tailBudget R) x := by
  let L : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n → Prop :=
    fun y => WidthCohortLayout ref.toWidthDigitReference root src R y.1 ∧ cut ≤ y.2.clock
  let P : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n → Prop :=
    fun y => WidthSrcLabAtC ring ref root lane src R cut y ∨ ¬ L y
  have hex : ∀ y, ∃ e : Fin n, ¬ P y →
      widthLabPot ring ref root lane src R cut (widthNxt ring ref y e) + 1 ≤
        widthLabPot ring ref root lane src R cut y := by
    intro y
    by_cases hP : P y
    · exact ⟨⟨0, by omega⟩, fun h => absurd hP h⟩
    · have hl : L y := Classical.byContradiction fun h => hP (Or.inr h)
      have hs : ¬ WidthSrcLabAtC ring ref root lane src R cut y := fun h => hP (Or.inl h)
      obtain ⟨e, he⟩ := widthLabPotDrop ring ref hn root lane src R cut hR hsrc hend y hl.1 hl.2 hs
      exact ⟨e, fun _ => he⟩
  have h0 := momentOfPotential (widthDigitAuditNext ref.toWidthDigitReference) P N
    (widthLabPot ring ref root lane src R cut) (fun y => Classical.choose (hex y)) (by omega)
    (Nat.le_of_lt hN) (fun y hy => Classical.choose_spec (hex y) hy)
    (fun y hy e => by
      have hl : L y := Classical.byContradiction fun h => hy (Or.inr h)
      have hs : ¬ WidthSrcLabAtC ring ref root lane src R cut y := fun h => hy (Or.inl h)
      exact widthLabPotMono ring ref hn root lane src R cut hR hsrc hend y e hl.1 hl.2 hs) x
  have h1 := momentKeep (widthDigitAuditNext ref.toWidthDigitReference) P L N _ _
    (fun y e hy => ⟨(widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hR
      hsrc hend y hy.1 e).1,
      (widthLabelCutStep ring ref hn root lane src R hR hsrc hend cut y hy.1 (fun _ => none) e
        (labelCutNone ring root lane src R cut _ _ hy.2)).1⟩) x ⟨hx, hc⟩ h0
  have h2 := momentWeaken (widthDigitAuditNext ref.toWidthDigitReference) _
    (fun y => WidthSrcLabAtC ring ref root lane src R cut y ∧
      WidthCohortLayout ref.toWidthDigitReference root src R y.1) N _ _
    (fun y hy => ⟨hy.1.resolve_right (fun h => h hy.2), hy.2.1⟩) x h1
  refine momentQCross _ _ N _ _ _ _ x (Nat.pow_pos (by omega)) ?_ h2
  exact powCross N n _ _ (widthLabPotLe ring ref root lane src R cut (by omega) x)

end Coupled

/-- **Port check**: the BANK instance of `widthTailLabMoment` (`bankWidthBoundaryReference`),
read on the BANK lane and the BANK labels with the cut. Consumer: none in the chain; it checks the
port. -/
theorem bankTailLabMomentCheck {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R cut : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (hc : cut ≤ x.2.clock) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => SrcLabAtC ring hbank root lane src R cut y ∧ CohortLayout ring hbank root src R y.1)
      N (N ^ tailBudget R) ((N - n) ^ tailBudget R) x :=
  widthTailLabMoment ring (bankWidthBoundaryReference ring hn hbank) hn root lane src R cut hR hsrc
    hend N hN x hx hc

end L3.WidthPacketMomentTailLab

#print axioms L3.WidthPacketMomentTailLab.wordAny
#print axioms L3.WidthPacketMomentTailLab.widthPreLabExport
#print axioms L3.WidthPacketMomentTailLab.widthLabIdxStep
#print axioms L3.WidthPacketMomentTailLab.widthLabPotMono
#print axioms L3.WidthPacketMomentTailLab.widthLabPotDrop
#print axioms L3.WidthPacketMomentTailLab.widthTailLabMoment
#print axioms L3.WidthPacketMomentTailLab.bankTailLabMomentCheck

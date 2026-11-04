import Leader.L3.Bank.RepairDigitPacketMomentSites
import Leader.L3.Bank.RepairDigitPacketMomentCells

/-!
# Lemma e-packet, I1: the position labels are the audit's recorded samples

repair.tex, Lemma e-packet: "After this tail exports, exclusion and its rearms force each
subsequent group's export origins to be `r-1, …, 0`."

`L3.PacketMomentSites` tracks a position label `σ j` (`Option Nat`) beside each lane cell and
proves that, once aligned, the source exports the labels `a, a - 1, …, 0, R - 1, …` in turn
(`siteAlignStep`). This module ties the labels to the audit ghosts of the coupled BANK x audit
chain: `LabelOk` says that every labelled data packet of the source (an output `D`) and every
labelled pending or settled target input (`P`, `S`) carries, as its ghost atom, a **recorded
sample of the audit taken at the source cell `src + v`** of its label `v`, on the lane, with tail
bit `v = 0` (`SampledAt`).

* `pipeLab`, `delLab`, `finLab`, `termLab`: the label rows `sigPipe` / `sigDel` / `sigFin` keep
  the predicate across the ghost rows `ghostPipe` / `ghostDel` / `ghostFinIn` / `ghostTermIn`
  (pure, any predicate `Q` on atoms and labels);
* `labelOkStep`: `LabelOk` is kept by every coupled letter (`L3.PacketMomentCells` plumbing, and
  `cellsRead` for the fresh sample of a read);
* `labAlignCoupled`, `labPreCoupled`: on the coupled chain, `SiteAlign a ∧ LabelOk` is kept by every
  letter without an export, and **an export delivers into the border input a recorded sample
  taken at source cell `src + a`** (tail bit `a = 0`), after which the index is `a - 1` (or
  `R - 1`); before alignment (`SitePre m`), the export at the empty prefix is the distinguished
  tail, a recorded sample at `src + 0` with tail bit set.

Initially (`σ = fun _ => none`) `LabelOk` holds vacuously (`labelOkNone`).
-/

namespace L3.PacketMomentLabels

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open L3
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.Correspondence
open L3.GhostBridge
open L3.WidthDigit
open L3.DigitPacketTransport
open L3.PacketMomentAlign
open L3.PacketMomentSites
open L3.PacketMomentCells

/-- A target input shape that holds a packet: pending or settled. Consumer: `LabelOk`. -/
def pendIn : BankRepairDigitInSh → Bool
  | .P _ => true
  | .S _ => true
  | _ => false

theorem updAt {α : Type} (f : Nat → α) (a : Nat) (v : α) : cohortUpd f a v a = v := by
  simp [cohortUpd]

theorem updNe {α : Type} (f : Nat → α) (a : Nat) (v : α) (j : Nat) (h : j ≠ a) :
    cohortUpd f a v j = f j := by
  simp [cohortUpd, h]

/-! ### The label rows keep any atom predicate -/

section Pure

variable {n : Nat} (Q : Option (DigitAtom n) → Nat → Prop)

/-- **Pipe edge.** Consumer: `labelOkStep`. -/
theorem pipeLab (k : Nat) (stamp : DigitStamp n) (bx : Bool) (ox oy : BankRepairDigitOutSh)
    (σ : Nat → Option Nat) (gx gy : DigitOutGhost n)
    (hx : ∀ T v, ox = .D T → σ k = some v → Q gx.atom v)
    (hy : ∀ T v, oy = .D T → σ (k + 1) = some v → Q gy.atom v)
    (hf : ox = .U → Q (some (.sampled stamp)) k) :
    (∀ T v, (bankRepairDigitPipeStep bx ox oy).1 = .D T → sigPipe k ox oy σ k = some v →
        Q (ghostPipe stamp bx ox oy gx gy).1.atom v) ∧
      (∀ T v, (bankRepairDigitPipeStep bx ox oy).2 = .D T → sigPipe k ox oy σ (k + 1) = some v →
        Q (ghostPipe stamp bx ox oy gx gy).2.atom v) := by
  have hk1 : k ≠ k + 1 := by omega
  refine ⟨fun T v hD hv => ?_, fun T v hD hv => ?_⟩ <;>
  rcases ox with _ | _ | ⟨_ | _⟩ <;> rcases oy with _ | _ | ⟨_ | _⟩ <;> cases bx <;>
  simp [bankRepairDigitPipeStep, sigPipe, ghostPipe, DigitOutGhost.atom, cohortUpd, hk1,
    hk1.symm] at hD hv ⊢ <;>
  first
  | exact hx _ _ rfl hv
  | exact hy _ _ rfl hv
  | (subst hv; exact hf rfl)

/-- **Delivery edge.** Consumer: `labelOkStep`. -/
theorem delLab (k : Nat) (stamp : DigitStamp n) (ox : BankRepairDigitOutSh)
    (iy : BankRepairDigitInSh) (ky : Bool) (σ : Nat → Option Nat) (gx : DigitOutGhost n)
    (gyi : Option (DigitAtom n))
    (hx : ∀ T v, ox = .D T → σ k = some v → Q gx.atom v)
    (hy : ∀ v, pendIn iy = true → σ (k + 1) = some v → Q gyi v)
    (hf : ox = .U → Q (some (.sampled stamp)) k) :
    (∀ T v, (bankRepairDigitDelStep ox iy ky).1 = .D T → sigDel k ox iy ky σ k = some v →
        Q (ghostDel stamp ox iy ky gx gyi).1.atom v) ∧
      (∀ v, pendIn (bankRepairDigitDelStep ox iy ky).2.1 = true →
        sigDel k ox iy ky σ (k + 1) = some v → Q (ghostDel stamp ox iy ky gx gyi).2 v) := by
  have hk1 : k ≠ k + 1 := by omega
  refine ⟨fun T v hD hv => ?_, fun v hD hv => ?_⟩ <;>
  rcases ox with _ | _ | ⟨_ | _⟩ <;> cases ky <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
  simp [bankRepairDigitDelStep, sigDel, ghostDel, DigitOutGhost.atom, cohortUpd, pendIn, hk1,
    hk1.symm] at hD hv ⊢ <;>
  first
  | exact hx _ _ rfl hv
  | exact hy _ rfl hv
  | (subst hv; exact hf rfl)

/-- **Input-motion edge.** Consumer: `labelOkStep`. -/
theorem finLab (k : Nat) (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool)
    (iy : BankRepairDigitInSh) (ky : Bool) (σ : Nat → Option Nat) (gxi gyi : Option (DigitAtom n))
    (hx : ∀ v, pendIn ix = true → σ k = some v → Q gxi v)
    (hy : ∀ v, pendIn iy = true → σ (k + 1) = some v → Q gyi v) :
    (∀ v, pendIn (bankRepairDigitFinStep bx ix kx iy ky).1 = true →
        sigFin k ix kx iy ky σ k = some v → Q (finInX bx ix kx iy ky gxi) v) ∧
      (∀ v, pendIn (bankRepairDigitFinStep bx ix kx iy ky).2.2.1 = true →
        sigFin k ix kx iy ky σ (k + 1) = some v → Q (finInY ix kx iy ky gxi gyi) v) := by
  have hk1 : k ≠ k + 1 := by omega
  refine ⟨fun v hp hv => ?_, fun v hp hv => ?_⟩ <;>
  rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases kx <;>
    rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases ky <;> cases bx <;>
  simp [bankRepairDigitFinStep, sigFin, finInX, finXP, finInY, finInYFree, finYX, finYP, shS,
    cohortUpd, pendIn, hk1, hk1.symm] at hp hv ⊢ <;>
  first
  | exact hx _ rfl hv
  | exact hy _ rfl hv

/-- **Terminal edge.** Consumer: `labelOkStep`. -/
theorem termLab (k : Nat) (ix : BankRepairDigitInSh) (kx : Bool) (σ : Nat → Option Nat)
    (gxi : Option (DigitAtom n)) (hx : ∀ v, pendIn ix = true → σ k = some v → Q gxi v) :
    ∀ v, pendIn (cohortTermStep ix kx).1 = true → σ k = some v → Q (ghostTermIn ix kx gxi) v := by
  intro v hp hv
  rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases kx <;>
  simp [cohortTermStep, ghostTermIn, pendIn] at hp ⊢ <;>
  exact hx _ rfl hv

end Pure

/-! ### The label invariant on the coupled chain -/

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat)

/-- **The atom is a recorded sample of the audit, taken at source cell `src + v`** of the label
`v < R`, on the lane, with tail bit `v = 0`. Consumer: `LabelOk`, the aligned completion
(`DigitCompletion`: the operand of digit `j` is the sample at `src + j`). -/
def SampledAt (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) (a : Option (DigitAtom n))
    (v : Nat) : Prop :=
  v < R ∧ ∃ smp : DigitSample (compileAdvice (ceilLogTwo n)) n,
    a = some (.sampled smp.id) ∧ smp.id.site = digitSite ring root (src + v) ∧
      smp.id.lane = lane ∧ smp.tail = decide (v = 0) ∧ DigitRecordedSample A smp

/-- Recorded samples stay recorded. Consumer: `labelOkStep`. -/
theorem sampledStep (S : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n) (a : Option (DigitAtom n))
    (v : Nat) (h : SampledAt ring root lane src R A a v) :
    SampledAt ring root lane src R (digitAuditStep ring S A e) a v := by
  obtain ⟨hv, smp, h1, h2, h3, h4, h5⟩ := h
  exact ⟨hv, smp, h1, h2, h3, h4, recordedSampleStep ring S A e smp h5⟩

/-- **The labels are the audit's samples**: every labelled source data packet and every labelled
pending / settled target input carries a recorded sample taken at the source cell of its label.
Consumer: `labAlignCoupled`, `labPreCoupled`, the pending join (I2). -/
def LabelOk (s : CohortLane) (σ : Nat → Option Nat)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  (∀ j, j < R → ∀ T v, s.out j = .D T → σ j = some v →
      SampledAt ring root lane src R A (laneCells ring root lane src A.current j).out.atom v) ∧
    (∀ j, R ≤ j → j < 2 * R → ∀ v, pendIn (s.inp j) = true → σ j = some v →
      SampledAt ring root lane src R A (laneCells ring root lane src A.current j).input v)

/-- Before any read nothing is labelled. Consumer: the start of the window. -/
theorem labelOkNone (s : CohortLane) (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    LabelOk ring root lane src R s (fun _ => none) A := by
  unfold LabelOk
  exact ⟨fun _ _ _ _ _ h => by simp at h, fun _ _ _ _ _ h => by simp at h⟩

/-- The label step of one scheduler letter. Consumer: `labelOkStep`. -/
def sigNext (R : Nat) (s : CohortLane) (σ : Nat → Option Nat) : Option Nat → Nat → Option Nat
  | none => σ
  | some k => sigStep R s σ k

/-- A pair edge is the letter at its site. Consumer: `labelOkStep`. -/
theorem edgeOfSome (e : Fin n) (k : Nat) (hE : cohortEdgeOf root src R e = some k) :
    k < 2 * R ∧ e = digitSite ring root (src + k) := by
  obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  unfold cohortEdgeOf at hE
  rw [cohortIdxSite ring root j hj] at hE
  by_cases hin : src ≤ j ∧ j < src + 2 * R
  · rw [if_pos hin] at hE
    simp only [Option.some.injEq] at hE
    refine ⟨by omega, ?_⟩
    rw [show src + k = j by omega]
  · rw [if_neg hin] at hE
    cases hE

include hn in
/-- **`LabelOk` is kept by every coupled letter.** Consumer: `labAlignCoupled`, `labPreCoupled`,
the pending join (I2). -/
theorem labelOkStep (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (σ : Nat → Option Nat) (e : Fin n)
    (h : LabelOk ring root lane src R (laneOfState ring hbank root lane src R x) σ x.2) :
    LabelOk ring root lane src R (laneOfState ring hbank root lane src R (nxt ring hn hbank x e))
      (sigNext R (laneOfState ring hbank root lane src R x) σ (cohortEdgeOf root src R e))
      (nxt ring hn hbank x e).2 := by
  have hls : laneOfState ring hbank root lane src R (nxt ring hn hbank x e) =
      cohortLaneStep R (laneOfState ring hbank root lane src R x) (cohortEdgeOf root src R e) :=
    (laneStep ring hn hbank root lane src R hR hsrc hend x hx e).2
  have hmono : ∀ a v, SampledAt ring root lane src R x.2 a v →
      SampledAt ring root lane src R (nxt ring hn hbank x e).2 a v :=
    fun a v hs => sampledStep ring root lane src R (piD x.1.val.1) x.2 e a v hs
  obtain ⟨hS, hT⟩ := h
  rw [hls]
  rcases hE : cohortEdgeOf root src R e with _ | k
  · have hoff := cellsOff ring hn hbank root lane src R hR hsrc hend x hx e hE
    refine ⟨fun j hj T v hD hv => ?_, fun j hj1 hj2 v hp hv => ?_⟩
    · rw [(hoff j (by omega)).1]
      exact hmono _ _ (hS j hj T v hD hv)
    · rw [(hoff j (by omega)).2 (by omega)]
      exact hmono _ _ (hT j hj1 hj2 v hp hv)
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
      have hpl := pipeLab (SampledAt ring root lane src R (nxt ring hn hbank x
          (digitSite ring root (src + k))).2) k (stampAt ring hbank root lane src x k)
        (decide (k = 0)) ((laneOfState ring hbank root lane src R x).out k)
        ((laneOfState ring hbank root lane src R x).out (k + 1)) σ
        (laneCells ring root lane src x.2.current k).out
        (laneCells ring root lane src x.2.current (k + 1)).out
        (fun T v hD hv => hmono _ _ (hS k (by omega) T v hD hv))
        (fun T v hD hv => hmono _ _ (hS (k + 1) h1 T v hD hv))
        (fun hU => by
          obtain ⟨smp, hid, htl, hrec⟩ :=
            cellsRead ring hn hbank root lane src R hR hsrc hend x hx k (by omega) hU
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
        have hdl := delLab (SampledAt ring root lane src R (nxt ring hn hbank x
            (digitSite ring root (src + k))).2) k (stampAt ring hbank root lane src x k)
          ((laneOfState ring hbank root lane src R x).out k)
          ((laneOfState ring hbank root lane src R x).inp (k + 1))
          ((laneOfState ring hbank root lane src R x).live (k + 1)) σ
          (laneCells ring root lane src x.2.current k).out
          (laneCells ring root lane src x.2.current (k + 1)).input
          (fun T v hD hv => hmono _ _ (hS k (by omega) T v hD hv))
          (fun v hp hv => hmono _ _ (hT (k + 1) (by omega) (by omega) v hp hv))
          (fun hU => by
            obtain ⟨smp, hid, htl, hrec⟩ :=
              cellsRead ring hn hbank root lane src R hR hsrc hend x hx k (by omega) hU
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
          have hfl := finLab (SampledAt ring root lane src R (nxt ring hn hbank x
              (digitSite ring root (src + k))).2) k (decide (k = R))
            ((laneOfState ring hbank root lane src R x).inp k)
            ((laneOfState ring hbank root lane src R x).live k)
            ((laneOfState ring hbank root lane src R x).inp (k + 1))
            ((laneOfState ring hbank root lane src R x).live (k + 1)) σ
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
          have htl := termLab (SampledAt ring root lane src R (nxt ring hn hbank x
              (digitSite ring root (src + k))).2) k
            ((laneOfState ring hbank root lane src R x).inp k)
            ((laneOfState ring hbank root lane src R x).live k) σ
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

/-- An export of the coupled letter: the delivery edge accepts. Consumer: `labAlignCoupled`. -/
def LabExport (R : Nat) (s : CohortLane) (o : Option Nat) (B : Bool) : Prop :=
  o = some (R - 1) ∧ Exported R s (R - 1) B

include hn in
/-- **I1 on the coupled chain.** With aligned labels `SiteAlign a` and `LabelOk`, a coupled
letter either exports nothing and keeps both, or exports, delivering into the border input a
recorded sample of the audit **taken at source cell `src + a`** (tail bit `a = 0`), after which
the labels are aligned at `a - 1` (or `R - 1` after the tail). Consumer: the pending join (I2),
the aligned completion (`DigitCompletion`). -/
theorem labAlignCoupled (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (σ : Nat → Option Nat) (a : Nat) (e : Fin n)
    (hA : SiteAlign R a (laneOfState ring hbank root lane src R x) σ)
    (hL : LabelOk ring root lane src R (laneOfState ring hbank root lane src R x) σ x.2) :
    LabelOk ring root lane src R (laneOfState ring hbank root lane src R (nxt ring hn hbank x e))
        (sigNext R (laneOfState ring hbank root lane src R x) σ (cohortEdgeOf root src R e))
        (nxt ring hn hbank x e).2 ∧
      ((SiteAlign R a (laneOfState ring hbank root lane src R (nxt ring hn hbank x e))
          (sigNext R (laneOfState ring hbank root lane src R x) σ (cohortEdgeOf root src R e)) ∧
        ∀ B, ¬ LabExport R (laneOfState ring hbank root lane src R x)
          (cohortEdgeOf root src R e) B) ∨
      (∃ B, LabExport R (laneOfState ring hbank root lane src R x) (cohortEdgeOf root src R e) B ∧
        SampledAt ring root lane src R (nxt ring hn hbank x e).2
          (laneCells ring root lane src (nxt ring hn hbank x e).2.current R).input a ∧
        SiteAlign R (if a = 0 then R - 1 else a - 1)
          (laneOfState ring hbank root lane src R (nxt ring hn hbank x e))
          (sigNext R (laneOfState ring hbank root lane src R x) σ (cohortEdgeOf root src R e)))) := by
  have hL' := labelOkStep ring hn hbank root lane src R hR hsrc hend x hx σ e hL
  have hls : laneOfState ring hbank root lane src R (nxt ring hn hbank x e) =
      cohortLaneStep R (laneOfState ring hbank root lane src R x) (cohortEdgeOf root src R e) :=
    (laneStep ring hn hbank root lane src R hR hsrc hend x hx e).2
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
      have hp : pendIn ((laneOfState ring hbank root lane src R (nxt ring hn hbank x e)).inp R) =
          true := by
        rw [hls, hE]
        simp only [cohortLaneStep]
        rw [hex.2.2.2.1]
        rfl
      exact hL'.2 R (by omega) (by omega) a hp hlab

include hn in
/-- **The distinguished tail on the coupled chain.** Before alignment (`SitePre m`), every
coupled letter keeps `LabelOk`; an export shrinks the prefix, and the export at the empty prefix
delivers a recorded sample **taken at source cell `src`** with the tail bit set, after which the
labels are aligned at `R - 1`. Consumer: the distinguished-tail phase, then `labAlignCoupled`. -/
theorem labPreCoupled (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (σ : Nat → Option Nat) (m : Nat) (e : Fin n)
    (hP : SitePre R m (laneOfState ring hbank root lane src R x) σ)
    (hL : LabelOk ring root lane src R (laneOfState ring hbank root lane src R x) σ x.2) :
    LabelOk ring root lane src R (laneOfState ring hbank root lane src R (nxt ring hn hbank x e))
        (sigNext R (laneOfState ring hbank root lane src R x) σ (cohortEdgeOf root src R e))
        (nxt ring hn hbank x e).2 ∧
      ((SitePre R m (laneOfState ring hbank root lane src R (nxt ring hn hbank x e))
          (sigNext R (laneOfState ring hbank root lane src R x) σ (cohortEdgeOf root src R e)) ∧
        ∀ B, ¬ LabExport R (laneOfState ring hbank root lane src R x)
          (cohortEdgeOf root src R e) B) ∨
      (∃ B, LabExport R (laneOfState ring hbank root lane src R x) (cohortEdgeOf root src R e) B ∧
        (m = 0 → SampledAt ring root lane src R (nxt ring hn hbank x e).2
            (laneCells ring root lane src (nxt ring hn hbank x e).2.current R).input 0 ∧
          SiteAlign R (R - 1) (laneOfState ring hbank root lane src R (nxt ring hn hbank x e))
            (sigNext R (laneOfState ring hbank root lane src R x) σ (cohortEdgeOf root src R e))) ∧
        (0 < m → SitePre R (m - 1) (laneOfState ring hbank root lane src R (nxt ring hn hbank x e))
            (sigNext R (laneOfState ring hbank root lane src R x) σ (cohortEdgeOf root src R e))))) := by
  have hL' := labelOkStep ring hn hbank root lane src R hR hsrc hend x hx σ e hL
  have hls : laneOfState ring hbank root lane src R (nxt ring hn hbank x e) =
      cohortLaneStep R (laneOfState ring hbank root lane src R x) (cohortEdgeOf root src R e) :=
    (laneStep ring hn hbank root lane src R hR hsrc hend x hx e).2
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
      have hp : pendIn ((laneOfState ring hbank root lane src R (nxt ring hn hbank x e)).inp R) =
          true := by
        rw [hls, hE]
        simp only [cohortLaneStep]
        rw [hex.2.2.2.1]
        rfl
      have hlab : sigNext R (laneOfState ring hbank root lane src R x) σ (some (R - 1)) R =
          some 0 := by
        simp only [sigNext]
        rcases siteStep R hR _ σ (R - 1) hP.1 with ⟨-, hne⟩ | ⟨-, -, hne⟩ | ⟨B', -, -, hl⟩
        · exact absurd hex (hne B)
        · exact absurd hex (hne B)
        · rw [hl, hlab0]
      exact hL'.2 R (by omega) (by omega) 0 hp hlab

end L3.PacketMomentLabels

#print axioms L3.PacketMomentLabels.pipeLab
#print axioms L3.PacketMomentLabels.delLab
#print axioms L3.PacketMomentLabels.finLab
#print axioms L3.PacketMomentLabels.termLab
#print axioms L3.PacketMomentLabels.labelOkStep
#print axioms L3.PacketMomentLabels.labAlignCoupled
#print axioms L3.PacketMomentLabels.labPreCoupled

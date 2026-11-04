import Leader.L3.Bank.RepairDigitPacketMomentQueueLabels

/-!
# Lemma e-packet, I2: the position labels of the settled run

repair.tex, Lemma e-packet: the aligned group settles the exports of origins `r-1, …, 0` on the
target cells in order. On the lane, with position labels (`L3.PacketMomentSites`):

* `LabRun m`: **every settled target cell `q` carries the label `m - (2R - 1 - q)`**, where `m` is
  the trial index (`L3.PacketMomentVSerial.vIdx`); a cell keeps its label while settled
  (`settledKeep`), and a cell becomes settled only as the oldest pending packet beside the run
  (`newSettled`), whose label is the head `a` of the aligned label queue (`labAlignStep`) and
  whose offset from the top is the run length `i`, with `m = a + i` (`labRunStep`).
* `LabTrial m`: the trial class `VIAt m` with the aligned label queue at the same index and
  `LabRun m`; one letter keeps it or reaches the trial target `VTAt m` with `LabRun m`
  (`labTrialStep`); it starts at the aligned packet-only cut (`labTrialOfPacketOnly`).
* `groupLabels`: at the aligned group (`VTAt (R - 1)`), **cell `R + j` carries label `j`**.

The label forms of the earlier phases: the aligned source (`srcLabStep`), the distinguished tail
(`preLabStep`), the aligned queue under the window invariants (`winLabStep`), and the start of the
queue at the mobile-free cut (`winLabOfMobileFree`).
-/

namespace L3.PacketMomentTrialLabels

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.MarkedCells
open L3.PacketMomentRows
open L3.PacketMomentWindow
open L3.PacketMomentAlign
open L3.PacketMomentPending
open L3.PacketMomentV
open L3.PacketMomentVSerial
open L3.PacketMomentSites
open L3.PacketMomentQueueLabels

/-! ### Settled cells -/

theorem finNewS (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (h1 : isSI (bankRepairDigitFinStep bx ix kx iy ky).1 = true)
    (h0 : isSI ix = false) :
    isPI ix = true ∧ isSI iy = true ∧ isSI (bankRepairDigitFinStep bx ix kx iy ky).2.2.1 = true := by
  revert h1 h0
  cases bx <;> cases kx <;> cases ky <;>
    rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    decide

theorem finNewSY (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (h1 : isSI (bankRepairDigitFinStep bx ix kx iy ky).2.2.1 = true)
    (h0 : isSI iy = false) : False := by
  revert h1 h0
  cases bx <;> cases kx <;> cases ky <;>
    rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    decide

theorem delNewS (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky : Bool)
    (h1 : isSI (bankRepairDigitDelStep ox iy ky).2.1 = true) (h0 : isSI iy = false) : False := by
  revert h1 h0
  cases ky <;> rcases ox with _ | _ | ⟨_ | _⟩ <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    decide

theorem termNewS (ix : BankRepairDigitInSh) (kx : Bool)
    (h1 : isSI (cohortTermStep ix kx).1 = true) (h0 : isSI ix = false) : isPI ix = true := by
  revert h1 h0
  cases kx <;> rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> decide

/-- **A cell becomes settled only as the pending packet on the letter's cell `k`, beside a
settled cell** (or at the terminal). Consumer: `labRunStep`. -/
theorem newSettled (R : Nat) (s : CohortLane) (k q : Nat) (hq1 : R ≤ q) (hq2 : q < 2 * R)
    (h1 : isSI ((cohortEdge R s k).inp q) = true) (h0 : isSI (s.inp q) = false) :
    q = k ∧ isPI (s.inp k) = true ∧
      (k + 1 < 2 * R → isSI (s.inp (k + 1)) = true ∧ isSI ((cohortEdge R s k).inp (k + 1)) = true) := by
  by_cases e1 : k + 1 < R
  · exfalso
    have hinp : (cohortEdge R s k).inp = s.inp := by unfold cohortEdge; rw [if_pos e1]
    rw [hinp, h0] at h1
    cases h1
  · by_cases e2 : k + 1 = R
    · exfalso
      have hinp : (cohortEdge R s k).inp = cohortUpd s.inp (k + 1)
          (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).2.1 := by
        unfold cohortEdge; rw [if_neg e1, if_pos e2]
      rw [hinp] at h1
      by_cases hq : q = k + 1
      · subst hq
        simp only [cohortUpd, if_true] at h1
        exact delNewS _ _ _ h1 h0
      · simp only [cohortUpd, if_neg hq] at h1
        rw [h0] at h1
        cases h1
    · by_cases e3 : k + 1 < 2 * R
      · have hinp : (cohortEdge R s k).inp = cohortUpd (cohortUpd s.inp k
            (bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
              (s.live (k + 1))).1) (k + 1)
            (bankRepairDigitFinStep (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1))
              (s.live (k + 1))).2.2.1 := by
          unfold cohortEdge; rw [if_neg e1, if_neg e2, if_pos e3]
        rw [hinp] at h1
        by_cases hq1' : q = k + 1
        · exfalso
          subst hq1'
          simp only [cohortUpd, if_true] at h1
          exact finNewSY _ _ _ _ _ h1 h0
        · by_cases hq0 : q = k
          · subst hq0
            simp only [cohortUpd, if_neg hq1', if_true] at h1
            obtain ⟨hP, hS, hS'⟩ := finNewS _ _ _ _ _ h1 h0
            refine ⟨rfl, hP, fun _ => ⟨hS, ?_⟩⟩
            rw [hinp]
            simp only [cohortUpd, if_true]
            exact hS'
          · exfalso
            simp only [cohortUpd, if_neg hq1', if_neg hq0] at h1
            rw [h0] at h1
            cases h1
      · by_cases e4 : k + 1 = 2 * R
        · have hinp : (cohortEdge R s k).inp = cohortUpd s.inp k
              (cohortTermStep (s.inp k) (s.live k)).1 := by
            unfold cohortEdge; rw [if_neg e1, if_neg e2, if_neg e3, if_pos e4]
          rw [hinp] at h1
          by_cases hq0 : q = k
          · subst hq0
            simp only [cohortUpd, if_true] at h1
            exact ⟨rfl, termNewS _ _ h1 h0, fun h => absurd h e3⟩
          · exfalso
            simp only [cohortUpd, if_neg hq0] at h1
            rw [h0] at h1
            cases h1
        · exfalso
          rw [edgeFar R s k (by omega), h0] at h1
          cases h1

/-- **A settled cell keeps its label.** Consumer: `labRunStep`. -/
theorem settledKeep (R : Nat) (s : CohortLane) (σ : Nat → Option Nat) (k q : Nat) (hq1 : R ≤ q)
    (hS : isSI (s.inp q) = true) : sigStep R s σ k q = σ q := by
  obtain ⟨T, hT⟩ : ∃ T, s.inp q = .S T := by
    revert hS; cases s.inp q with
    | S T => intro _; exact ⟨T, rfl⟩
    | _ => intro h; cases h
  unfold sigStep
  by_cases e1 : k + 1 < R
  · rw [if_pos e1]; exact sigPipeOther _ _ _ _ _ (by omega) (by omega)
  · rw [if_neg e1]
    by_cases e2 : k + 1 = R
    · rw [if_pos e2]
      by_cases hq : q = k + 1
      · subst hq
        rcases ho : s.out k with _ | _ | T0 <;> cases hl : s.live (k + 1) <;>
          simp [sigDel, hT, cohortUpd]
      · exact sigDelOther _ _ _ _ _ _ (by omega) hq
    · rw [if_neg e2]
      by_cases e3 : k + 1 < 2 * R
      · rw [if_pos e3]
        by_cases hq : q = k + 1
        · subst hq
          rcases hi : s.inp k with _ | _ | T0 | T0 <;> cases hl : s.live k <;>
            cases hl' : s.live (k + 1) <;> simp [sigFin, hT, cohortUpd]
        · exact sigFinLow _ _ _ _ _ _ _ hq
      · rw [if_neg e3]

/-- The letter's own target cell keeps its label. Consumer: `labRunStep`. -/
theorem sigAtSelf (R : Nat) (s : CohortLane) (σ : Nat → Option Nat) (k : Nat) (hk : R ≤ k) :
    sigStep R s σ k k = σ k := by
  unfold sigStep
  rw [if_neg (by omega), if_neg (by omega)]
  split
  · exact sigFinLow _ _ _ _ _ _ _ (by omega)
  · rfl

theorem pwIS (i : BankRepairDigitInSh) (h : isSI i = true) : pwI i = [] := by
  revert h; cases i <;> simp [isSI, pwI]

theorem pwIP (i : BankRepairDigitInSh) (h : isPI i = true) : pwI i ≠ [] := by
  revert h; cases i <;> simp [isPI, pwI]

/-! ### The labels of the settled run -/

/-- **The settled labels of the trial at index `m`**: every settled target cell `q` carries the
label `m - (2R - 1 - q)`. Consumer: `LabTrial`, `groupLabels`. -/
def LabRun (R m : Nat) (s : CohortLane) (σ : Nat → Option Nat) : Prop :=
  ∀ q, R ≤ q → q < 2 * R → isSI (s.inp q) = true →
    2 * R - 1 - q ≤ m ∧ σ q = some (m - (2 * R - 1 - q))

/-- **The settled labels are kept by every trial letter.** Consumer: `labTrialStep`. -/
theorem labRunStep (R a i m : Nat) (hR : 2 ≤ R) (s : CohortLane) (σ : Nat → Option Nat) (k : Nat)
    (hai : i + a + 1 ≤ R) (hA : AlignExt R a s) (hS : VShape R i s) (hm : vIdx R a i = m)
    (hL : LabExtAlign R a s σ) (hrun : LabRun R m s σ) :
    LabRun R m (cohortEdge R s k) (sigStep R s σ k) := by
  have hw := shapeWin R i s hS
  have hh := hostOfInv R s hw.1
  have hb := barOfBarrier R s hw.2
  intro q hq1 hq2 hS'
  by_cases hSq : isSI (s.inp q) = true
  · rw [settledKeep R s σ k q hq1 hSq]
    exact hrun q hq1 hq2 hSq
  · have hSq' : isSI (s.inp q) = false := by
      cases h : isSI (s.inp q)
      · rfl
      · exact absurd h hSq
    obtain ⟨rfl, hPk, hnext⟩ := newSettled R s k q hq1 hq2 hS' hSq'
    rw [sigAtSelf R s σ q hq1]
    rcases alignExtStep R a hR s q hA hw with ⟨_, _, hls⟩ |
        ⟨B, heB, hB, _, _, _, hPB, _, hret⟩
    · exfalso
      by_cases h3 : q + 1 < 2 * R
      · have hl := hls.1 hq1 h3
        obtain ⟨hs1, hs1'⟩ := hnext h3
        rw [pwIS _ hs1', pwIS _ hS', pwIS _ hs1] at hl
        simp only [List.nil_append] at hl
        exact pwIP _ hPk hl.symm
      · have hl := hls.2 (by omega)
        rw [pwIS _ hS'] at hl
        exact pwIP _ hPk hl.symm
    · rcases labAlignStep R a hR s σ q hL hh hb with ⟨_, hlen⟩ | ⟨_, _, _, hσ, _, _⟩
      · exfalso
        have h1 := labLen R s σ
        have h2 := labLen R (cohortEdge R s q) (sigStep R s σ q)
        have h3 := congrArg List.length heB
        simp only [List.length_cons] at h3
        omega
      · rw [hσ]
        have hqlt : q < 2 * R - i := by
          by_cases hge : 2 * R - i ≤ q
          · rw [(hS.2 q hq1 hq2).2.1 hge] at hPk
            cases hPk
          · omega
        have hqi : 2 * R - 1 - q = i := by
          by_cases h3 : q + 1 < 2 * R
          · have hs1 := (hnext h3).1
            by_cases hlt : q + 1 < 2 * R - i
            · rcases (hS.2 (q + 1) (by omega) h3).2.2 hlt with he | hp
              · rw [he] at hs1; cases hs1
              · revert hs1 hp; cases s.inp (q + 1) <;> simp [isSI, isPI]
            · omega
          · omega
        unfold vIdx at hm
        by_cases hai0 : a + i = 0
        · exfalso
          have ha0 : a = 0 := by omega
          have hq' : q + 1 = 2 * R := by omega
          rw [hB, ha0] at hret
          have := hret hq'
          rw [this] at hS'
          cases hS'
        · rw [if_neg hai0] at hm
          refine ⟨by omega, ?_⟩
          rw [hqi]
          congr 1
          omega

/-- **The labelled trial class at index `m`.** Consumer: the coupled trial with labels. -/
def LabTrial (R m : Nat) (s : CohortLane) (σ : Nat → Option Nat) : Prop :=
  ∃ a i, i + a + 1 ≤ R ∧ AlignExt R a s ∧ VShape R i s ∧ vIdx R a i = m ∧
    LabExtAlign R a s σ ∧ LabRun R m s σ

/-- **One letter of the labelled trial**: the trial target at the index with the settled labels,
or the labelled trial at the same index. Consumer: the coupled trial with labels. -/
theorem labTrialStep (R m : Nat) (hR : 3 ≤ R) (s : CohortLane) (σ : Nat → Option Nat) (k : Nat)
    (h : LabTrial R m s σ) :
    (VTAt R m (cohortEdge R s k) ∧ LabRun R m (cohortEdge R s k) (sigStep R s σ k)) ∨
      LabTrial R m (cohortEdge R s k) (sigStep R s σ k) := by
  obtain ⟨a, i, hai, hA, hS, hm, hL, hrun⟩ := h
  have hrun' := labRunStep R a i m (by omega) s σ k hai hA hS hm hL hrun
  have hw := shapeWin R i s hS
  have hh := hostOfInv R s hw.1
  have hb := barOfBarrier R s hw.2
  rcases vStepIdx R hR s k a i hai hA hS with ⟨ha0, hi1, hVT⟩ | ⟨a', i', hai', hA', hS', hm'⟩
  · left
    have : m = i := by
      rw [← hm]; unfold vIdx; rw [if_neg (by omega), ha0]; omega
    rw [this] at hrun' ⊢
    exact ⟨hVT, hrun'⟩
  · right
    obtain ⟨a'', hL'⟩ : ∃ a'', LabExtAlign R a'' (cohortEdge R s k) (sigStep R s σ k) := by
      rcases labAlignStep R a (by omega) s σ k hL hh hb with ⟨h1, _⟩ | ⟨_, _, _, _, _, h1⟩
      · exact ⟨_, h1⟩
      · exact ⟨_, h1⟩
    have hidx := extIdx R a' a'' _ _ hA' hL'
    subst hidx
    exact ⟨a', i', hai', hA', hS', by rw [hm', hm], hL', hrun'⟩

/-- **Entry of the labelled trial** at an aligned packet-only cut. Consumer: the coupled trial
with labels. -/
theorem labTrialOfPacketOnly (R a : Nat) (s : CohortLane) (σ : Nat → Option Nat)
    (hA : AlignExt R a s) (hL : LabExtAlign R a s σ)
    (hP : L3.PacketMomentRetire.PacketOnly R s) : LabTrial R (vIdx R a 0) s σ := by
  have ha := hA.2.1
  have hS := shapeOfPacketOnly R (by omega) s hP
  refine ⟨a, 0, by omega, hA, hS, rfl, hL, fun q hq1 hq2 hSq => ?_⟩
  exfalso
  rcases (hS.2 q hq1 hq2).2.2 (by omega) with he | hp
  · rw [he] at hSq; cases hSq
  · revert hSq hp; cases s.inp q <;> simp [isSI, isPI]

/-- **At the aligned group, target cell `R + j` carries label `j`** (and is settled).
Consumer: the aligned completion (`DigitCompletion`: the operand of digit `j` is the sample at
source cell `src + j`). -/
theorem groupLabels (R : Nat) (hR : 1 ≤ R) (s : CohortLane) (σ : Nat → Option Nat)
    (hg : VTAt R (R - 1) s) (hrun : LabRun R (R - 1) s σ) (j : Nat) (hj : j < R) :
    isSI (s.inp (R + j)) = true ∧ σ (R + j) = some j := by
  obtain ⟨_, hc⟩ := hg
  have hS : isSI (s.inp (R + j)) = true := by
    have hq := hc (R + j) (by omega) (by omega)
    by_cases h0 : j = 0
    · rw [hq.2.1 (by omega)]; rfl
    · rw [hq.2.2.1 (by omega)]; rfl
  refine ⟨hS, ?_⟩
  rw [(hrun (R + j) (by omega) (by omega) hS).2]
  congr 1
  omega

/-! ### The label forms of the earlier phases -/

/-- **The labelled aligned source**: the tail-bit and label alignments at one index. Consumer:
the coupled phases up to the mobile-free cut. -/
def SrcLab (R : Nat) (s : CohortLane) (σ : Nat → Option Nat) : Prop :=
  ∃ a, Align R a s.out ∧ SiteAlign R a s σ

/-- Kept by every lane letter. Consumer: the coupled phases up to the mobile-free cut. -/
theorem srcLabStep (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (σ : Nat → Option Nat) (k : Nat)
    (h : SrcLab R s σ) : SrcLab R (cohortEdge R s k) (sigStep R s σ k) := by
  obtain ⟨a, hA, hL⟩ := h
  obtain ⟨a', hA'⟩ : ∃ a', Align R a' (cohortEdge R s k).out := by
    rcases alignStep R a hR s k hA with ⟨h1, _⟩ | ⟨_, _, _, _, h1⟩
    · exact ⟨_, h1⟩
    · exact ⟨_, h1⟩
  obtain ⟨a'', hL'⟩ : ∃ a'', SiteAlign R a'' (cohortEdge R s k) (sigStep R s σ k) := by
    rcases siteAlignStep R a hR s σ k hL with ⟨h1, _⟩ | ⟨_, _, _, _, h1⟩
    · exact ⟨_, h1⟩
    · exact ⟨_, h1⟩
  have hidx := srcIdx R a' a'' _ _ hA' hL'
  subst hidx
  exact ⟨a', hA', hL'⟩

/-- An export removes its tail bit from the source word. Consumer: `preLabStep`. -/
theorem exportWord (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (k : Nat) (B : Bool) (hc : CZero s.out)
    (hex : Exported R s k B) : srcWord R s.out = B :: srcWord R (cohortEdge R s k).out := by
  rcases srcStep R hR s k hc with ⟨_, hp⟩ | ⟨hk0, _⟩ | ⟨B', hex', he⟩
  · exfalso
    obtain ⟨hk, hE, hl, hP, _⟩ := hex
    have h1 := (hp hk).1
    rw [hP] at h1
    simp [hl, hE] at h1
  · exfalso
    have := hex.1
    omega
  · have hB : B' = B := by
      have h1 := hex'.2.2.2.1
      rw [hex.2.2.2.1] at h1
      cases h1
      rfl
    rw [he, hB]

/-- **The labelled distinguished-tail phase**: the tail-bit and label prefixes of one length.
Consumer: the coupled distinguished-tail phase. -/
def PreLab (R m : Nat) (s : CohortLane) (σ : Nat → Option Nat) : Prop :=
  Pre R m s.out ∧ SitePre R m s σ

/-- **Start**: as soon as cell `0` holds an unread `U`, with any labels. Consumer: the coupled
distinguished-tail phase. -/
theorem preLabOfU (R : Nat) (hR : 1 ≤ R) (s : CohortLane) (σ : Nat → Option Nat)
    (h0 : s.out 0 = .U) : PreLab R (wSeg R s.out 1 (R - 1)).length s σ := by
  have hc : CZero s.out := Or.inl h0
  have hz : SigZero s σ := fun h => by rw [h0] at h; cases h
  refine ⟨preOfCZero R hR s.out hc, ?_⟩
  have hl : (wSeg R s.out 1 (R - 1)).length = (sSeg R s.out σ 1 (R - 1)).length := by
    have h1 := siteLen R s.out σ
    rw [siteCZero R hR s σ hc hz, wordCZero R hR s.out hc] at h1
    simp only [List.length_append, sb, blk, List.length_cons, List.length_map, dnLen,
      List.length_replicate] at h1
    omega
  rw [hl]
  exact sitePreOf R hR s σ hc hz

/-- **One letter of the distinguished-tail phase**: kept without an export; an export shrinks
the prefix, and the export at the empty prefix leaves the labelled aligned source at `R - 1`.
Consumer: the coupled distinguished-tail phase. -/
theorem preLabStep (R m : Nat) (hR : 2 ≤ R) (s : CohortLane) (σ : Nat → Option Nat) (k : Nat)
    (h : PreLab R m s σ) :
    (PreLab R m (cohortEdge R s k) (sigStep R s σ k) ∧ ∀ B, ¬ Exported R s k B) ∨
      (∃ B, Exported R s k B ∧
        (m = 0 → SrcLab R (cohortEdge R s k) (sigStep R s σ k)) ∧
        (0 < m → PreLab R (m - 1) (cohortEdge R s k) (sigStep R s σ k))) := by
  obtain ⟨hP, hL⟩ := h
  rcases sitePreStep R m hR s σ k hL with ⟨hL', hne⟩ | ⟨B, hex, h0, hpos⟩
  · left
    refine ⟨⟨?_, hL'⟩, hne⟩
    rcases preStep R m hR s k hP with ⟨hP', _⟩ | ⟨B', hex', _⟩
    · exact hP'
    · exact absurd hex' (hne B')
  · right
    rcases preStep R m hR s k hP with ⟨_, hne⟩ | ⟨B', _, hw', hb0, hbpos⟩
    · exact absurd ⟨hex, exportWord R hR s k B hP.1 hex⟩ (hne B)
    · refine ⟨B, hex, fun hm => ?_, fun hm => ⟨hbpos hm, hpos hm⟩⟩
      exact ⟨R - 1, (hb0 hm).2, (h0 hm).2⟩

/-- **The labelled aligned queue**: the tail-bit and label queue alignments at one index.
Consumer: the coupled phases U and retirement. -/
def WinLab (R : Nat) (s : CohortLane) (σ : Nat → Option Nat) : Prop :=
  ∃ a, AlignExt R a s ∧ LabExtAlign R a s σ

/-- Kept by every lane letter under the window invariants. Consumer: the coupled phases U and
retirement. -/
theorem winLabStep (R : Nat) (hR : 2 ≤ R) (s : CohortLane) (σ : Nat → Option Nat) (k : Nat)
    (h : WinLab R s σ) (hw : Inv R (winOf R s) ∧ Barrier R (winOf R s)) :
    WinLab R (cohortEdge R s k) (sigStep R s σ k) := by
  obtain ⟨a, hA, hL⟩ := h
  obtain ⟨a', hA'⟩ : ∃ a', AlignExt R a' (cohortEdge R s k) := by
    rcases alignExtStep R a hR s k hA hw with ⟨h1, _⟩ | ⟨_, _, _, h1, _⟩
    · exact ⟨_, h1⟩
    · exact ⟨_, h1⟩
  obtain ⟨a'', hL'⟩ : ∃ a'', LabExtAlign R a'' (cohortEdge R s k) (sigStep R s σ k) := by
    rcases labAlignStep R a hR s σ k hL (hostOfInv R s hw.1) (barOfBarrier R s hw.2) with
      ⟨h1, _⟩ | ⟨_, _, _, _, _, h1⟩
    · exact ⟨_, h1⟩
    · exact ⟨_, h1⟩
  have hidx := extIdx R a' a'' _ _ hA' hL'
  subst hidx
  exact ⟨a', hA', hL'⟩

/-- **At a mobile-free cut the labelled aligned source aligns the labelled queue.** Consumer: the
coupled start of phase U. -/
theorem winLabOfMobileFree (R : Nat) (s : CohortLane) (σ : Nat → Option Nat) (hs : SrcLab R s σ)
    (h : ∀ q, R ≤ q → q < 2 * R → s.live q = false ∧ (s.inp q = .E ∨ ∃ T, s.inp q = .S T)) :
    WinLab R s σ := by
  obtain ⟨a, hA, hL⟩ := hs
  have hnp : ∀ q, R ≤ q → q < 2 * R → isPI (s.inp q) = false := fun q h1 h2 => by
    rcases (h q h1 h2).2 with hE | ⟨T, hS⟩
    · rw [hE]; rfl
    · rw [hS]; rfl
  exact ⟨a, alignExtOfSrc R a s hA hnp, labExtOfSite R a s σ hL hnp⟩

end L3.PacketMomentTrialLabels

#print axioms L3.PacketMomentTrialLabels.newSettled
#print axioms L3.PacketMomentTrialLabels.settledKeep
#print axioms L3.PacketMomentTrialLabels.labRunStep
#print axioms L3.PacketMomentTrialLabels.labTrialStep
#print axioms L3.PacketMomentTrialLabels.labTrialOfPacketOnly
#print axioms L3.PacketMomentTrialLabels.groupLabels
#print axioms L3.PacketMomentTrialLabels.srcLabStep
#print axioms L3.PacketMomentTrialLabels.preLabOfU
#print axioms L3.PacketMomentTrialLabels.preLabStep
#print axioms L3.PacketMomentTrialLabels.winLabStep
#print axioms L3.PacketMomentTrialLabels.winLabOfMobileFree

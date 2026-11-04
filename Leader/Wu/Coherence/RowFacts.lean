import Leader.Wu.Coherence.RowFactStatements
import Leader.Wu.Coherence.FreshnessClear

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31RowFacts

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31FootprintCover2R

variable {ψ κ τ : Nat}

theorem branchAtV3_cases
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ) :
    (branchAtV3 hψ h2 l r = .seek ∧
      r.ctl.tok = .seek) ∨
    (branchAtV3 hψ h2 l r = .sweep ∧
      r.ctl.tok ≠ .seek ∧ l.ctl.tok = .sweep) ∨
    (branchAtV3 hψ h2 l r = .commit ∧
      r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok = .commit) ∨
    (branchAtV3 hψ h2 l r = .release ∧
      r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok = .release) ∨
    (branchAtV3 hψ h2 l r = .scrubL ∧
      r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok ≠ .release ∧
      r.ctl.tok = .scrubL) ∨
    (branchAtV3 hψ h2 l r = .openR ∧
      r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok ≠ .release ∧
      r.ctl.tok ≠ .scrubL ∧ l.ctl.tok = .openR) ∨
    (branchAtV3 hψ h2 l r = .sealed ∧
      r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok ≠ .release ∧
      r.ctl.tok ≠ .scrubL ∧ l.ctl.tok ≠ .openR ∧
      l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
      l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed) ∨
    (branchAtV3 hψ h2 l r = .openHazard ∧
      r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok ≠ .release ∧
      r.ctl.tok ≠ .scrubL ∧ l.ctl.tok ≠ .openR ∧
      l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
      ¬ (l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed) ∧
      l.ctl.mark = .open ∧ r.ctl.mark = .open ∧
      (let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
       pairHazardV3 l.phys r.phys q.1 q.2 = true)) ∨
    (branchAtV3 hψ h2 l r = .openNoHazard ∧
      r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok ≠ .release ∧
      r.ctl.tok ≠ .scrubL ∧ l.ctl.tok ≠ .openR ∧
      l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
      ¬ (l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed) ∧
      l.ctl.mark = .open ∧ r.ctl.mark = .open ∧
      (let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
       pairHazardV3 l.phys r.phys q.1 q.2 = false)) ∨
    (branchAtV3 hψ h2 l r = .mixed ∧
      r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok ≠ .release ∧
      r.ctl.tok ≠ .scrubL ∧ l.ctl.tok ≠ .openR ∧
      (¬ (l.ctl.tok = .none ∧ r.ctl.tok = .none) ∨
        (l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
          ¬ (l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed) ∧
          ¬ (l.ctl.mark = .open ∧ r.ctl.mark = .open)))) := by
  by_cases hs : r.ctl.tok = .seek
  · simp [branchAtV3, hs]
  · by_cases hw : l.ctl.tok = .sweep
    · simp [branchAtV3, hs, hw]
    · by_cases hc : r.ctl.tok = .commit
      · simp [branchAtV3, hs, hw, hc]
      · by_cases hr : l.ctl.tok = .release
        · simp [branchAtV3, hs, hw, hc, hr]
        · by_cases hsl : r.ctl.tok = .scrubL
          · simp [branchAtV3, hs, hw, hc, hr, hsl]
          · by_cases hor : l.ctl.tok = .openR
            · simp [branchAtV3, hs, hw, hc, hr, hsl, hor]
            · by_cases hn : l.ctl.tok = .none ∧ r.ctl.tok = .none
              · rcases hn with ⟨hln, hrn⟩
                by_cases hseal :
                    l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed
                · rcases hseal with ⟨hlm, hrm⟩
                  simp [branchAtV3, hs, hw, hc, hr, hsl, hor,
                    hln, hrn, hlm, hrm]
                · by_cases hopen :
                    l.ctl.mark = .open ∧ r.ctl.mark = .open
                  · rcases hopen with ⟨hlm, hrm⟩
                    let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
                    by_cases hh : pairHazardV3 l.phys r.phys q.1 q.2 = true
                    · simp [branchAtV3, hs, hw, hc, hr, hsl, hor,
                        hln, hrn, hseal, hlm, hrm, q, hh]
                    · have hh0 := Bool.eq_false_iff.mpr hh
                      simp [branchAtV3, hs, hw, hc, hr, hsl, hor,
                        hln, hrn, hseal, hlm, hrm, q, hh, hh0]
                  · simp [branchAtV3, hs, hw, hc, hr, hsl, hor,
                      hln, hrn, hseal, hopen]
              · simp [branchAtV3, hs, hw, hc, hr, hsl, hor, hn]

theorem branch_seek_inv
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .seek) :
    r.ctl.tok = .seek := by
  have h := branchAtV3_cases hψ h2 l r
  rw [hb] at h
  simpa using h

theorem branch_sweep_inv
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .sweep) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok = .sweep := by
  have h := branchAtV3_cases hψ h2 l r
  rw [hb] at h
  simpa using h

theorem branch_commit_inv
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .commit) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧ r.ctl.tok = .commit := by
  have h := branchAtV3_cases hψ h2 l r
  rw [hb] at h
  simpa using h

theorem branch_release_inv
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .release) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok = .release := by
  have h := branchAtV3_cases hψ h2 l r
  rw [hb] at h
  simpa using h

theorem branch_scrubL_inv
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .scrubL) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok ≠ .release ∧
      r.ctl.tok = .scrubL := by
  have h := branchAtV3_cases hψ h2 l r
  rw [hb] at h
  simpa using h

theorem branch_openR_inv
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openR) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok ≠ .release ∧
      r.ctl.tok ≠ .scrubL ∧ l.ctl.tok = .openR := by
  have h := branchAtV3_cases hψ h2 l r
  rw [hb] at h
  simpa using h

theorem branch_sealed_inv
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .sealed) :
    l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
      l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed := by
  have h := branchAtV3_cases hψ h2 l r
  rw [hb] at h
  simp at h
  rcases h with ⟨_, _, _, _, _, _, hln, hrn, hlm, hrm⟩
  exact ⟨hln, hrn, hlm, hrm⟩

theorem branch_openHazard_inv
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openHazard) :
    l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
      l.ctl.mark = .open ∧ r.ctl.mark = .open ∧
      (let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
       pairHazardV3 l.phys r.phys q.1 q.2 = true) := by
  have h := branchAtV3_cases hψ h2 l r
  rw [hb] at h
  simp at h
  rcases h with ⟨_, _, _, _, _, _, hln, hrn, _, hlm, hrm, hh⟩
  exact ⟨hln, hrn, hlm, hrm, by simpa using hh⟩

theorem branch_openNoHazard_inv
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openNoHazard) :
    l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
      l.ctl.mark = .open ∧ r.ctl.mark = .open ∧
      (let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
       pairHazardV3 l.phys r.phys q.1 q.2 = false) := by
  have h := branchAtV3_cases hψ h2 l r
  rw [hb] at h
  simp at h
  rcases h with ⟨_, _, _, _, _, _, hln, hrn, _, hlm, hrm, hh⟩
  exact ⟨hln, hrn, hlm, hrm, by simpa using hh⟩

theorem branch_mixed_inv
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .mixed) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok ≠ .release ∧
      r.ctl.tok ≠ .scrubL ∧ l.ctl.tok ≠ .openR := by
  have h := branchAtV3_cases hψ h2 l r
  rw [hb] at h
  simp at h
  rcases h with ⟨hs, hw, hc, hr, hsl, hor, _⟩
  exact ⟨hs, hw, hc, hr, hsl, hor⟩

private theorem mainClear_setControl
    (u : Cell ψ κ τ) (m : R2Coherence.Mark) (t : TokenV3)
    (h : MainClearV3 u) : MainClearV3 (setControl u m t) := by
  unfold MainClearV3 R2CoherenceBranches.MainClear at h ⊢
  simpa [eraseCellV3, setControl, R2Coherence.raw] using h

private theorem mainClear_startClosing
    (u : Cell ψ κ τ) (h : MainClearV3 u) :
    MainClearV3 (startClosing u) := by
  exact mainClear_setControl u .closing .seek h

private theorem mainClear_cleared
    (u : Cell ψ κ τ) (m : R2Coherence.Mark) (t : TokenV3) :
    MainClearV3 (setControl (clearMain u) m t) := by
  unfold MainClearV3 R2CoherenceBranches.MainClear
  simp [eraseCellV3, setControl, clearMain, R2Coherence.clearMainPhys,
    PPLLExpiringComparisonRepair.clearComparisonCarrier, R2Coherence.raw]

private theorem seekStage_mainClear
    (l r : Cell ψ κ τ) :
    (MainClearV3 l → MainClearV3 (seekStageV3 l r).1) ∧
    (MainClearV3 r → MainClearV3 (seekStageV3 l r).2) := by
  by_cases hr : atRootB r = true
  · rw [show seekStageV3 l r = (l, setControl r .closing .sweep) by
      simp [seekStageV3, hr]]
    exact ⟨fun h => h, mainClear_setControl r .closing .sweep⟩
  · by_cases hl : atRootB l = true
    · rw [show seekStageV3 l r =
        (setControl l .closing .sweep, setControl r .closing .none) by
        simp [seekStageV3, hr, hl]]
      exact ⟨mainClear_setControl l .closing .sweep,
        mainClear_setControl r .closing .none⟩
    · rw [show seekStageV3 l r =
        (setControl l .closing .seek, setControl r .closing .none) by
        simp [seekStageV3, hr, hl]]
      exact ⟨mainClear_setControl l .closing .seek,
        mainClear_setControl r .closing .none⟩

private theorem sweepStage_mainClear
    (l r : Cell ψ κ τ) :
    (MainClearV3 l → MainClearV3 (sweepStageV3 l r).1) ∧
    (MainClearV3 r → MainClearV3 (sweepStageV3 l r).2) := by
  by_cases hs : successorB l r = true
  · by_cases ht : atTerminalB r = true
    · simp [sweepStageV3, hs, ht]
      exact ⟨fun _ => mainClear_cleared l .closing .none,
        fun _ => mainClear_cleared r .closing .commit⟩
    · simp [sweepStageV3, hs, ht]
      exact ⟨fun _ => mainClear_cleared l .closing .none,
        fun _ => mainClear_cleared r .closing .sweep⟩
  · rw [show sweepStageV3 l r = (startClosing l, r) by
      simp [sweepStageV3, hs]]
    exact ⟨mainClear_startClosing l, fun h => h⟩

private theorem commitStage_mainClear
    (l r : Cell ψ κ τ) :
    (MainClearV3 l → MainClearV3 (commitStageV3 l r).1) ∧
    (MainClearV3 r → MainClearV3 (commitStageV3 l r).2) := by
  by_cases hr : atRootB r = true
  · rw [show commitStageV3 l r =
      (l, setControl (clearMain r) .sealed .none) by
        simp [commitStageV3, hr]]
    constructor
    · intro h
      exact h
    · intro _
      exact mainClear_cleared r .sealed .none
  · by_cases hl : atRootB l = true
    · rw [show commitStageV3 l r =
        (setControl (clearMain l) .sealed .none,
          setControl (clearMain r) .sealed .none) by
          simp [commitStageV3, hr, hl]]
      constructor
      · intro _
        exact mainClear_cleared l .sealed .none
      · intro _
        exact mainClear_cleared r .sealed .none
    · rw [show commitStageV3 l r =
        (setControl (clearMain l) .closing .commit,
          setControl (clearMain r) .sealed .none) by
          simp [commitStageV3, hr, hl]]
      constructor
      · intro _
        exact mainClear_cleared l .closing .commit
      · intro _
        exact mainClear_cleared r .sealed .none

private theorem releaseStage_mainClear
    (l r : Cell ψ κ τ) :
    (MainClearV3 l → MainClearV3 (releaseStageV3 l r).1) ∧
    (MainClearV3 r → MainClearV3 (releaseStageV3 l r).2) := by
  by_cases hs : successorB l r = true
  · by_cases hq : writerQuiet r = true
    · by_cases ht : atTerminalB r = true
      · rw [show releaseStageV3 l r =
          (setControl l .releasing .none,
            setControl r .releasing .scrubL) by
            simp [releaseStageV3, hs, hq, ht]]
        constructor
        · intro h
          exact mainClear_setControl l .releasing .none h
        · intro h
          exact mainClear_setControl r .releasing .scrubL h
      · rw [show releaseStageV3 l r =
          (setControl l .releasing .none,
            setControl r .releasing .release) by
            simp [releaseStageV3, hs, hq, ht]]
        constructor
        · intro h
          exact mainClear_setControl l .releasing .none h
        · intro h
          exact mainClear_setControl r .releasing .release h
    · by_cases hl : atRootB l = true
      · rw [show releaseStageV3 l r =
          (setControl l .sealed .none, r) by
            simp [releaseStageV3, hs, hq, hl]]
        constructor
        · intro h
          exact mainClear_setControl l .sealed .none h
        · intro h
          exact h
      · rw [show releaseStageV3 l r =
          (setControl l .closing .commit, r) by
            simp [releaseStageV3, hs, hq, hl]]
        constructor
        · intro h
          exact mainClear_setControl l .closing .commit h
        · intro h
          exact h
  · rw [show releaseStageV3 l r = (startClosing l, r) by
      simp [releaseStageV3, hs]]
    constructor
    · intro h
      exact mainClear_startClosing l h
    · intro h
      exact h

private theorem scrubLStage_mainClear
    (l r : Cell ψ κ τ) :
    (MainClearV3 l → MainClearV3 (scrubLStageV3 l r).1) ∧
    (MainClearV3 r → MainClearV3 (scrubLStageV3 l r).2) := by
  by_cases hs : successorB l r = true
  · by_cases hr : atRootB r = true
    · rw [show scrubLStageV3 l r = (l, startClosing r) by
        simp [scrubLStageV3, hs, hr]]
      exact ⟨fun h => h, mainClear_startClosing r⟩
    · by_cases hl : atRootB l = true
      · simp [scrubLStageV3, hs, hr, hl]
        exact ⟨fun _ => mainClear_cleared l .releasing .openR,
          fun _ => mainClear_cleared r .releasing .none⟩
      · simp [scrubLStageV3, hs, hr, hl]
        exact ⟨fun _ => mainClear_cleared l .releasing .scrubL,
          fun _ => mainClear_cleared r .releasing .none⟩
  · rw [show scrubLStageV3 l r = (l, startClosing r) by
      simp [scrubLStageV3, hs]]
    exact ⟨fun h => h, mainClear_startClosing r⟩

private theorem openRStage_mainClear
    (l r : Cell ψ κ τ) :
    (MainClearV3 l → MainClearV3 (openRStageV3 l r).1) ∧
    (MainClearV3 r → MainClearV3 (openRStageV3 l r).2) := by
  by_cases hs : successorB l r = true
  · by_cases ht : atTerminalB r = true
    · simp [openRStageV3, hs, ht]
      exact ⟨fun _ => mainClear_cleared l .open .none,
        fun _ => mainClear_cleared r .open .none⟩
    · simp [openRStageV3, hs, ht]
      exact ⟨fun _ => mainClear_cleared l .open .none,
        fun _ => mainClear_cleared r .releasing .openR⟩
  · rw [show openRStageV3 l r = (startClosing l, r) by
      simp [openRStageV3, hs]]
    exact ⟨mainClear_startClosing l, fun h => h⟩

private theorem row_seek_mainClear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hs : r.ctl.tok = .seek) :
    (MainClearV3 l → MainClearV3 (rowV3 hψ (by decide) h2 l r).1) ∧
    (MainClearV3 r → MainClearV3 (rowV3 hψ (by decide) h2 l r).2) := by
  simpa [rowV3, hs] using seekStage_mainClear l r

private theorem row_sweep_mainClear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hs : r.ctl.tok ≠ .seek) (hw : l.ctl.tok = .sweep) :
    (MainClearV3 l → MainClearV3 (rowV3 hψ (by decide) h2 l r).1) ∧
    (MainClearV3 r → MainClearV3 (rowV3 hψ (by decide) h2 l r).2) := by
  simpa [rowV3, hs, hw] using sweepStage_mainClear l r

private theorem row_commit_mainClear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hs : r.ctl.tok ≠ .seek) (hw : l.ctl.tok ≠ .sweep)
    (hc : r.ctl.tok = .commit) :
    (MainClearV3 l → MainClearV3 (rowV3 hψ (by decide) h2 l r).1) ∧
    (MainClearV3 r → MainClearV3 (rowV3 hψ (by decide) h2 l r).2) := by
  simpa [rowV3, hs, hw, hc] using commitStage_mainClear l r

private theorem row_release_mainClear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hs : r.ctl.tok ≠ .seek) (hw : l.ctl.tok ≠ .sweep)
    (hc : r.ctl.tok ≠ .commit) (hr : l.ctl.tok = .release) :
    (MainClearV3 l → MainClearV3 (rowV3 hψ (by decide) h2 l r).1) ∧
    (MainClearV3 r → MainClearV3 (rowV3 hψ (by decide) h2 l r).2) := by
  simpa [rowV3, hs, hw, hc, hr] using releaseStage_mainClear l r

private theorem row_scrubL_mainClear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hs : r.ctl.tok ≠ .seek) (hw : l.ctl.tok ≠ .sweep)
    (hc : r.ctl.tok ≠ .commit) (hr : l.ctl.tok ≠ .release)
    (hsl : r.ctl.tok = .scrubL) :
    (MainClearV3 l → MainClearV3 (rowV3 hψ (by decide) h2 l r).1) ∧
    (MainClearV3 r → MainClearV3 (rowV3 hψ (by decide) h2 l r).2) := by
  simpa [rowV3, hs, hw, hc, hr, hsl] using scrubLStage_mainClear l r

private theorem row_openR_mainClear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hs : r.ctl.tok ≠ .seek) (hw : l.ctl.tok ≠ .sweep)
    (hc : r.ctl.tok ≠ .commit) (hr : l.ctl.tok ≠ .release)
    (hsl : r.ctl.tok ≠ .scrubL) (ho : l.ctl.tok = .openR) :
    (MainClearV3 l → MainClearV3 (rowV3 hψ (by decide) h2 l r).1) ∧
    (MainClearV3 r → MainClearV3 (rowV3 hψ (by decide) h2 l r).2) := by
  simpa [rowV3, hs, hw, hc, hr, hsl, ho] using openRStage_mainClear l r


private theorem mainClear_sealedProposal_install
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ) :
    MainClearV3
      (install l (sealedProposalV3 hψ (by decide : 0 < 2) h2 l r).1) ∧
    MainClearV3
      (install r (sealedProposalV3 hψ (by decide : 0 < 2) h2 l r).2) := by
  unfold sealedProposalV3
  constructor
  · unfold MainClearV3 R2CoherenceBranches.MainClear
    simp [eraseCellV3, install, R2Coherence.raw,
      R2Coherence.clearMainPhys,
      PPLLExpiringComparisonRepair.clearComparisonCarrier]
  · unfold MainClearV3 R2CoherenceBranches.MainClear
    simp [eraseCellV3, install, R2Coherence.raw,
      R2Coherence.clearMainPhys,
      PPLLExpiringComparisonRepair.clearComparisonCarrier]

private theorem sealedStage_mainClear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ) :
    (MainClearV3 l →
      MainClearV3 (sealedStageV3 hψ (by decide : 0 < 2) h2 l r).1) ∧
    (MainClearV3 r →
      MainClearV3 (sealedStageV3 hψ (by decide : 0 < 2) h2 l r).2) := by
  by_cases hlaunch :
      (atRootB l && successorB l r && writerQuiet l && writerQuiet r) = true
  · rw [show sealedStageV3 hψ (by decide : 0 < 2) h2 l r =
      (setControl l .releasing .release, r) by
        simp [sealedStageV3, hlaunch]]
    exact ⟨mainClear_setControl l .releasing .release, fun h => h⟩
  · let q := sealedProposalV3 hψ (by decide : 0 < 2) h2 l r
    by_cases hrel :
        R2Coherence.pairRelabels l.phys r.phys q.1 q.2 = true
    · rw [show sealedStageV3 hψ (by decide : 0 < 2) h2 l r = (l, r) by
          simp [sealedStageV3, hlaunch, q, hrel]]
      exact ⟨fun h => h, fun h => h⟩
    · rw [show sealedStageV3 hψ (by decide : 0 < 2) h2 l r =
        (install l q.1, install r q.2) by
          simp [sealedStageV3, hlaunch, q, hrel]]
      have hq := mainClear_sealedProposal_install hψ h2 l r
      constructor
      · intro _
        simpa [q] using hq.1
      · intro _
        simpa [q] using hq.2

private theorem openHazardStage_mainClear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hh :
      (let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
       pairHazardV3 l.phys r.phys q.1 q.2 = true)) :
    (MainClearV3 l →
      MainClearV3 (openStageV3 hψ (by decide : 0 < 2) h2 l r).1) ∧
    (MainClearV3 r →
      MainClearV3 (openStageV3 hψ (by decide : 0 < 2) h2 l r).2) := by
  let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
  have hhq : pairHazardV3 l.phys r.phys q.1 q.2 = true := by
    simpa [q] using hh
  by_cases he : endpointHazardV3 r.phys q.2 = true
  · rw [show openStageV3 hψ (by decide : 0 < 2) h2 l r =
      (l, startClosing r) by
        simp [openStageV3, q, hhq, he]]
    exact ⟨fun h => h, mainClear_startClosing r⟩
  · rw [show openStageV3 hψ (by decide : 0 < 2) h2 l r =
      (startClosing l, r) by
        simp [openStageV3, q, hhq, he]]
    exact ⟨mainClear_startClosing l, fun h => h⟩

private theorem normalizePassive_mainClear
    (l r : Cell ψ κ τ) :
    (MainClearV3 l → MainClearV3 (normalizePassiveV3 l r).1) ∧
    (MainClearV3 r → MainClearV3 (normalizePassiveV3 l r).2) := by
  by_cases hp : passiveEdgeOKV3 l r = true
  · rw [normalizePassiveV3_good_edge l r hp]
    exact ⟨fun h => h, mainClear_startClosing r⟩
  · have hp0 : passiveEdgeOKV3 l r = false := Bool.eq_false_iff.mpr hp
    rw [normalizePassiveV3_bad_edge l r hp0]
    exact ⟨fun _ => mainClear_cleared l .open .none,
      fun _ => mainClear_cleared r .open .none⟩

private theorem mixedStage_mainClear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hm :
      ¬ (l.ctl.tok = .none ∧ r.ctl.tok = .none) ∨
      (l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
        ¬ (l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed) ∧
        ¬ (l.ctl.mark = .open ∧ r.ctl.mark = .open))) :
    (MainClearV3 l → MainClearV3
      (ordinaryStageV3 hψ (by decide : 0 < 2) h2 l r).1) ∧
    (MainClearV3 r → MainClearV3
      (ordinaryStageV3 hψ (by decide : 0 < 2) h2 l r).2) := by
  rcases hm with hnone | ⟨hln, hrn, hseal, hopen⟩
  · simpa [ordinaryStageV3, hnone]
  · simpa [ordinaryStageV3, hln, hrn, hseal, hopen] using
      (normalizePassive_mainClear l r)

private theorem branch_mixed_shape_inv
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .mixed) :
    ¬ (l.ctl.tok = .none ∧ r.ctl.tok = .none) ∨
    (l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
      ¬ (l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed) ∧
      ¬ (l.ctl.mark = .open ∧ r.ctl.mark = .open)) := by
  rcases branchAtV3_cases hψ h2 l r with
    hseek | hsweep | hcommit | hrelease | hscrubL | hopenR |
    hsealed | hopenHazard | hopenNoHazard | hmixed
  · rw [hb] at hseek
    cases hseek.1
  · rw [hb] at hsweep
    cases hsweep.1
  · rw [hb] at hcommit
    cases hcommit.1
  · rw [hb] at hrelease
    cases hrelease.1
  · rw [hb] at hscrubL
    cases hscrubL.1
  · rw [hb] at hopenR
    cases hopenR.1
  · rw [hb] at hsealed
    cases hsealed.1
  · rw [hb] at hopenHazard
    cases hopenHazard.1
  · rw [hb] at hopenNoHazard
    cases hopenNoHazard.1
  · rcases hmixed with ⟨_, _, _, _, _, _, _, hm⟩
    exact hm

private theorem row_sealed_mainClear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hln : l.ctl.tok = .none) (hrn : r.ctl.tok = .none)
    (hlm : l.ctl.mark = .sealed) (hrm : r.ctl.mark = .sealed) :
    (MainClearV3 l → MainClearV3
      (rowV3 hψ (by decide : 0 < 2) h2 l r).1) ∧
    (MainClearV3 r → MainClearV3
      (rowV3 hψ (by decide : 0 < 2) h2 l r).2) := by
  simpa [rowV3, hln, hrn, hlm, hrm, ordinaryStageV3] using
    (sealedStage_mainClear hψ h2 l r)

private theorem row_openHazard_mainClear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hln : l.ctl.tok = .none) (hrn : r.ctl.tok = .none)
    (hlm : l.ctl.mark = .open) (hrm : r.ctl.mark = .open)
    (hh :
      (let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
       pairHazardV3 l.phys r.phys q.1 q.2 = true)) :
    (MainClearV3 l → MainClearV3
      (rowV3 hψ (by decide : 0 < 2) h2 l r).1) ∧
    (MainClearV3 r → MainClearV3
      (rowV3 hψ (by decide : 0 < 2) h2 l r).2) := by
  simpa [rowV3, hln, hrn, hlm, hrm, ordinaryStageV3] using
    (openHazardStage_mainClear hψ h2 l r hh)

private theorem row_mixed_mainClear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hs : r.ctl.tok ≠ .seek) (hw : l.ctl.tok ≠ .sweep)
    (hc : r.ctl.tok ≠ .commit) (hr : l.ctl.tok ≠ .release)
    (hsl : r.ctl.tok ≠ .scrubL) (ho : l.ctl.tok ≠ .openR)
    (hm :
      ¬ (l.ctl.tok = .none ∧ r.ctl.tok = .none) ∨
      (l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
        ¬ (l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed) ∧
        ¬ (l.ctl.mark = .open ∧ r.ctl.mark = .open))) :
    (MainClearV3 l → MainClearV3
      (rowV3 hψ (by decide : 0 < 2) h2 l r).1) ∧
    (MainClearV3 r → MainClearV3
      (rowV3 hψ (by decide : 0 < 2) h2 l r).2) := by
  simpa [rowV3, hs, hw, hc, hr, hsl, ho] using
    (mixedStage_mainClear hψ h2 l r hm)

theorem rowMainClearFact_holds :
    R2CoherenceV31FootprintCover2R.RowMainClearFactV31 ψ κ τ := by
  unfold R2CoherenceV31FootprintCover2R.RowMainClearFactV31
  intro b hψ h2 l r hb hn
  cases b with
  | seek =>
      exact row_seek_mainClear hψ h2 l r
        (branch_seek_inv hψ h2 l r hb)
  | sweep =>
      rcases branch_sweep_inv hψ h2 l r hb with ⟨hs, hw⟩
      exact row_sweep_mainClear hψ h2 l r hs hw
  | commit =>
      rcases branch_commit_inv hψ h2 l r hb with ⟨hs, hw, hc⟩
      exact row_commit_mainClear hψ h2 l r hs hw hc
  | release =>
      rcases branch_release_inv hψ h2 l r hb with ⟨hs, hw, hc, hr⟩
      exact row_release_mainClear hψ h2 l r hs hw hc hr
  | scrubL =>
      rcases branch_scrubL_inv hψ h2 l r hb with ⟨hs, hw, hc, hr, hsl⟩
      exact row_scrubL_mainClear hψ h2 l r hs hw hc hr hsl
  | openR =>
      rcases branch_openR_inv hψ h2 l r hb with ⟨hs, hw, hc, hr, hsl, ho⟩
      exact row_openR_mainClear hψ h2 l r hs hw hc hr hsl ho
  | sealed =>
      rcases branch_sealed_inv hψ h2 l r hb with ⟨hln, hrn, hlm, hrm⟩
      exact row_sealed_mainClear hψ h2 l r hln hrn hlm hrm
  | openHazard =>
      rcases branch_openHazard_inv hψ h2 l r hb with
        ⟨hln, hrn, hlm, hrm, hh⟩
      exact row_openHazard_mainClear hψ h2 l r hln hrn hlm hrm hh
  | openNoHazard =>
      exact (hn rfl).elim
  | mixed =>
      rcases branch_mixed_inv hψ h2 l r hb with ⟨hs, hw, hc, hr, hsl, ho⟩
      have hm := branch_mixed_shape_inv hψ h2 l r hb
      exact row_mixed_mainClear hψ h2 l r hs hw hc hr hsl ho hm

private theorem seekStage_noScrubL
    (l r : Cell ψ κ τ) :
    ((seekStageV3 l r).1.ctl.tok = .scrubL → l.ctl.tok = .scrubL) ∧
    ((seekStageV3 l r).2.ctl.tok = .scrubL → r.ctl.tok = .scrubL) := by
  by_cases hr : atRootB r = true
  · rw [show seekStageV3 l r = (l, setControl r .closing .sweep) by
      simp [seekStageV3, hr]]
    simp [setControl]
  · by_cases hl : atRootB l = true
    · rw [show seekStageV3 l r =
        (setControl l .closing .sweep, setControl r .closing .none) by
        simp [seekStageV3, hr, hl]]
      simp [setControl]
    · rw [show seekStageV3 l r =
        (setControl l .closing .seek, setControl r .closing .none) by
        simp [seekStageV3, hr, hl]]
      simp [setControl]

private theorem sweepStage_noScrubL
    (l r : Cell ψ κ τ) :
    ((sweepStageV3 l r).1.ctl.tok = .scrubL → l.ctl.tok = .scrubL) ∧
    ((sweepStageV3 l r).2.ctl.tok = .scrubL → r.ctl.tok = .scrubL) := by
  by_cases hs : successorB l r = true
  · by_cases ht : atTerminalB r = true
    · rw [show sweepStageV3 l r =
        (setControl (clearMain l) .closing .none,
          setControl (clearMain r) .closing .commit) by
        simp [sweepStageV3, hs, ht]]
      simp [setControl]
    · rw [show sweepStageV3 l r =
        (setControl (clearMain l) .closing .none,
          setControl (clearMain r) .closing .sweep) by
        simp [sweepStageV3, hs, ht]]
      simp [setControl]
  · rw [show sweepStageV3 l r = (startClosing l, r) by
      simp [sweepStageV3, hs]]
    simp [startClosing, setControl]

private theorem commitStage_noScrubL
    (l r : Cell ψ κ τ) :
    ((commitStageV3 l r).1.ctl.tok = .scrubL → l.ctl.tok = .scrubL) ∧
    ((commitStageV3 l r).2.ctl.tok = .scrubL → r.ctl.tok = .scrubL) := by
  by_cases hr : atRootB r = true
  · rw [show commitStageV3 l r =
      (l, setControl (clearMain r) .sealed .none) by
      simp [commitStageV3, hr]]
    simp [setControl]
  · by_cases hl : atRootB l = true
    · rw [show commitStageV3 l r =
        (setControl (clearMain l) .sealed .none,
          setControl (clearMain r) .sealed .none) by
        simp [commitStageV3, hr, hl]]
      simp [setControl]
    · rw [show commitStageV3 l r =
        (setControl (clearMain l) .closing .commit,
          setControl (clearMain r) .sealed .none) by
        simp [commitStageV3, hr, hl]]
      simp [setControl]

private theorem openRStage_noScrubL
    (l r : Cell ψ κ τ) :
    ((openRStageV3 l r).1.ctl.tok = .scrubL → l.ctl.tok = .scrubL) ∧
    ((openRStageV3 l r).2.ctl.tok = .scrubL → r.ctl.tok = .scrubL) := by
  by_cases hs : successorB l r = true
  · by_cases ht : atTerminalB r = true
    · rw [show openRStageV3 l r =
        (setControl (clearMain l) .open .none,
          setControl (clearMain r) .open .none) by
        simp [openRStageV3, hs, ht]]
      simp [setControl]
    · rw [show openRStageV3 l r =
        (setControl (clearMain l) .open .none,
          setControl (clearMain r) .releasing .openR) by
        simp [openRStageV3, hs, ht]]
      simp [setControl]
  · rw [show openRStageV3 l r = (startClosing l, r) by
      simp [openRStageV3, hs]]
    simp [startClosing, setControl]

private theorem sealedStage_noScrubL
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ) :
    ((sealedStageV3 hψ (by decide : 0 < 2) h2 l r).1.ctl.tok = .scrubL →
      l.ctl.tok = .scrubL) ∧
    ((sealedStageV3 hψ (by decide : 0 < 2) h2 l r).2.ctl.tok = .scrubL →
      r.ctl.tok = .scrubL) := by
  by_cases hlaunch :
      (atRootB l && successorB l r && writerQuiet l && writerQuiet r) = true
  · rw [show sealedStageV3 hψ (by decide : 0 < 2) h2 l r =
      (setControl l .releasing .release, r) by
      simp [sealedStageV3, hlaunch]]
    simp [setControl]
  · let q := sealedProposalV3 hψ (by decide : 0 < 2) h2 l r
    by_cases hrel : R2Coherence.pairRelabels l.phys r.phys q.1 q.2 = true
    · rw [show sealedStageV3 hψ (by decide : 0 < 2) h2 l r = (l, r) by
        simp [sealedStageV3, hlaunch, q, hrel]]
      simp
    · rw [show sealedStageV3 hψ (by decide : 0 < 2) h2 l r =
        (install l q.1, install r q.2) by
        simp [sealedStageV3, hlaunch, q, hrel]]
      simp [install]

private theorem openHazardStage_noScrubL
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hh :
      (let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
       pairHazardV3 l.phys r.phys q.1 q.2 = true)) :
    ((openStageV3 hψ (by decide : 0 < 2) h2 l r).1.ctl.tok = .scrubL →
      l.ctl.tok = .scrubL) ∧
    ((openStageV3 hψ (by decide : 0 < 2) h2 l r).2.ctl.tok = .scrubL →
      r.ctl.tok = .scrubL) := by
  let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
  have hhq : pairHazardV3 l.phys r.phys q.1 q.2 = true := by
    simpa [q] using hh
  by_cases he : endpointHazardV3 r.phys q.2 = true
  · rw [show openStageV3 hψ (by decide : 0 < 2) h2 l r =
      (l, startClosing r) by
      simp [openStageV3, q, hhq, he]]
    simp [startClosing, setControl]
  · rw [show openStageV3 hψ (by decide : 0 < 2) h2 l r =
      (startClosing l, r) by
      simp [openStageV3, q, hhq, he]]
    simp [startClosing, setControl]

private theorem openNoHazardStage_noScrubL
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hh :
      (let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
       pairHazardV3 l.phys r.phys q.1 q.2 = false)) :
    ((openStageV3 hψ (by decide : 0 < 2) h2 l r).1.ctl.tok = .scrubL →
      l.ctl.tok = .scrubL) ∧
    ((openStageV3 hψ (by decide : 0 < 2) h2 l r).2.ctl.tok = .scrubL →
      r.ctl.tok = .scrubL) := by
  let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
  have hhq : pairHazardV3 l.phys r.phys q.1 q.2 = false := by
    simpa [q] using hh
  rw [show openStageV3 hψ (by decide : 0 < 2) h2 l r =
      (install l q.1, install r q.2) by
      simp [openStageV3, q, hhq]]
  simp [install]

private theorem mixedStage_noScrubL
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hm :
      ¬ (l.ctl.tok = .none ∧ r.ctl.tok = .none) ∨
      (l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
        ¬ (l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed) ∧
        ¬ (l.ctl.mark = .open ∧ r.ctl.mark = .open))) :
    ((ordinaryStageV3 hψ (by decide : 0 < 2) h2 l r).1.ctl.tok = .scrubL →
      l.ctl.tok = .scrubL) ∧
    ((ordinaryStageV3 hψ (by decide : 0 < 2) h2 l r).2.ctl.tok = .scrubL →
      r.ctl.tok = .scrubL) := by
  rcases hm with hnone | ⟨hln, hrn, hseal, hopen⟩
  · rw [show ordinaryStageV3 hψ (by decide : 0 < 2) h2 l r = (l, r) by
      simp [ordinaryStageV3, hnone]]
    simp
  · rw [show ordinaryStageV3 hψ (by decide : 0 < 2) h2 l r =
      normalizePassiveV3 l r by
      simp [ordinaryStageV3, hln, hrn, hseal, hopen]]
    by_cases hp : passiveEdgeOKV3 l r = true
    · rw [normalizePassiveV3_good_edge l r hp]
      simp [startClosing, setControl]
    · have hp0 : passiveEdgeOKV3 l r = false := Bool.eq_false_iff.mpr hp
      rw [normalizePassiveV3_bad_edge l r hp0]
      simp [setControl]

private theorem row_seek_scrubBack
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hs : r.ctl.tok = .seek) :
    ((rowV3 hψ (by decide : 0 < 2) h2 l r).1.ctl.tok = .scrubL →
      l.ctl.tok = .scrubL) ∧
    ((rowV3 hψ (by decide : 0 < 2) h2 l r).2.ctl.tok = .scrubL →
      r.ctl.tok = .scrubL) := by
  simpa [rowV3, hs] using seekStage_noScrubL l r

private theorem row_sweep_scrubBack
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hs : r.ctl.tok ≠ .seek) (hw : l.ctl.tok = .sweep) :
    ((rowV3 hψ (by decide : 0 < 2) h2 l r).1.ctl.tok = .scrubL →
      l.ctl.tok = .scrubL) ∧
    ((rowV3 hψ (by decide : 0 < 2) h2 l r).2.ctl.tok = .scrubL →
      r.ctl.tok = .scrubL) := by
  simpa [rowV3, hs, hw] using sweepStage_noScrubL l r

private theorem row_commit_scrubBack
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hs : r.ctl.tok ≠ .seek) (hw : l.ctl.tok ≠ .sweep)
    (hc : r.ctl.tok = .commit) :
    ((rowV3 hψ (by decide : 0 < 2) h2 l r).1.ctl.tok = .scrubL →
      l.ctl.tok = .scrubL) ∧
    ((rowV3 hψ (by decide : 0 < 2) h2 l r).2.ctl.tok = .scrubL →
      r.ctl.tok = .scrubL) := by
  simpa [rowV3, hs, hw, hc] using commitStage_noScrubL l r

private theorem row_openR_scrubBack
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hs : r.ctl.tok ≠ .seek) (hw : l.ctl.tok ≠ .sweep)
    (hc : r.ctl.tok ≠ .commit) (hr : l.ctl.tok ≠ .release)
    (hsl : r.ctl.tok ≠ .scrubL) (ho : l.ctl.tok = .openR) :
    ((rowV3 hψ (by decide : 0 < 2) h2 l r).1.ctl.tok = .scrubL →
      l.ctl.tok = .scrubL) ∧
    ((rowV3 hψ (by decide : 0 < 2) h2 l r).2.ctl.tok = .scrubL →
      r.ctl.tok = .scrubL) := by
  simpa [rowV3, hs, hw, hc, hr, hsl, ho] using openRStage_noScrubL l r

private theorem row_sealed_scrubBack
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hln : l.ctl.tok = .none) (hrn : r.ctl.tok = .none)
    (hlm : l.ctl.mark = .sealed) (hrm : r.ctl.mark = .sealed) :
    ((rowV3 hψ (by decide : 0 < 2) h2 l r).1.ctl.tok = .scrubL →
      l.ctl.tok = .scrubL) ∧
    ((rowV3 hψ (by decide : 0 < 2) h2 l r).2.ctl.tok = .scrubL →
      r.ctl.tok = .scrubL) := by
  simpa [rowV3, hln, hrn, hlm, hrm, ordinaryStageV3] using
    (sealedStage_noScrubL hψ h2 l r)

private theorem row_openHazard_scrubBack
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hln : l.ctl.tok = .none) (hrn : r.ctl.tok = .none)
    (hlm : l.ctl.mark = .open) (hrm : r.ctl.mark = .open)
    (hh :
      (let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
       pairHazardV3 l.phys r.phys q.1 q.2 = true)) :
    ((rowV3 hψ (by decide : 0 < 2) h2 l r).1.ctl.tok = .scrubL →
      l.ctl.tok = .scrubL) ∧
    ((rowV3 hψ (by decide : 0 < 2) h2 l r).2.ctl.tok = .scrubL →
      r.ctl.tok = .scrubL) := by
  simpa [rowV3, hln, hrn, hlm, hrm, ordinaryStageV3] using
    (openHazardStage_noScrubL hψ h2 l r hh)

private theorem row_openNoHazard_scrubBack
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hln : l.ctl.tok = .none) (hrn : r.ctl.tok = .none)
    (hlm : l.ctl.mark = .open) (hrm : r.ctl.mark = .open)
    (hh :
      (let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
       pairHazardV3 l.phys r.phys q.1 q.2 = false)) :
    ((rowV3 hψ (by decide : 0 < 2) h2 l r).1.ctl.tok = .scrubL →
      l.ctl.tok = .scrubL) ∧
    ((rowV3 hψ (by decide : 0 < 2) h2 l r).2.ctl.tok = .scrubL →
      r.ctl.tok = .scrubL) := by
  simpa [rowV3, hln, hrn, hlm, hrm, ordinaryStageV3] using
    (openNoHazardStage_noScrubL hψ h2 l r hh)

private theorem row_mixed_scrubBack
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hs : r.ctl.tok ≠ .seek) (hw : l.ctl.tok ≠ .sweep)
    (hc : r.ctl.tok ≠ .commit) (hr : l.ctl.tok ≠ .release)
    (hsl : r.ctl.tok ≠ .scrubL) (ho : l.ctl.tok ≠ .openR)
    (hm :
      ¬ (l.ctl.tok = .none ∧ r.ctl.tok = .none) ∨
      (l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
        ¬ (l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed) ∧
        ¬ (l.ctl.mark = .open ∧ r.ctl.mark = .open))) :
    ((rowV3 hψ (by decide : 0 < 2) h2 l r).1.ctl.tok = .scrubL →
      l.ctl.tok = .scrubL) ∧
    ((rowV3 hψ (by decide : 0 < 2) h2 l r).2.ctl.tok = .scrubL →
      r.ctl.tok = .scrubL) := by
  simpa [rowV3, hs, hw, hc, hr, hsl, ho] using
    (mixedStage_noScrubL hψ h2 l r hm)

theorem rowScrubBackFact_holds :
    R2CoherenceV31FootprintCover2R.RowScrubBackFactV31 ψ κ τ := by
  unfold R2CoherenceV31FootprintCover2R.RowScrubBackFactV31
  intro b hψ h2 l r hb hRelease hScrubL
  cases b with
  | seek =>
      exact row_seek_scrubBack hψ h2 l r
        (branch_seek_inv hψ h2 l r hb)
  | sweep =>
      rcases branch_sweep_inv hψ h2 l r hb with ⟨hs, hw⟩
      exact row_sweep_scrubBack hψ h2 l r hs hw
  | commit =>
      rcases branch_commit_inv hψ h2 l r hb with ⟨hs, hw, hc⟩
      exact row_commit_scrubBack hψ h2 l r hs hw hc
  | release =>
      exact (hRelease rfl).elim
  | scrubL =>
      exact (hScrubL rfl).elim
  | openR =>
      rcases branch_openR_inv hψ h2 l r hb with ⟨hs, hw, hc, hr, hsl, ho⟩
      exact row_openR_scrubBack hψ h2 l r hs hw hc hr hsl ho
  | sealed =>
      rcases branch_sealed_inv hψ h2 l r hb with ⟨hln, hrn, hlm, hrm⟩
      exact row_sealed_scrubBack hψ h2 l r hln hrn hlm hrm
  | openHazard =>
      rcases branch_openHazard_inv hψ h2 l r hb with
        ⟨hln, hrn, hlm, hrm, hh⟩
      exact row_openHazard_scrubBack hψ h2 l r hln hrn hlm hrm hh
  | openNoHazard =>
      rcases branch_openNoHazard_inv hψ h2 l r hb with
        ⟨hln, hrn, hlm, hrm, hh⟩
      exact row_openNoHazard_scrubBack hψ h2 l r hln hrn hlm hrm hh
  | mixed =>
      rcases branch_mixed_inv hψ h2 l r hb with ⟨hs, hw, hc, hr, hsl, ho⟩
      have hm := branch_mixed_shape_inv hψ h2 l r hb
      exact row_mixed_scrubBack hψ h2 l r hs hw hc hr hsl ho hm

private theorem freshnessClear_setControl
    (u : Cell ψ κ τ) (m : R2Coherence.Mark) (t : TokenV3)
    (h : R2CoherenceV31MainClearTruth.FreshnessClearV31 u) :
    R2CoherenceV31MainClearTruth.FreshnessClearV31
      (setControl u m t) := by
  unfold R2CoherenceV31MainClearTruth.FreshnessClearV31 at h ⊢
  change u.phys.base.core.core.path = .bot at h
  change u.phys.base.core.core.path = .bot
  exact h

private theorem freshnessClear_startClosing
    (u : Cell ψ κ τ)
    (h : R2CoherenceV31MainClearTruth.FreshnessClearV31 u) :
    R2CoherenceV31MainClearTruth.FreshnessClearV31 (startClosing u) := by
  simpa [startClosing] using
    (freshnessClear_setControl u .closing .seek h)

private theorem freshnessClear_cleared
    (u : Cell ψ κ τ) (m : R2Coherence.Mark) (t : TokenV3) :
    R2CoherenceV31MainClearTruth.FreshnessClearV31
      (setControl (clearMain u) m t) := by
  exact R2CoherenceV31MainClearTruth.freshnessClear_of_mainClear _
    (mainClear_cleared u m t)

private theorem seekStage_freshnessClear
    (l r : Cell ψ κ τ) :
    (R2CoherenceV31MainClearTruth.FreshnessClearV31 l →
      R2CoherenceV31MainClearTruth.FreshnessClearV31 (seekStageV3 l r).1) ∧
    (R2CoherenceV31MainClearTruth.FreshnessClearV31 r →
      R2CoherenceV31MainClearTruth.FreshnessClearV31 (seekStageV3 l r).2) := by
  by_cases hr : atRootB r = true
  · rw [show seekStageV3 l r = (l, setControl r .closing .sweep) by
      simp [seekStageV3, hr]]
    exact ⟨fun h => h, freshnessClear_setControl r .closing .sweep⟩
  · by_cases hl : atRootB l = true
    · rw [show seekStageV3 l r =
        (setControl l .closing .sweep, setControl r .closing .none) by
        simp [seekStageV3, hr, hl]]
      exact ⟨freshnessClear_setControl l .closing .sweep,
        freshnessClear_setControl r .closing .none⟩
    · rw [show seekStageV3 l r =
        (setControl l .closing .seek, setControl r .closing .none) by
        simp [seekStageV3, hr, hl]]
      exact ⟨freshnessClear_setControl l .closing .seek,
        freshnessClear_setControl r .closing .none⟩

private theorem sweepStage_freshnessClear
    (l r : Cell ψ κ τ) :
    (R2CoherenceV31MainClearTruth.FreshnessClearV31 l →
      R2CoherenceV31MainClearTruth.FreshnessClearV31 (sweepStageV3 l r).1) ∧
    (R2CoherenceV31MainClearTruth.FreshnessClearV31 r →
      R2CoherenceV31MainClearTruth.FreshnessClearV31 (sweepStageV3 l r).2) := by
  by_cases hs : successorB l r = true
  · by_cases ht : atTerminalB r = true
    · simp [sweepStageV3, hs, ht]
      exact ⟨fun _ => freshnessClear_cleared l .closing .none,
        fun _ => freshnessClear_cleared r .closing .commit⟩
    · simp [sweepStageV3, hs, ht]
      exact ⟨fun _ => freshnessClear_cleared l .closing .none,
        fun _ => freshnessClear_cleared r .closing .sweep⟩
  · rw [show sweepStageV3 l r = (startClosing l, r) by
      simp [sweepStageV3, hs]]
    exact ⟨freshnessClear_startClosing l, fun h => h⟩

private theorem commitStage_freshnessClear
    (l r : Cell ψ κ τ) :
    (R2CoherenceV31MainClearTruth.FreshnessClearV31 l →
      R2CoherenceV31MainClearTruth.FreshnessClearV31 (commitStageV3 l r).1) ∧
    (R2CoherenceV31MainClearTruth.FreshnessClearV31 r →
      R2CoherenceV31MainClearTruth.FreshnessClearV31 (commitStageV3 l r).2) := by
  by_cases hr : atRootB r = true
  · rw [show commitStageV3 l r =
      (l, setControl (clearMain r) .sealed .none) by
        simp [commitStageV3, hr]]
    exact ⟨fun h => h, fun _ => freshnessClear_cleared r .sealed .none⟩
  · by_cases hl : atRootB l = true
    · rw [show commitStageV3 l r =
        (setControl (clearMain l) .sealed .none,
          setControl (clearMain r) .sealed .none) by
          simp [commitStageV3, hr, hl]]
      exact ⟨fun _ => freshnessClear_cleared l .sealed .none,
        fun _ => freshnessClear_cleared r .sealed .none⟩
    · rw [show commitStageV3 l r =
        (setControl (clearMain l) .closing .commit,
          setControl (clearMain r) .sealed .none) by
          simp [commitStageV3, hr, hl]]
      exact ⟨fun _ => freshnessClear_cleared l .closing .commit,
        fun _ => freshnessClear_cleared r .sealed .none⟩

private theorem releaseStage_freshnessClear
    (l r : Cell ψ κ τ) :
    (R2CoherenceV31MainClearTruth.FreshnessClearV31 l →
      R2CoherenceV31MainClearTruth.FreshnessClearV31 (releaseStageV3 l r).1) ∧
    (R2CoherenceV31MainClearTruth.FreshnessClearV31 r →
      R2CoherenceV31MainClearTruth.FreshnessClearV31 (releaseStageV3 l r).2) := by
  by_cases hs : successorB l r = true
  · by_cases hq : writerQuiet r = true
    · by_cases ht : atTerminalB r = true
      · rw [show releaseStageV3 l r =
          (setControl l .releasing .none,
            setControl r .releasing .scrubL) by
            simp [releaseStageV3, hs, hq, ht]]
        exact ⟨freshnessClear_setControl l .releasing .none,
          freshnessClear_setControl r .releasing .scrubL⟩
      · rw [show releaseStageV3 l r =
          (setControl l .releasing .none,
            setControl r .releasing .release) by
            simp [releaseStageV3, hs, hq, ht]]
        exact ⟨freshnessClear_setControl l .releasing .none,
          freshnessClear_setControl r .releasing .release⟩
    · by_cases hl : atRootB l = true
      · rw [show releaseStageV3 l r =
          (setControl l .sealed .none, r) by
            simp [releaseStageV3, hs, hq, hl]]
        exact ⟨freshnessClear_setControl l .sealed .none, fun h => h⟩
      · rw [show releaseStageV3 l r =
          (setControl l .closing .commit, r) by
            simp [releaseStageV3, hs, hq, hl]]
        exact ⟨freshnessClear_setControl l .closing .commit, fun h => h⟩
  · rw [show releaseStageV3 l r = (startClosing l, r) by
      simp [releaseStageV3, hs]]
    exact ⟨freshnessClear_startClosing l, fun h => h⟩

private theorem scrubLStage_freshnessClear
    (l r : Cell ψ κ τ) :
    (R2CoherenceV31MainClearTruth.FreshnessClearV31 l →
      R2CoherenceV31MainClearTruth.FreshnessClearV31 (scrubLStageV3 l r).1) ∧
    (R2CoherenceV31MainClearTruth.FreshnessClearV31 r →
      R2CoherenceV31MainClearTruth.FreshnessClearV31 (scrubLStageV3 l r).2) := by
  by_cases hs : successorB l r = true
  · by_cases hr : atRootB r = true
    · rw [show scrubLStageV3 l r = (l, startClosing r) by
        simp [scrubLStageV3, hs, hr]]
      exact ⟨fun h => h, freshnessClear_startClosing r⟩
    · by_cases hl : atRootB l = true
      · simp [scrubLStageV3, hs, hr, hl]
        exact ⟨fun _ => freshnessClear_cleared l .releasing .openR,
          fun _ => freshnessClear_cleared r .releasing .none⟩
      · simp [scrubLStageV3, hs, hr, hl]
        exact ⟨fun _ => freshnessClear_cleared l .releasing .scrubL,
          fun _ => freshnessClear_cleared r .releasing .none⟩
  · rw [show scrubLStageV3 l r = (l, startClosing r) by
      simp [scrubLStageV3, hs]]
    exact ⟨fun h => h, freshnessClear_startClosing r⟩

private theorem openRStage_freshnessClear
    (l r : Cell ψ κ τ) :
    (R2CoherenceV31MainClearTruth.FreshnessClearV31 l →
      R2CoherenceV31MainClearTruth.FreshnessClearV31 (openRStageV3 l r).1) ∧
    (R2CoherenceV31MainClearTruth.FreshnessClearV31 r →
      R2CoherenceV31MainClearTruth.FreshnessClearV31 (openRStageV3 l r).2) := by
  by_cases hs : successorB l r = true
  · by_cases ht : atTerminalB r = true
    · simp [openRStageV3, hs, ht]
      exact ⟨fun _ => freshnessClear_cleared l .open .none,
        fun _ => freshnessClear_cleared r .open .none⟩
    · simp [openRStageV3, hs, ht]
      exact ⟨fun _ => freshnessClear_cleared l .open .none,
        fun _ => freshnessClear_cleared r .releasing .openR⟩
  · rw [show openRStageV3 l r = (startClosing l, r) by
      simp [openRStageV3, hs]]
    exact ⟨freshnessClear_startClosing l, fun h => h⟩

private theorem sealedStage_freshnessClear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ) :
    (R2CoherenceV31MainClearTruth.FreshnessClearV31 l →
      R2CoherenceV31MainClearTruth.FreshnessClearV31
        (sealedStageV3 hψ (by decide : 0 < 2) h2 l r).1) ∧
    (R2CoherenceV31MainClearTruth.FreshnessClearV31 r →
      R2CoherenceV31MainClearTruth.FreshnessClearV31
        (sealedStageV3 hψ (by decide : 0 < 2) h2 l r).2) := by
  by_cases hlaunch :
      (atRootB l && successorB l r && writerQuiet l && writerQuiet r) = true
  · rw [show sealedStageV3 hψ (by decide : 0 < 2) h2 l r =
      (setControl l .releasing .release, r) by
        simp [sealedStageV3, hlaunch]]
    exact ⟨freshnessClear_setControl l .releasing .release, fun h => h⟩
  · let q := sealedProposalV3 hψ (by decide : 0 < 2) h2 l r
    by_cases hrel : R2Coherence.pairRelabels l.phys r.phys q.1 q.2 = true
    · rw [show sealedStageV3 hψ (by decide : 0 < 2) h2 l r = (l, r) by
          simp [sealedStageV3, hlaunch, q, hrel]]
      exact ⟨fun h => h, fun h => h⟩
    · rw [show sealedStageV3 hψ (by decide : 0 < 2) h2 l r =
        (install l q.1, install r q.2) by
          simp [sealedStageV3, hlaunch, q, hrel]]
      have hq := mainClear_sealedProposal_install hψ h2 l r
      constructor
      · intro _
        simpa [q] using
          (R2CoherenceV31MainClearTruth.freshnessClear_of_mainClear _ hq.1)
      · intro _
        simpa [q] using
          (R2CoherenceV31MainClearTruth.freshnessClear_of_mainClear _ hq.2)

private theorem openHazardStage_freshnessClear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hh :
      (let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
       pairHazardV3 l.phys r.phys q.1 q.2 = true)) :
    (R2CoherenceV31MainClearTruth.FreshnessClearV31 l →
      R2CoherenceV31MainClearTruth.FreshnessClearV31
        (openStageV3 hψ (by decide : 0 < 2) h2 l r).1) ∧
    (R2CoherenceV31MainClearTruth.FreshnessClearV31 r →
      R2CoherenceV31MainClearTruth.FreshnessClearV31
        (openStageV3 hψ (by decide : 0 < 2) h2 l r).2) := by
  let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
  have hhq : pairHazardV3 l.phys r.phys q.1 q.2 = true := by
    simpa [q] using hh
  by_cases he : endpointHazardV3 r.phys q.2 = true
  · rw [show openStageV3 hψ (by decide : 0 < 2) h2 l r =
      (l, startClosing r) by
        simp [openStageV3, q, hhq, he]]
    exact ⟨fun h => h, freshnessClear_startClosing r⟩
  · rw [show openStageV3 hψ (by decide : 0 < 2) h2 l r =
      (startClosing l, r) by
        simp [openStageV3, q, hhq, he]]
    exact ⟨freshnessClear_startClosing l, fun h => h⟩

private theorem normalizePassive_freshnessClear
    (l r : Cell ψ κ τ) :
    (R2CoherenceV31MainClearTruth.FreshnessClearV31 l →
      R2CoherenceV31MainClearTruth.FreshnessClearV31 (normalizePassiveV3 l r).1) ∧
    (R2CoherenceV31MainClearTruth.FreshnessClearV31 r →
      R2CoherenceV31MainClearTruth.FreshnessClearV31 (normalizePassiveV3 l r).2) := by
  by_cases hp : passiveEdgeOKV3 l r = true
  · rw [normalizePassiveV3_good_edge l r hp]
    exact ⟨fun h => h, freshnessClear_startClosing r⟩
  · have hp0 : passiveEdgeOKV3 l r = false := Bool.eq_false_iff.mpr hp
    rw [normalizePassiveV3_bad_edge l r hp0]
    exact ⟨fun _ => freshnessClear_cleared l .open .none,
      fun _ => freshnessClear_cleared r .open .none⟩

private theorem mixedStage_freshnessClear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hm :
      ¬ (l.ctl.tok = .none ∧ r.ctl.tok = .none) ∨
      (l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
        ¬ (l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed) ∧
        ¬ (l.ctl.mark = .open ∧ r.ctl.mark = .open))) :
    (R2CoherenceV31MainClearTruth.FreshnessClearV31 l →
      R2CoherenceV31MainClearTruth.FreshnessClearV31
        (ordinaryStageV3 hψ (by decide : 0 < 2) h2 l r).1) ∧
    (R2CoherenceV31MainClearTruth.FreshnessClearV31 r →
      R2CoherenceV31MainClearTruth.FreshnessClearV31
        (ordinaryStageV3 hψ (by decide : 0 < 2) h2 l r).2) := by
  rcases hm with hnone | ⟨hln, hrn, hseal, hopen⟩
  · simpa [ordinaryStageV3, hnone]
  · simpa [ordinaryStageV3, hln, hrn, hseal, hopen] using
      (normalizePassive_freshnessClear l r)

theorem rowFreshFact_holds :
    R2CoherenceV31FootprintCover2R.RowFreshFactV31 ψ κ τ := by
  unfold R2CoherenceV31FootprintCover2R.RowFreshFactV31
  intro b hψ h2 l r hb hn
  cases b with
  | seek =>
      have hs := branch_seek_inv hψ h2 l r hb
      simpa [rowV3, hs] using seekStage_freshnessClear l r
  | sweep =>
      rcases branch_sweep_inv hψ h2 l r hb with ⟨hs, hw⟩
      simpa [rowV3, hs, hw] using sweepStage_freshnessClear l r
  | commit =>
      rcases branch_commit_inv hψ h2 l r hb with ⟨hs, hw, hc⟩
      simpa [rowV3, hs, hw, hc] using commitStage_freshnessClear l r
  | release =>
      rcases branch_release_inv hψ h2 l r hb with ⟨hs, hw, hc, hr⟩
      simpa [rowV3, hs, hw, hc, hr] using releaseStage_freshnessClear l r
  | scrubL =>
      rcases branch_scrubL_inv hψ h2 l r hb with ⟨hs, hw, hc, hr, hsl⟩
      simpa [rowV3, hs, hw, hc, hr, hsl] using
        scrubLStage_freshnessClear l r
  | openR =>
      rcases branch_openR_inv hψ h2 l r hb with ⟨hs, hw, hc, hr, hsl, ho⟩
      simpa [rowV3, hs, hw, hc, hr, hsl, ho] using
        openRStage_freshnessClear l r
  | sealed =>
      rcases branch_sealed_inv hψ h2 l r hb with ⟨hln, hrn, hlm, hrm⟩
      simpa [rowV3, hln, hrn, hlm, hrm, ordinaryStageV3] using
        (sealedStage_freshnessClear hψ h2 l r)
  | openHazard =>
      rcases branch_openHazard_inv hψ h2 l r hb with
        ⟨hln, hrn, hlm, hrm, hh⟩
      simpa [rowV3, hln, hrn, hlm, hrm, ordinaryStageV3] using
        (openHazardStage_freshnessClear hψ h2 l r hh)
  | openNoHazard =>
      exact (hn rfl).elim
  | mixed =>
      rcases branch_mixed_inv hψ h2 l r hb with ⟨hs, hw, hc, hr, hsl, ho⟩
      have hm := branch_mixed_shape_inv hψ h2 l r hb
      simpa [rowV3, hs, hw, hc, hr, hsl, ho] using
        (mixedStage_freshnessClear hψ h2 l r hm)

end R2CoherenceV31RowFacts

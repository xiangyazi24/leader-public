import Leader.Wu.Coherence.Closure

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31Closure2

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure

variable {n ψ κ τ : Nat}

private def erasePairV312
    (q : Cell ψ κ τ × Cell ψ κ τ) :
    R2Coherence.Cell ψ κ τ × R2Coherence.Cell ψ κ τ :=
  (eraseCellV3 q.1, eraseCellV3 q.2)

private theorem branch_sealed_conditions
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .sealed) :
    l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
      l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed := by
  unfold branchAtV3 at hb
  by_cases hSeek : r.ctl.tok = .seek
  · rw [if_pos hSeek] at hb
    cases hb
  · rw [if_neg hSeek] at hb
    by_cases hSweep : l.ctl.tok = .sweep
    · rw [if_pos hSweep] at hb
      cases hb
    · rw [if_neg hSweep] at hb
      by_cases hCommit : r.ctl.tok = .commit
      · rw [if_pos hCommit] at hb
        cases hb
      · rw [if_neg hCommit] at hb
        by_cases hRelease : l.ctl.tok = .release
        · rw [if_pos hRelease] at hb
          cases hb
        · rw [if_neg hRelease] at hb
          by_cases hScrub : r.ctl.tok = .scrubL
          · rw [if_pos hScrub] at hb
            cases hb
          · rw [if_neg hScrub] at hb
            by_cases hOpenR : l.ctl.tok = .openR
            · rw [if_pos hOpenR] at hb
              cases hb
            · rw [if_neg hOpenR] at hb
              by_cases hNone : l.ctl.tok = .none ∧ r.ctl.tok = .none
              · rw [if_pos hNone] at hb
                by_cases hSealed :
                    l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed
                · exact ⟨hNone.1, hNone.2, hSealed.1, hSealed.2⟩
                · rw [if_neg hSealed] at hb
                  by_cases hOpen : l.ctl.mark = .open ∧ r.ctl.mark = .open
                  · rw [if_pos hOpen] at hb
                    by_cases hHaz :
                        pairHazardV3 l.phys r.phys
                            (proposalV3 hψ (by decide : 0 < 2) h2 l r).1
                            (proposalV3 hψ (by decide : 0 < 2) h2 l r).2 = true
                    · simp [hHaz] at hb
                    · simp [hHaz] at hb
                  · rw [if_neg hOpen] at hb
                    cases hb
              · rw [if_neg hNone] at hb
                cases hb

private theorem pairMutation_sealedStageV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ)
    (hl : l.ctl.mark = .sealed) (hr : r.ctl.mark = .sealed) :
    PairQuarantineMutation (eraseCellV3 l) (eraseCellV3 r)
      (erasePairV312
        (sealedStageV3 hψ (by decide : 0 < 2) h2 l r)) := by
  unfold sealedStageV3
  split
  · simp [PairQuarantineMutation, NonOpen, erasePairV312,
      setControl, eraseCellV3, eraseTokenV3, hl, hr]
  · dsimp only
    split
    · simp [PairQuarantineMutation, erasePairV312]
    · simp [PairQuarantineMutation, NonOpen, erasePairV312,
        install, eraseCellV3, eraseTokenV3, hl, hr]

private theorem pairMutation_sealed
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .sealed) :
    PairQuarantineMutation (eraseCellV3 l) (eraseCellV3 r)
      (erasePairV312
        (rowV3 hψ (by decide : 0 < 2) h2 l r)) := by
  rcases branch_sealed_conditions hψ h2 l r hb with
    ⟨hln, hrn, hls, hrs⟩
  simpa [rowV3, ordinaryStageV3, hln, hrn, hls, hrs] using
    (pairMutation_sealedStageV31 hψ h2 l r hls hrs)

private theorem quarantineMutation_stepV312_of_pair
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hPair : PairQuarantineMutation
      (eraseCellV3 (C e))
      (eraseCellV3 (C (ring.rightNeighbor e)))
      (erasePairV312
        (rowV3 hψ (by decide : 0 < 2) h2
          (C e) (C (ring.rightNeighbor e))))) :
    QuarantineMutation
      (eraseCfgV3 C)
      (eraseCfgV3 (stepV3 hψ h2 ring C e)) := by
  rcases hPair with ⟨hLM, hRM, hLN, hRN⟩
  intro p
  by_cases hpe : p = e
  · subst p
    simpa [eraseCfgV3, erasePairV312, stepV3, protocolV3,
      PopulationProtocol.step] using And.intro hLM hLN
  · by_cases hpj : p = ring.rightNeighbor e
    · subst p
      simpa [eraseCfgV3, erasePairV312, stepV3, protocolV3,
        PopulationProtocol.step, hpe] using And.intro hRM hRN
    · have hSame :
        (((eraseCfgV3 C) p).phys ≠ ((eraseCfgV3 C) p).phys →
            NonOpen ((eraseCfgV3 C) p)) ∧
          (NonOpen ((eraseCfgV3 C) p) →
            NonOpen ((eraseCfgV3 C) p)) :=
        ⟨fun h => (h rfl).elim, fun h => h⟩
      simpa [eraseCfgV3, stepV3, protocolV3,
        PopulationProtocol.step, hpe, hpj] using hSame

theorem sealed_coherence
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    BranchCoherenceObligationV31 (κ := κ) (τ := τ)
      hψ h2 ring .sealed := by
  intro C e hClosed hb
  rcases hClosed with ⟨_, hCoh, hSound⟩
  have hPair := pairMutation_sealed hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hMut := quarantineMutation_stepV312_of_pair
    hψ h2 ring C e hPair
  constructor
  · change R2Coherence.CoherentPrefixes ring
      (eraseCfgV3 (stepV3 hψ h2 ring C e))
    exact coherentPrefixes_of_quarantineMutation ring hMut hCoh
  · exact controllerSoundV3_step hψ h2 ring C e hSound

private theorem bool_false_of_not_true (b : Bool) (h : b ≠ true) :
    b = false := by
  cases b <;> simp_all

private theorem pairRelabels_false_labels
    (l r ql qr : R2.Cell ψ κ τ)
    (h : R2Coherence.pairRelabels l r ql qr = false) :
    l.base.core.core.label = ql.base.core.core.label ∧
      r.base.core.core.label = qr.base.core.core.label := by
  simpa [R2Coherence.pairRelabels, R2Coherence.labelChanged] using h

private theorem pairHazardV3_false_pairRelabels
    (l r ql qr : R2.Cell ψ κ τ)
    (h : pairHazardV3 l r ql qr = false) :
    R2Coherence.pairRelabels l r ql qr = false := by
  cases hRel : R2Coherence.pairRelabels l r ql qr with
  | false => rfl
  | true =>
      simp [pairHazardV3, R2Coherence.pairHazard, hRel] at h

private theorem seekStageV3_labels
    (l r : Cell ψ κ τ) :
    (raw (seekStageV3 l r).1).label = (raw l).label ∧
      (raw (seekStageV3 l r).2).label = (raw r).label := by
  unfold seekStageV3
  repeat' split <;> simp [setControl, raw]

private theorem sweepStageV3_labels
    (l r : Cell ψ κ τ) :
    (raw (sweepStageV3 l r).1).label = (raw l).label ∧
      (raw (sweepStageV3 l r).2).label = (raw r).label := by
  unfold sweepStageV3
  split <;>
    simp [clearMain, startClosing, setControl, raw]

private theorem commitStageV3_labels
    (l r : Cell ψ κ τ) :
    (raw (commitStageV3 l r).1).label = (raw l).label ∧
      (raw (commitStageV3 l r).2).label = (raw r).label := by
  unfold commitStageV3
  dsimp only
  repeat' split <;>
    simp [clearMain, setControl, raw]

private theorem releaseStageV3_labels
    (l r : Cell ψ κ τ) :
    (raw (releaseStageV3 l r).1).label = (raw l).label ∧
      (raw (releaseStageV3 l r).2).label = (raw r).label := by
  unfold releaseStageV3
  repeat' split <;>
    simp [startClosing, setControl, raw]

private theorem scrubLStageV3_labels
    (l r : Cell ψ κ τ) :
    (raw (scrubLStageV3 l r).1).label = (raw l).label ∧
      (raw (scrubLStageV3 l r).2).label = (raw r).label := by
  unfold scrubLStageV3
  repeat' split <;>
    simp [clearMain, startClosing, setControl, raw]

private theorem openRStageV3_labels
    (l r : Cell ψ κ τ) :
    (raw (openRStageV3 l r).1).label = (raw l).label ∧
      (raw (openRStageV3 l r).2).label = (raw r).label := by
  unfold openRStageV3
  repeat' split <;>
    simp [clearMain, startClosing, setControl, raw]

private theorem normalizePassiveV3_labels
    (l r : Cell ψ κ τ) :
    (raw (normalizePassiveV3 l r).1).label = (raw l).label ∧
      (raw (normalizePassiveV3 l r).2).label = (raw r).label := by
  unfold normalizePassiveV3
  split <;>
    simp [clearMain, startClosing, setControl, raw]

private theorem openStageV3_labels
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ) :
    (raw (openStageV3 hψ (by decide : 0 < 2) h2 l r).1).label =
        (raw l).label ∧
      (raw (openStageV3 hψ (by decide : 0 < 2) h2 l r).2).label =
        (raw r).label := by
  unfold openStageV3
  dsimp only
  by_cases hHaz :
      pairHazardV3 l.phys r.phys
        (proposalV3 hψ (by decide : 0 < 2) h2 l r).1
        (proposalV3 hψ (by decide : 0 < 2) h2 l r).2 = true
  · rw [if_pos hHaz]
    split <;> simp [startClosing, setControl, raw]
  · rw [if_neg hHaz]
    have hHazF :
        pairHazardV3 l.phys r.phys
          (proposalV3 hψ (by decide : 0 < 2) h2 l r).1
          (proposalV3 hψ (by decide : 0 < 2) h2 l r).2 = false :=
      bool_false_of_not_true _ hHaz
    have hRelF := pairHazardV3_false_pairRelabels
      l.phys r.phys
      (proposalV3 hψ (by decide : 0 < 2) h2 l r).1
      (proposalV3 hψ (by decide : 0 < 2) h2 l r).2 hHazF
    have hLab := pairRelabels_false_labels
      l.phys r.phys
      (proposalV3 hψ (by decide : 0 < 2) h2 l r).1
      (proposalV3 hψ (by decide : 0 < 2) h2 l r).2 hRelF
    constructor
    · simpa [install, raw] using hLab.1.symm
    · simpa [install, raw] using hLab.2.symm

private theorem sealedStageV3_labels
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ) :
    (raw (sealedStageV3 hψ (by decide : 0 < 2) h2 l r).1).label =
        (raw l).label ∧
      (raw (sealedStageV3 hψ (by decide : 0 < 2) h2 l r).2).label =
        (raw r).label := by
  unfold sealedStageV3
  split
  · simp [setControl, raw]
  · dsimp only
    by_cases hRel :
        R2Coherence.pairRelabels l.phys r.phys
          (sealedProposalV3 hψ (by decide : 0 < 2) h2 l r).1
          (sealedProposalV3 hψ (by decide : 0 < 2) h2 l r).2 = true
    · rw [if_pos hRel]
      exact ⟨rfl, rfl⟩
    · rw [if_neg hRel]
      have hRelF :
          R2Coherence.pairRelabels l.phys r.phys
            (sealedProposalV3 hψ (by decide : 0 < 2) h2 l r).1
            (sealedProposalV3 hψ (by decide : 0 < 2) h2 l r).2 = false :=
        bool_false_of_not_true _ hRel
      have hLab := pairRelabels_false_labels
        l.phys r.phys
        (sealedProposalV3 hψ (by decide : 0 < 2) h2 l r).1
        (sealedProposalV3 hψ (by decide : 0 < 2) h2 l r).2 hRelF
      constructor
      · simpa [install, raw] using hLab.1.symm
      · simpa [install, raw] using hLab.2.symm

private theorem ordinaryStageV3_labels
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ) :
    (raw (ordinaryStageV3 hψ (by decide : 0 < 2) h2 l r).1).label =
        (raw l).label ∧
      (raw (ordinaryStageV3 hψ (by decide : 0 < 2) h2 l r).2).label =
        (raw r).label := by
  unfold ordinaryStageV3
  split
  · split
    · exact sealedStageV3_labels hψ h2 l r
    · split
      · exact openStageV3_labels hψ h2 l r
      · exact normalizePassiveV3_labels l r
  · exact ⟨rfl, rfl⟩

private theorem rowV3_labels
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ) :
    (raw (rowV3 hψ (by decide : 0 < 2) h2 l r).1).label =
        (raw l).label ∧
      (raw (rowV3 hψ (by decide : 0 < 2) h2 l r).2).label =
        (raw r).label := by
  unfold rowV3
  split
  · exact seekStageV3_labels l r
  · split
    · exact sweepStageV3_labels l r
    · split
      · exact commitStageV3_labels l r
      · split
        · exact releaseStageV3_labels l r
        · split
          · exact scrubLStageV3_labels l r
          · split
            · exact openRStageV3_labels l r
            · exact ordinaryStageV3_labels hψ h2 l r

/-- Every V3.1 service preserves every physical label.  Label-changing open
proposals are held by `pairHazardV3`; label-changing sealed proposals are held
by `pairRelabels`; all maintenance stages are label-preserving directly. -/
theorem stepV3_labels_eq_or_held
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) :
    ∀ i : Fin n,
      (raw (stepV3 hψ h2 ring C e i)).label = (raw (C i)).label := by
  intro i
  have hPair := rowV3_labels hψ h2
    (C e) (C (ring.rightNeighbor e))
  by_cases hie : i = e
  · subst i
    simpa [stepV3, protocolV3, PopulationProtocol.step] using hPair.1
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      simpa [stepV3, protocolV3, PopulationProtocol.step, hie] using hPair.2
    · simp [stepV3, protocolV3, PopulationProtocol.step, hie, hij]

/-- The separated election geometry is closed under every V3.1 service. -/
theorem electionGeometryStepV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    ElectionGeometryStepV31 (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hGeom
  exact electionGeometryV31_of_same_labels ring hGeom
    (stepV3_labels_eq_or_held hψ h2 ring C e)

end R2CoherenceV31Closure2

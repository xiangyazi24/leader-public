import Leader.Wu.Coherence.Controller
import Leader.Wu.Coherence.SixTokenBranches


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31Branches


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair


variable {n ψ κ τ : Nat}


@[simp] private theorem raw_eraseCellV3
    (u : R2CoherenceV31.Cell ψ κ τ) :
    R2Coherence.raw (R2CoherenceV31.eraseCellV3 u) =
      R2CoherenceV31.raw u := by
  rfl


private def CellSameGeometryV3
    (u v : R2CoherenceV31.Cell ψ κ τ) : Prop :=
  (R2CoherenceV31.raw v).leader = (R2CoherenceV31.raw u).leader ∧
    (R2CoherenceV31.raw v).label = (R2CoherenceV31.raw u).label


private def SameGeometryV3
    (C D : R2CoherenceV31.FC n ψ κ τ) : Prop :=
  ∀ i : Fin n,
    (R2CoherenceV31.raw (D i)).leader =
        (R2CoherenceV31.raw (C i)).leader ∧
      (R2CoherenceV31.raw (D i)).label =
        (R2CoherenceV31.raw (C i)).label


@[simp] private theorem raw_eraseCfgV3_apply
    (C : R2CoherenceV31.FC n ψ κ τ) (i : Fin n) :
    R2Coherence.raw (R2CoherenceV31.eraseCfgV3 C i) =
      R2CoherenceV31.raw (C i) := by
  rfl

private theorem admitted_of_sameGeometryV3
    (hψ : 0 < ψ) (ring : DirectedRing n)
    {C D : R2CoherenceV31.FC n ψ κ τ}
    (hSame : SameGeometryV3 C D)
    (hC : R2CoherenceV31.AdmittedPostBirthGeometryV3 hψ ring C) :
    R2CoherenceV31.AdmittedPostBirthGeometryV3 hψ ring D := by
  change R2Coherence.AdmittedPostBirthGeometry hψ ring
    (R2CoherenceV31.eraseCfgV3 C) at hC
  change R2Coherence.AdmittedPostBirthGeometry hψ ring
    (R2CoherenceV31.eraseCfgV3 D)
  unfold R2Coherence.AdmittedPostBirthGeometry at hC ⊢
  simp only [raw_eraseCfgV3_apply] at hC ⊢
  rcases hC with ⟨hLead, hEdge⟩
  constructor
  · intro i hDi
    have hCi : (R2CoherenceV31.raw (C i)).leader = true := by
      calc
        (R2CoherenceV31.raw (C i)).leader =
            (R2CoherenceV31.raw (D i)).leader := (hSame i).1.symm
        _ = true := hDi
    calc
      (R2CoherenceV31.raw (D i)).label =
          (R2CoherenceV31.raw (C i)).label := (hSame i).2
      _ = ⟨0, hψ⟩ := hLead i hCi
  · intro i
    change
      (R2CoherenceV31.raw (D (ring.rightNeighbor i))).leader = true ∨
        (R2CoherenceV31.raw (D (ring.rightNeighbor i))).label =
          ⟨((R2CoherenceV31.raw (D i)).label.val + 1) % ψ,
            Nat.mod_lt _ hψ⟩
    have hOld := hEdge i
    change
      (R2CoherenceV31.raw (C (ring.rightNeighbor i))).leader = true ∨
        (R2CoherenceV31.raw (C (ring.rightNeighbor i))).label =
          ⟨((R2CoherenceV31.raw (C i)).label.val + 1) % ψ,
            Nat.mod_lt _ hψ⟩ at hOld
    rcases hOld with hRoot | hSucc
    · left
      calc
        (R2CoherenceV31.raw (D (ring.rightNeighbor i))).leader =
            (R2CoherenceV31.raw (C (ring.rightNeighbor i))).leader :=
          (hSame (ring.rightNeighbor i)).1
        _ = true := hRoot
    · right
      calc
        (R2CoherenceV31.raw (D (ring.rightNeighbor i))).label =
            (R2CoherenceV31.raw (C (ring.rightNeighbor i))).label :=
          (hSame (ring.rightNeighbor i)).2
        _ = ⟨((R2CoherenceV31.raw (C i)).label.val + 1) % ψ,
              Nat.mod_lt _ hψ⟩ := hSucc
        _ = ⟨((R2CoherenceV31.raw (D i)).label.val + 1) % ψ,
              Nat.mod_lt _ hψ⟩ := by
          rw [(hSame i).2]



private theorem seekStageV3_geometry
    (l r : R2CoherenceV31.Cell ψ κ τ) :
    CellSameGeometryV3 l (R2CoherenceV31.seekStageV3 l r).1 ∧
      CellSameGeometryV3 r (R2CoherenceV31.seekStageV3 l r).2 := by
  unfold R2CoherenceV31.seekStageV3
  repeat' split <;>
    simp [CellSameGeometryV3, R2CoherenceV31.setControl,
      R2CoherenceV31.raw]


private theorem sweepStageV3_geometry
    (l r : R2CoherenceV31.Cell ψ κ τ) :
    CellSameGeometryV3 l (R2CoherenceV31.sweepStageV3 l r).1 ∧
      CellSameGeometryV3 r (R2CoherenceV31.sweepStageV3 l r).2 := by
  unfold R2CoherenceV31.sweepStageV3
  split <;>
    simp [CellSameGeometryV3, R2CoherenceV31.clearMain,
      R2CoherenceV31.startClosing, R2CoherenceV31.setControl,
      R2CoherenceV31.raw]


private theorem commitStageV3_geometry
    (l r : R2CoherenceV31.Cell ψ κ τ) :
    CellSameGeometryV3 l (R2CoherenceV31.commitStageV3 l r).1 ∧
      CellSameGeometryV3 r (R2CoherenceV31.commitStageV3 l r).2 := by
  unfold R2CoherenceV31.commitStageV3
  dsimp only
  repeat' split <;>
    simp [CellSameGeometryV3, R2CoherenceV31.clearMain,
      R2CoherenceV31.setControl, R2CoherenceV31.raw]


private theorem branch_seek_token
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2CoherenceV31.Cell ψ κ τ)
    (hb : R2CoherenceV31.branchAtV3 hψ h2 l r = .seek) :
    r.ctl.tok = .seek := by
  unfold R2CoherenceV31.branchAtV3 at hb
  by_cases hSeek : r.ctl.tok = .seek
  · exact hSeek
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
              by_cases hNone :
                  l.ctl.tok = .none ∧ r.ctl.tok = .none
              · rw [if_pos hNone] at hb
                by_cases hSealed :
                    l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed
                · rw [if_pos hSealed] at hb
                  cases hb
                · rw [if_neg hSealed] at hb
                  by_cases hOpen :
                      l.ctl.mark = .open ∧ r.ctl.mark = .open
                  · rw [if_pos hOpen] at hb
                    by_cases hHaz :
                        R2CoherenceV31.pairHazardV3 l.phys r.phys
                            (R2CoherenceV31.proposalV3 hψ
                              (by decide : 0 < 2) h2 l r).1
                            (R2CoherenceV31.proposalV3 hψ
                              (by decide : 0 < 2) h2 l r).2 = true
                    · simp [hHaz] at hb
                    · simp [hHaz] at hb
                  · rw [if_neg hOpen] at hb
                    cases hb
              · rw [if_neg hNone] at hb
                cases hb




private theorem branch_sweep_conditions
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2CoherenceV31.Cell ψ κ τ)
    (hb : R2CoherenceV31.branchAtV3 hψ h2 l r = .sweep) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok = .sweep := by
  unfold R2CoherenceV31.branchAtV3 at hb
  by_cases hSeek : r.ctl.tok = .seek
  · rw [if_pos hSeek] at hb
    cases hb
  · rw [if_neg hSeek] at hb
    by_cases hSweep : l.ctl.tok = .sweep
    · exact ⟨hSeek, hSweep⟩
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
              by_cases hNone :
                  l.ctl.tok = .none ∧ r.ctl.tok = .none
              · rw [if_pos hNone] at hb
                by_cases hSealed :
                    l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed
                · rw [if_pos hSealed] at hb
                  cases hb
                · rw [if_neg hSealed] at hb
                  by_cases hOpen :
                      l.ctl.mark = .open ∧ r.ctl.mark = .open
                  · rw [if_pos hOpen] at hb
                    by_cases hHaz :
                        R2CoherenceV31.pairHazardV3 l.phys r.phys
                            (R2CoherenceV31.proposalV3 hψ
                              (by decide : 0 < 2) h2 l r).1
                            (R2CoherenceV31.proposalV3 hψ
                              (by decide : 0 < 2) h2 l r).2 = true
                    · simp [hHaz] at hb
                    · simp [hHaz] at hb
                  · rw [if_neg hOpen] at hb
                    cases hb
              · rw [if_neg hNone] at hb
                cases hb




private theorem branch_commit_conditions
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2CoherenceV31.Cell ψ κ τ)
    (hb : R2CoherenceV31.branchAtV3 hψ h2 l r = .commit) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧ r.ctl.tok = .commit := by
  unfold R2CoherenceV31.branchAtV3 at hb
  by_cases hSeek : r.ctl.tok = .seek
  · rw [if_pos hSeek] at hb
    cases hb
  · rw [if_neg hSeek] at hb
    by_cases hSweep : l.ctl.tok = .sweep
    · rw [if_pos hSweep] at hb
      cases hb
    · rw [if_neg hSweep] at hb
      by_cases hCommit : r.ctl.tok = .commit
      · exact ⟨hSeek, hSweep, hCommit⟩
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
              by_cases hNone :
                  l.ctl.tok = .none ∧ r.ctl.tok = .none
              · rw [if_pos hNone] at hb
                by_cases hSealed :
                    l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed
                · rw [if_pos hSealed] at hb
                  cases hb
                · rw [if_neg hSealed] at hb
                  by_cases hOpen :
                      l.ctl.mark = .open ∧ r.ctl.mark = .open
                  · rw [if_pos hOpen] at hb
                    by_cases hHaz :
                        R2CoherenceV31.pairHazardV3 l.phys r.phys
                            (R2CoherenceV31.proposalV3 hψ
                              (by decide : 0 < 2) h2 l r).1
                            (R2CoherenceV31.proposalV3 hψ
                              (by decide : 0 < 2) h2 l r).2 = true
                    · simp [hHaz] at hb
                    · simp [hHaz] at hb
                  · rw [if_neg hOpen] at hb
                    cases hb
              · rw [if_neg hNone] at hb
                cases hb




private theorem rowV3_geometry_seek
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2CoherenceV31.Cell ψ κ τ)
    (hb : R2CoherenceV31.branchAtV3 hψ h2 l r = .seek) :
    CellSameGeometryV3 l
        (R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2 l r).1 ∧
      CellSameGeometryV3 r
        (R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2 l r).2 := by
  have hs := branch_seek_token hψ h2 l r hb
  unfold R2CoherenceV31.rowV3
  rw [if_pos hs]
  exact seekStageV3_geometry l r


private theorem rowV3_geometry_sweep
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2CoherenceV31.Cell ψ κ τ)
    (hb : R2CoherenceV31.branchAtV3 hψ h2 l r = .sweep) :
    CellSameGeometryV3 l
        (R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2 l r).1 ∧
      CellSameGeometryV3 r
        (R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2 l r).2 := by
  rcases branch_sweep_conditions hψ h2 l r hb with ⟨hSeek, hSweep⟩
  unfold R2CoherenceV31.rowV3
  rw [if_neg hSeek, if_pos hSweep]
  exact sweepStageV3_geometry l r


private theorem rowV3_geometry_commit
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2CoherenceV31.Cell ψ κ τ)
    (hb : R2CoherenceV31.branchAtV3 hψ h2 l r = .commit) :
    CellSameGeometryV3 l
        (R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2 l r).1 ∧
      CellSameGeometryV3 r
        (R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2 l r).2 := by
  rcases branch_commit_conditions hψ h2 l r hb with
    ⟨hSeek, hSweep, hCommit⟩
  unfold R2CoherenceV31.rowV3
  rw [if_neg hSeek, if_neg hSweep, if_pos hCommit]
  exact commitStageV3_geometry l r


private theorem sameGeometry_stepV3_of_pair
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : R2CoherenceV31.FC n ψ κ τ) (e : Fin n)
    (hPair :
      CellSameGeometryV3 (C e)
        (R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2
          (C e) (C (ring.rightNeighbor e))).1 ∧
      CellSameGeometryV3 (C (ring.rightNeighbor e))
        (R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2
          (C e) (C (ring.rightNeighbor e))).2) :
    SameGeometryV3 C (R2CoherenceV31.stepV3 hψ h2 ring C e) := by
  unfold SameGeometryV3
  intro i
  by_cases hie : i = e
  · subst i
    simpa [CellSameGeometryV3, R2CoherenceV31.stepV3,
      R2CoherenceV31.protocolV3, PopulationProtocol.step] using hPair.1
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      simpa [CellSameGeometryV3, R2CoherenceV31.stepV3,
        R2CoherenceV31.protocolV3, PopulationProtocol.step, hie] using hPair.2
    · simp [R2CoherenceV31.stepV3, R2CoherenceV31.protocolV3,
        PopulationProtocol.step, hie, hij]


private def erasePairV3
    (q : R2CoherenceV31.Cell ψ κ τ × R2CoherenceV31.Cell ψ κ τ) :
    R2Coherence.Cell ψ κ τ × R2Coherence.Cell ψ κ τ :=
  (R2CoherenceV31.eraseCellV3 q.1, R2CoherenceV31.eraseCellV3 q.2)


@[simp] private theorem erase_setControlV3
    (u : R2CoherenceV31.Cell ψ κ τ) (m : R2Coherence.Mark)
    (t : R2CoherenceV31.TokenV3) :
    R2CoherenceV31.eraseCellV3 (R2CoherenceV31.setControl u m t) =
      R2Coherence.setControl (R2CoherenceV31.eraseCellV3 u) m
        (R2CoherenceV31.eraseTokenV3 t) := by
  cases u
  rfl


@[simp] private theorem erase_clearMainV3
    (u : R2CoherenceV31.Cell ψ κ τ) :
    R2CoherenceV31.eraseCellV3 (R2CoherenceV31.clearMain u) =
      R2Coherence.clearMain (R2CoherenceV31.eraseCellV3 u) := by
  cases u
  rfl


@[simp] private theorem atRoot_eraseCellV3
    (u : R2CoherenceV31.Cell ψ κ τ) :
    R2Coherence.atRootB (R2CoherenceV31.eraseCellV3 u) =
      R2CoherenceV31.atRootB u := by
  rfl


@[simp] private theorem atTerminal_eraseCellV3
    (u : R2CoherenceV31.Cell ψ κ τ) :
    R2Coherence.atTerminalB (R2CoherenceV31.eraseCellV3 u) =
      R2CoherenceV31.atTerminalB u := by
  rfl


@[simp] private theorem successor_eraseCellV3
    (l r : R2CoherenceV31.Cell ψ κ τ) :
    R2Coherence.successorB
        (R2CoherenceV31.eraseCellV3 l) (R2CoherenceV31.eraseCellV3 r) =
      R2CoherenceV31.successorB l r := by
  rfl


@[simp] private theorem eraseTokenV3_eq_seek_iff
    (t : R2CoherenceV31.TokenV3) :
    R2CoherenceV31.eraseTokenV3 t = R2Coherence.Token.seek ↔ t = .seek := by
  cases t <;> simp [R2CoherenceV31.eraseTokenV3]


@[simp] private theorem eraseTokenV3_eq_sweep_iff
    (t : R2CoherenceV31.TokenV3) :
    R2CoherenceV31.eraseTokenV3 t = R2Coherence.Token.sweep ↔ t = .sweep := by
  cases t <;> simp [R2CoherenceV31.eraseTokenV3]


@[simp] private theorem eraseTokenV3_eq_commit_iff
    (t : R2CoherenceV31.TokenV3) :
    R2CoherenceV31.eraseTokenV3 t = R2Coherence.Token.commit ↔ t = .commit := by
  cases t <;> simp [R2CoherenceV31.eraseTokenV3]


@[simp] private theorem eraseTokenV3_none_local :
    R2CoherenceV31.eraseTokenV3 R2CoherenceV31.TokenV3.none =
      R2Coherence.Token.none := by
  rfl


@[simp] private theorem eraseTokenV3_seek_local :
    R2CoherenceV31.eraseTokenV3 R2CoherenceV31.TokenV3.seek =
      R2Coherence.Token.seek := by
  rfl


@[simp] private theorem eraseTokenV3_sweep_local :
    R2CoherenceV31.eraseTokenV3 R2CoherenceV31.TokenV3.sweep =
      R2Coherence.Token.sweep := by
  rfl


@[simp] private theorem eraseTokenV3_commit_local :
    R2CoherenceV31.eraseTokenV3 R2CoherenceV31.TokenV3.commit =
      R2Coherence.Token.commit := by
  rfl

private theorem erase_seekStageV3
    (l r : R2CoherenceV31.Cell ψ κ τ) :
    erasePairV3 (R2CoherenceV31.seekStageV3 l r) =
      R2Coherence.seekStage
        (R2CoherenceV31.eraseCellV3 l) (R2CoherenceV31.eraseCellV3 r) := by
  by_cases hr : R2CoherenceV31.atRootB r = true
  · simp [erasePairV3, R2CoherenceV31.seekStageV3,
      R2Coherence.seekStage, hr]
  · by_cases hl : R2CoherenceV31.atRootB l = true
    · simp [erasePairV3, R2CoherenceV31.seekStageV3,
        R2Coherence.seekStage, hr, hl]
    · simp [erasePairV3, R2CoherenceV31.seekStageV3,
        R2Coherence.seekStage, hr, hl]



private theorem erase_sweepStageV3_of_successor
    (l r : R2CoherenceV31.Cell ψ κ τ)
    (hs : R2CoherenceV31.successorB l r = true) :
    erasePairV3 (R2CoherenceV31.sweepStageV3 l r) =
      R2Coherence.sweepStage
        (R2CoherenceV31.eraseCellV3 l) (R2CoherenceV31.eraseCellV3 r) := by
  by_cases ht : R2CoherenceV31.atTerminalB r = true
  · simp [erasePairV3, R2CoherenceV31.sweepStageV3,
      R2Coherence.sweepStage, hs, ht]
  · simp [erasePairV3, R2CoherenceV31.sweepStageV3,
      R2Coherence.sweepStage, hs, ht]



private theorem erase_commitStageV3
    (l r : R2CoherenceV31.Cell ψ κ τ) :
    erasePairV3 (R2CoherenceV31.commitStageV3 l r) =
      R2Coherence.commitStage
        (R2CoherenceV31.eraseCellV3 l) (R2CoherenceV31.eraseCellV3 r) := by
  by_cases hr : R2CoherenceV31.atRootB r = true
  · simp [erasePairV3, R2CoherenceV31.commitStageV3,
      R2Coherence.commitStage, hr]
  · by_cases hl : R2CoherenceV31.atRootB l = true
    · simp [erasePairV3, R2CoherenceV31.commitStageV3,
        R2Coherence.commitStage, hr, hl]
    · simp [erasePairV3, R2CoherenceV31.commitStageV3,
        R2Coherence.commitStage, hr, hl]



private theorem erase_rowV3_seek
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2CoherenceV31.Cell ψ κ τ)
    (hb : R2CoherenceV31.branchAtV3 hψ h2 l r = .seek) :
    erasePairV3
        (R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2 l r) =
      R2Coherence.row hψ (by decide : 0 < 2) h2
        (R2CoherenceV31.eraseCellV3 l) (R2CoherenceV31.eraseCellV3 r) := by
  have hs := branch_seek_token hψ h2 l r hb
  have hsE :
      (R2CoherenceV31.eraseCellV3 r).ctl.tok = R2Coherence.Token.seek := by
    simpa [R2CoherenceV31.eraseCellV3] using
      ((eraseTokenV3_eq_seek_iff r.ctl.tok).2 hs)
  unfold R2CoherenceV31.rowV3 R2Coherence.row
  rw [if_pos hs, if_pos hsE]
  exact erase_seekStageV3 l r



private theorem erase_rowV3_sweep_of_successor
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2CoherenceV31.Cell ψ κ τ)
    (hb : R2CoherenceV31.branchAtV3 hψ h2 l r = .sweep)
    (hs : R2CoherenceV31.successorB l r = true) :
    erasePairV3
        (R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2 l r) =
      R2Coherence.row hψ (by decide : 0 < 2) h2
        (R2CoherenceV31.eraseCellV3 l) (R2CoherenceV31.eraseCellV3 r) := by
  rcases branch_sweep_conditions hψ h2 l r hb with ⟨hSeek, hSweep⟩
  have hSeekE :
      (R2CoherenceV31.eraseCellV3 r).ctl.tok ≠ R2Coherence.Token.seek := by
    intro h
    apply hSeek
    apply (eraseTokenV3_eq_seek_iff r.ctl.tok).1
    simpa [R2CoherenceV31.eraseCellV3] using h
  have hSweepE :
      (R2CoherenceV31.eraseCellV3 l).ctl.tok = R2Coherence.Token.sweep := by
    simpa [R2CoherenceV31.eraseCellV3] using
      ((eraseTokenV3_eq_sweep_iff l.ctl.tok).2 hSweep)
  unfold R2CoherenceV31.rowV3 R2Coherence.row
  rw [if_neg hSeek, if_pos hSweep, if_neg hSeekE, if_pos hSweepE]
  exact erase_sweepStageV3_of_successor l r hs



private theorem erase_rowV3_commit
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2CoherenceV31.Cell ψ κ τ)
    (hb : R2CoherenceV31.branchAtV3 hψ h2 l r = .commit) :
    erasePairV3
        (R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2 l r) =
      R2Coherence.row hψ (by decide : 0 < 2) h2
        (R2CoherenceV31.eraseCellV3 l) (R2CoherenceV31.eraseCellV3 r) := by
  rcases branch_commit_conditions hψ h2 l r hb with
    ⟨hSeek, hSweep, hCommit⟩
  have hSeekE :
      (R2CoherenceV31.eraseCellV3 r).ctl.tok ≠ R2Coherence.Token.seek := by
    intro h
    apply hSeek
    apply (eraseTokenV3_eq_seek_iff r.ctl.tok).1
    simpa [R2CoherenceV31.eraseCellV3] using h
  have hSweepE :
      (R2CoherenceV31.eraseCellV3 l).ctl.tok ≠ R2Coherence.Token.sweep := by
    intro h
    apply hSweep
    apply (eraseTokenV3_eq_sweep_iff l.ctl.tok).1
    simpa [R2CoherenceV31.eraseCellV3] using h
  have hCommitE :
      (R2CoherenceV31.eraseCellV3 r).ctl.tok = R2Coherence.Token.commit := by
    simpa [R2CoherenceV31.eraseCellV3] using
      ((eraseTokenV3_eq_commit_iff r.ctl.tok).2 hCommit)
  unfold R2CoherenceV31.rowV3 R2Coherence.row
  rw [if_neg hSeek, if_neg hSweep, if_pos hCommit,
    if_neg hSeekE, if_neg hSweepE, if_pos hCommitE]
  exact erase_commitStageV3 l r



private theorem erase_stepV3_of_row
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : R2CoherenceV31.FC n ψ κ τ) (e : Fin n)
    (hRow :
      erasePairV3
          (R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2
            (C e) (C (ring.rightNeighbor e))) =
        R2Coherence.row hψ (by decide : 0 < 2) h2
          (R2CoherenceV31.eraseCellV3 (C e))
          (R2CoherenceV31.eraseCellV3 (C (ring.rightNeighbor e)))) :
    R2CoherenceV31.eraseCfgV3 (R2CoherenceV31.stepV3 hψ h2 ring C e) =
      R2Coherence.step hψ h2 ring (R2CoherenceV31.eraseCfgV3 C) e := by
  have hL :
      R2CoherenceV31.eraseCellV3
          (R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2
            (C e) (C (ring.rightNeighbor e))).1 =
        (R2Coherence.row hψ (by decide : 0 < 2) h2
          (R2CoherenceV31.eraseCellV3 (C e))
          (R2CoherenceV31.eraseCellV3 (C (ring.rightNeighbor e)))).1 := by
    simpa [erasePairV3] using congrArg Prod.fst hRow
  have hR :
      R2CoherenceV31.eraseCellV3
          (R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2
            (C e) (C (ring.rightNeighbor e))).2 =
        (R2Coherence.row hψ (by decide : 0 < 2) h2
          (R2CoherenceV31.eraseCellV3 (C e))
          (R2CoherenceV31.eraseCellV3 (C (ring.rightNeighbor e)))).2 := by
    simpa [erasePairV3] using congrArg Prod.snd hRow
  funext i
  by_cases hie : i = e
  · subst i
    simpa [R2CoherenceV31.eraseCfgV3, R2CoherenceV31.stepV3,
      R2CoherenceV31.protocolV3, R2Coherence.step, R2Coherence.protocol,
      PopulationProtocol.step] using hL
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      simpa [R2CoherenceV31.eraseCfgV3, R2CoherenceV31.stepV3,
        R2CoherenceV31.protocolV3, R2Coherence.step, R2Coherence.protocol,
        PopulationProtocol.step, hie] using hR
    · simp [R2CoherenceV31.eraseCfgV3, R2CoherenceV31.stepV3,
        R2CoherenceV31.protocolV3, R2Coherence.step, R2Coherence.protocol,
        PopulationProtocol.step, hie, hij]


private theorem erase_branchAtV3_seek
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : R2CoherenceV31.FC n ψ κ τ) (e : Fin n)
    (hb : R2CoherenceV31.branchAtV3 hψ h2
      (C e) (C (ring.rightNeighbor e)) = .seek) :
    R2Coherence.branchAt hψ h2 ring (R2CoherenceV31.eraseCfgV3 C) e = .seek := by
  have hs := branch_seek_token hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  simp [R2Coherence.branchAt, R2CoherenceV31.eraseCfgV3,
    R2CoherenceV31.eraseCellV3, hs]


private theorem erase_branchAtV3_sweep
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : R2CoherenceV31.FC n ψ κ τ) (e : Fin n)
    (hb : R2CoherenceV31.branchAtV3 hψ h2
      (C e) (C (ring.rightNeighbor e)) = .sweep) :
    R2Coherence.branchAt hψ h2 ring (R2CoherenceV31.eraseCfgV3 C) e = .sweep := by
  rcases branch_sweep_conditions hψ h2
    (C e) (C (ring.rightNeighbor e)) hb with ⟨hSeek, hSweep⟩
  simp [R2Coherence.branchAt, R2CoherenceV31.eraseCfgV3,
    R2CoherenceV31.eraseCellV3, hSeek, hSweep]


private theorem erase_branchAtV3_commit
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : R2CoherenceV31.FC n ψ κ τ) (e : Fin n)
    (hb : R2CoherenceV31.branchAtV3 hψ h2
      (C e) (C (ring.rightNeighbor e)) = .commit) :
    R2Coherence.branchAt hψ h2 ring (R2CoherenceV31.eraseCfgV3 C) e = .commit := by
  rcases branch_commit_conditions hψ h2
    (C e) (C (ring.rightNeighbor e)) hb with
    ⟨hSeek, hSweep, hCommit⟩
  simp [R2Coherence.branchAt, R2CoherenceV31.eraseCfgV3,
    R2CoherenceV31.eraseCellV3, hSeek, hSweep, hCommit]


private theorem quarantineMutation_erase_stepV3_of_pair
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : R2CoherenceV31.FC n ψ κ τ) (e : Fin n)
    (hPair : R2CoherenceBranches.PairQuarantineMutation
      (R2CoherenceV31.eraseCellV3 (C e))
      (R2CoherenceV31.eraseCellV3 (C (ring.rightNeighbor e)))
      (erasePairV3
        (R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2
          (C e) (C (ring.rightNeighbor e))))) :
    R2CoherenceBranches.QuarantineMutation
      (R2CoherenceV31.eraseCfgV3 C)
      (R2CoherenceV31.eraseCfgV3 (R2CoherenceV31.stepV3 hψ h2 ring C e)) := by
  rcases hPair with ⟨hLM, hRM, hLN, hRN⟩
  intro p
  by_cases hpe : p = e
  · subst p
    simpa [R2CoherenceV31.eraseCfgV3, erasePairV3,
      R2CoherenceV31.stepV3, R2CoherenceV31.protocolV3,
      PopulationProtocol.step] using And.intro hLM hLN
  · by_cases hpj : p = ring.rightNeighbor e
    · subst p
      simpa [R2CoherenceV31.eraseCfgV3, erasePairV3,
        R2CoherenceV31.stepV3, R2CoherenceV31.protocolV3,
        PopulationProtocol.step, hpe] using And.intro hRM hRN
    · have hSame :
        (((R2CoherenceV31.eraseCfgV3 C) p).phys ≠
              ((R2CoherenceV31.eraseCfgV3 C) p).phys →
            R2CoherenceBranches.NonOpen ((R2CoherenceV31.eraseCfgV3 C) p)) ∧
          (R2CoherenceBranches.NonOpen ((R2CoherenceV31.eraseCfgV3 C) p) →
            R2CoherenceBranches.NonOpen ((R2CoherenceV31.eraseCfgV3 C) p)) :=
        ⟨fun h => (h rfl).elim, fun h => h⟩
      simpa [R2CoherenceV31.eraseCfgV3, R2CoherenceV31.stepV3,
        R2CoherenceV31.protocolV3, PopulationProtocol.step, hpe, hpj] using hSame


private theorem pairMutation_sweep_bad
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2CoherenceV31.Cell ψ κ τ)
    (hb : R2CoherenceV31.branchAtV3 hψ h2 l r = .sweep)
    (hs : R2CoherenceV31.successorB l r = false) :
    R2CoherenceBranches.PairQuarantineMutation
      (R2CoherenceV31.eraseCellV3 l) (R2CoherenceV31.eraseCellV3 r)
      (erasePairV3
        (R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2 l r)) := by
  rcases branch_sweep_conditions hψ h2 l r hb with ⟨hSeek, hSweep⟩
  simp [R2CoherenceBranches.PairQuarantineMutation,
    R2CoherenceBranches.NonOpen, R2CoherenceV31.rowV3,
    R2CoherenceV31.sweepStageV3, R2CoherenceV31.startClosing,
    R2CoherenceV31.setControl, R2CoherenceV31.eraseCellV3,
    R2CoherenceV31.eraseTokenV3, erasePairV3, hSeek, hSweep, hs]


/-- SEEK: exact V3→V1 erasure, plus one-step ControllerSound closure. -/
theorem seek_preservation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    R2CoherenceV31.SeekPreservationObligationV3
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hRec hb
  rcases hRec with ⟨hGeom, hCoh, hSound⟩
  have hPairGeom := rowV3_geometry_seek hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hSame := sameGeometry_stepV3_of_pair hψ h2 ring C e hPairGeom
  refine ⟨admitted_of_sameGeometryV3 hψ ring hSame hGeom, ?_,
    R2CoherenceV31.controllerSoundV3_step hψ h2 ring C e hSound⟩
  have hRow := erase_rowV3_seek hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hStep := erase_stepV3_of_row hψ h2 ring C e hRow
  have hOld : R2Coherence.CoherentPrefixes ring
      (R2Coherence.step hψ h2 ring (R2CoherenceV31.eraseCfgV3 C) e) :=
    R2CoherenceBranches.seek_preservation
      (κ := κ) (τ := τ) hψ h2 ring
      (R2CoherenceV31.eraseCfgV3 C) e hGeom hCoh
      (erase_branchAtV3_seek hψ h2 ring C e hb)
  change R2Coherence.CoherentPrefixes ring
    (R2CoherenceV31.eraseCfgV3 (R2CoherenceV31.stepV3 hψ h2 ring C e))
  rw [hStep]
  exact hOld


theorem sweep_preservation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    R2CoherenceV31.SweepPreservationObligationV3
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hRec hb
  rcases hRec with ⟨hGeom, hCoh, hSound⟩
  have hPairGeom := rowV3_geometry_sweep hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hSame := sameGeometry_stepV3_of_pair hψ h2 ring C e hPairGeom
  refine ⟨admitted_of_sameGeometryV3 hψ ring hSame hGeom, ?_,
    R2CoherenceV31.controllerSoundV3_step hψ h2 ring C e hSound⟩
  by_cases hs :
      R2CoherenceV31.successorB (C e) (C (ring.rightNeighbor e)) = true
  · have hRow := erase_rowV3_sweep_of_successor hψ h2
      (C e) (C (ring.rightNeighbor e)) hb hs
    have hStep := erase_stepV3_of_row hψ h2 ring C e hRow
    have hOld : R2Coherence.CoherentPrefixes ring
        (R2Coherence.step hψ h2 ring (R2CoherenceV31.eraseCfgV3 C) e) :=
      R2CoherenceBranches.sweep_preservation
        (κ := κ) (τ := τ) hψ h2 ring
        (R2CoherenceV31.eraseCfgV3 C) e hGeom hCoh
        (erase_branchAtV3_sweep hψ h2 ring C e hb)
    change R2Coherence.CoherentPrefixes ring
      (R2CoherenceV31.eraseCfgV3
        (R2CoherenceV31.stepV3 hψ h2 ring C e))
    rw [hStep]
    exact hOld
  · have hsFalse :
        R2CoherenceV31.successorB
          (C e) (C (ring.rightNeighbor e)) = false := by
      cases hq : R2CoherenceV31.successorB
          (C e) (C (ring.rightNeighbor e)) with
      | false => rfl
      | true => exact (hs hq).elim
    have hPair := pairMutation_sweep_bad hψ h2
      (C e) (C (ring.rightNeighbor e)) hb hsFalse
    have hMut := quarantineMutation_erase_stepV3_of_pair
      hψ h2 ring C e hPair
    change R2Coherence.CoherentPrefixes ring
      (R2CoherenceV31.eraseCfgV3
        (R2CoherenceV31.stepV3 hψ h2 ring C e))
    exact R2CoherenceBranches.coherentPrefixes_of_quarantineMutation
      ring hMut hCoh




/-- COMMIT: exact V3→V1 erasure, plus one-step ControllerSound closure. -/
theorem commit_preservation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    R2CoherenceV31.CommitPreservationObligationV3
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hRec hb
  rcases hRec with ⟨hGeom, hCoh, hSound⟩
  have hPairGeom := rowV3_geometry_commit hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hSame := sameGeometry_stepV3_of_pair hψ h2 ring C e hPairGeom
  refine ⟨admitted_of_sameGeometryV3 hψ ring hSame hGeom, ?_,
    R2CoherenceV31.controllerSoundV3_step hψ h2 ring C e hSound⟩
  have hRow := erase_rowV3_commit hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hStep := erase_stepV3_of_row hψ h2 ring C e hRow
  have hOld : R2Coherence.CoherentPrefixes ring
      (R2Coherence.step hψ h2 ring (R2CoherenceV31.eraseCfgV3 C) e) :=
    R2CoherenceBranches.commit_preservation
      (κ := κ) (τ := τ) hψ h2 ring
      (R2CoherenceV31.eraseCfgV3 C) e hGeom hCoh
      (erase_branchAtV3_commit hψ h2 ring C e hb)
  change R2Coherence.CoherentPrefixes ring
    (R2CoherenceV31.eraseCfgV3 (R2CoherenceV31.stepV3 hψ h2 ring C e))
  rw [hStep]
  exact hOld


end R2CoherenceV31Branches

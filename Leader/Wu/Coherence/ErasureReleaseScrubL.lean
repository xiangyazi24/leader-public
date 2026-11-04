import Leader.Wu.Coherence.ErasureSeekSweepCommit

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31Branches3

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair

variable {n ψ κ τ : Nat}

@[simp] private theorem raw_eraseCfgV3_apply
    (C : R2CoherenceV31.FC n ψ κ τ) (i : Fin n) :
    R2Coherence.raw (R2CoherenceV31.eraseCfgV3 C i) =
      R2CoherenceV31.raw (C i) := by
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

private theorem branch_release_conditions
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2CoherenceV31.Cell ψ κ τ)
    (hb : R2CoherenceV31.branchAtV3 hψ h2 l r = .release) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok = .release := by
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
      · rw [if_pos hCommit] at hb
        cases hb
      · rw [if_neg hCommit] at hb
        by_cases hRelease : l.ctl.tok = .release
        · exact ⟨hSeek, hSweep, hCommit, hRelease⟩
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

private theorem branch_scrubL_conditions
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2CoherenceV31.Cell ψ κ τ)
    (hb : R2CoherenceV31.branchAtV3 hψ h2 l r = .scrubL) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok ≠ .release ∧
      r.ctl.tok = .scrubL := by
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
      · rw [if_pos hCommit] at hb
        cases hb
      · rw [if_neg hCommit] at hb
        by_cases hRelease : l.ctl.tok = .release
        · rw [if_pos hRelease] at hb
          cases hb
        · rw [if_neg hRelease] at hb
          by_cases hScrub : r.ctl.tok = .scrubL
          · exact ⟨hSeek, hSweep, hCommit, hRelease, hScrub⟩
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

private theorem releaseStageV3_geometry
    (l r : R2CoherenceV31.Cell ψ κ τ) :
    CellSameGeometryV3 l (R2CoherenceV31.releaseStageV3 l r).1 ∧
      CellSameGeometryV3 r (R2CoherenceV31.releaseStageV3 l r).2 := by
  unfold R2CoherenceV31.releaseStageV3
  repeat' split <;>
    simp [CellSameGeometryV3, R2CoherenceV31.startClosing,
      R2CoherenceV31.setControl, R2CoherenceV31.raw]

private theorem scrubLStageV3_geometry
    (l r : R2CoherenceV31.Cell ψ κ τ) :
    CellSameGeometryV3 l (R2CoherenceV31.scrubLStageV3 l r).1 ∧
      CellSameGeometryV3 r (R2CoherenceV31.scrubLStageV3 l r).2 := by
  unfold R2CoherenceV31.scrubLStageV3
  repeat' split <;>
    simp [CellSameGeometryV3, R2CoherenceV31.clearMain,
      R2CoherenceV31.startClosing, R2CoherenceV31.setControl,
      R2CoherenceV31.raw]

private theorem rowV3_geometry_release
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2CoherenceV31.Cell ψ κ τ)
    (hb : R2CoherenceV31.branchAtV3 hψ h2 l r = .release) :
    CellSameGeometryV3 l
        (R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2 l r).1 ∧
      CellSameGeometryV3 r
        (R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2 l r).2 := by
  rcases branch_release_conditions hψ h2 l r hb with
    ⟨hSeek, hSweep, hCommit, hRelease⟩
  unfold R2CoherenceV31.rowV3
  rw [if_neg hSeek, if_neg hSweep, if_neg hCommit, if_pos hRelease]
  exact releaseStageV3_geometry l r

private theorem rowV3_geometry_scrubL
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2CoherenceV31.Cell ψ κ τ)
    (hb : R2CoherenceV31.branchAtV3 hψ h2 l r = .scrubL) :
    CellSameGeometryV3 l
        (R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2 l r).1 ∧
      CellSameGeometryV3 r
        (R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2 l r).2 := by
  rcases branch_scrubL_conditions hψ h2 l r hb with
    ⟨hSeek, hSweep, hCommit, hRelease, hScrub⟩
  unfold R2CoherenceV31.rowV3
  rw [if_neg hSeek, if_neg hSweep, if_neg hCommit,
    if_neg hRelease, if_pos hScrub]
  exact scrubLStageV3_geometry l r

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

@[simp] private theorem writerQuiet_eraseCellV3
    (u : R2CoherenceV31.Cell ψ κ τ) :
    R2Coherence.writerQuiet (R2CoherenceV31.eraseCellV3 u) =
      R2CoherenceV31.writerQuiet u := by
  rfl

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

@[simp] private theorem eraseTokenV3_release_local :
    R2CoherenceV31.eraseTokenV3 R2CoherenceV31.TokenV3.release =
      R2Coherence.Token.release := by
  rfl

@[simp] private theorem eraseTokenV3_scrubL_local :
    R2CoherenceV31.eraseTokenV3 R2CoherenceV31.TokenV3.scrubL =
      R2Coherence.Token.reopen := by
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

@[simp] private theorem eraseTokenV3_eq_release_iff
    (t : R2CoherenceV31.TokenV3) :
    R2CoherenceV31.eraseTokenV3 t = R2Coherence.Token.release ↔ t = .release := by
  cases t <;> simp [R2CoherenceV31.eraseTokenV3]

private theorem erase_releaseStageV3_of_successor
    (l r : R2CoherenceV31.Cell ψ κ τ)
    (hs : R2CoherenceV31.successorB l r = true) :
    erasePairV3 (R2CoherenceV31.releaseStageV3 l r) =
      R2Coherence.releaseStage
        (R2CoherenceV31.eraseCellV3 l) (R2CoherenceV31.eraseCellV3 r) := by
  by_cases hq : R2CoherenceV31.writerQuiet r = true
  · by_cases ht : R2CoherenceV31.atTerminalB r = true
    · simp [erasePairV3, R2CoherenceV31.releaseStageV3,
        R2Coherence.releaseStage, hs, hq, ht]
    · simp [erasePairV3, R2CoherenceV31.releaseStageV3,
        R2Coherence.releaseStage, hs, hq, ht]
  · by_cases hr : R2CoherenceV31.atRootB l = true
    · simp [erasePairV3, R2CoherenceV31.releaseStageV3,
        R2Coherence.releaseStage, hs, hq, hr]
    · simp [erasePairV3, R2CoherenceV31.releaseStageV3,
        R2Coherence.releaseStage, hs, hq, hr]

private theorem erase_rowV3_release_of_successor
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2CoherenceV31.Cell ψ κ τ)
    (hb : R2CoherenceV31.branchAtV3 hψ h2 l r = .release)
    (hs : R2CoherenceV31.successorB l r = true) :
    erasePairV3
        (R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2 l r) =
      R2Coherence.row hψ (by decide : 0 < 2) h2
        (R2CoherenceV31.eraseCellV3 l) (R2CoherenceV31.eraseCellV3 r) := by
  rcases branch_release_conditions hψ h2 l r hb with
    ⟨hSeek, hSweep, hCommit, hRelease⟩
  have hSeekE :
      (R2CoherenceV31.eraseCellV3 r).ctl.tok ≠ R2Coherence.Token.seek := by
    intro h
    exact hSeek ((eraseTokenV3_eq_seek_iff r.ctl.tok).1 h)
  have hSweepE :
      (R2CoherenceV31.eraseCellV3 l).ctl.tok ≠ R2Coherence.Token.sweep := by
    intro h
    exact hSweep ((eraseTokenV3_eq_sweep_iff l.ctl.tok).1 h)
  have hCommitE :
      (R2CoherenceV31.eraseCellV3 r).ctl.tok ≠ R2Coherence.Token.commit := by
    intro h
    exact hCommit ((eraseTokenV3_eq_commit_iff r.ctl.tok).1 h)
  have hReleaseE :
      (R2CoherenceV31.eraseCellV3 l).ctl.tok = R2Coherence.Token.release := by
    exact (eraseTokenV3_eq_release_iff l.ctl.tok).2 hRelease
  unfold R2CoherenceV31.rowV3 R2Coherence.row
  rw [if_neg hSeek, if_neg hSweep, if_neg hCommit, if_pos hRelease,
    if_neg hSeekE, if_neg hSweepE, if_neg hCommitE, if_pos hReleaseE]
  exact erase_releaseStageV3_of_successor l r hs

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
  have hL := congrArg Prod.fst hRow
  have hR := congrArg Prod.snd hRow
  funext i
  by_cases hie : i = e
  · subst i
    simpa [erasePairV3, R2CoherenceV31.eraseCfgV3,
      R2CoherenceV31.stepV3, R2CoherenceV31.protocolV3,
      R2Coherence.step, R2Coherence.protocol, PopulationProtocol.step] using hL
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      simpa [erasePairV3, R2CoherenceV31.eraseCfgV3,
        R2CoherenceV31.stepV3, R2CoherenceV31.protocolV3,
        R2Coherence.step, R2Coherence.protocol, PopulationProtocol.step, hie] using hR
    · simp [R2CoherenceV31.eraseCfgV3, R2CoherenceV31.stepV3,
        R2CoherenceV31.protocolV3, R2Coherence.step, R2Coherence.protocol,
        PopulationProtocol.step, hie, hij]

private theorem erase_branchAtV3_release
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : R2CoherenceV31.FC n ψ κ τ) (e : Fin n)
    (hb : R2CoherenceV31.branchAtV3 hψ h2
      (C e) (C (ring.rightNeighbor e)) = .release) :
    R2Coherence.branchAt hψ h2 ring (R2CoherenceV31.eraseCfgV3 C) e =
      .release := by
  rcases branch_release_conditions hψ h2
    (C e) (C (ring.rightNeighbor e)) hb with
    ⟨hSeek, hSweep, hCommit, hRelease⟩
  have hSeekE :
      (R2CoherenceV31.eraseCellV3 (C (ring.rightNeighbor e))).ctl.tok ≠
        R2Coherence.Token.seek := by
    intro h
    exact hSeek ((eraseTokenV3_eq_seek_iff _).1 h)
  have hSweepE :
      (R2CoherenceV31.eraseCellV3 (C e)).ctl.tok ≠ R2Coherence.Token.sweep := by
    intro h
    exact hSweep ((eraseTokenV3_eq_sweep_iff _).1 h)
  have hCommitE :
      (R2CoherenceV31.eraseCellV3 (C (ring.rightNeighbor e))).ctl.tok ≠
        R2Coherence.Token.commit := by
    intro h
    exact hCommit ((eraseTokenV3_eq_commit_iff _).1 h)
  have hReleaseE :
      (R2CoherenceV31.eraseCellV3 (C e)).ctl.tok = R2Coherence.Token.release :=
    (eraseTokenV3_eq_release_iff _).2 hRelease
  unfold R2Coherence.branchAt
  dsimp only [R2CoherenceV31.eraseCfgV3]
  rw [if_neg hSeekE, if_neg hSweepE, if_neg hCommitE, if_pos hReleaseE]

private theorem pairMutation_release_bad
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2CoherenceV31.Cell ψ κ τ)
    (hb : R2CoherenceV31.branchAtV3 hψ h2 l r = .release)
    (hs : R2CoherenceV31.successorB l r = false) :
    R2CoherenceBranches.PairQuarantineMutation
      (R2CoherenceV31.eraseCellV3 l) (R2CoherenceV31.eraseCellV3 r)
      (erasePairV3
        (R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2 l r)) := by
  rcases branch_release_conditions hψ h2 l r hb with
    ⟨hSeek, hSweep, hCommit, hRelease⟩
  simp [R2CoherenceBranches.PairQuarantineMutation,
    R2CoherenceBranches.NonOpen, R2CoherenceV31.rowV3,
    R2CoherenceV31.releaseStageV3, R2CoherenceV31.startClosing,
    R2CoherenceV31.setControl, R2CoherenceV31.eraseCellV3,
    R2CoherenceV31.eraseTokenV3, erasePairV3,
    hSeek, hSweep, hCommit, hRelease, hs]

private theorem pairMutation_scrubLStageV3
    (l r : R2CoherenceV31.Cell ψ κ τ) :
    R2CoherenceBranches.PairQuarantineMutation
      (R2CoherenceV31.eraseCellV3 l) (R2CoherenceV31.eraseCellV3 r)
      (erasePairV3 (R2CoherenceV31.scrubLStageV3 l r)) := by
  by_cases hs : R2CoherenceV31.successorB l r = true
  · by_cases hr : R2CoherenceV31.atRootB r = true
    · simp [R2CoherenceBranches.PairQuarantineMutation,
        R2CoherenceBranches.NonOpen, erasePairV3,
        R2CoherenceV31.scrubLStageV3, R2CoherenceV31.startClosing,
        R2CoherenceV31.setControl, R2CoherenceV31.eraseCellV3,
        R2CoherenceV31.eraseTokenV3, hs, hr]
    · by_cases hl : R2CoherenceV31.atRootB l = true
      · simp [R2CoherenceBranches.PairQuarantineMutation,
          R2CoherenceBranches.NonOpen, erasePairV3,
          R2CoherenceV31.scrubLStageV3, R2CoherenceV31.clearMain,
          R2CoherenceV31.startClosing, R2CoherenceV31.setControl,
          R2CoherenceV31.eraseCellV3, R2CoherenceV31.eraseTokenV3,
          hs, hr, hl]
      · simp [R2CoherenceBranches.PairQuarantineMutation,
          R2CoherenceBranches.NonOpen, erasePairV3,
          R2CoherenceV31.scrubLStageV3, R2CoherenceV31.clearMain,
          R2CoherenceV31.startClosing, R2CoherenceV31.setControl,
          R2CoherenceV31.eraseCellV3, R2CoherenceV31.eraseTokenV3,
          hs, hr, hl]
  · have hsFalse : R2CoherenceV31.successorB l r = false := by
      cases hq : R2CoherenceV31.successorB l r with
      | false => rfl
      | true => exact (hs hq).elim
    simp [R2CoherenceBranches.PairQuarantineMutation,
      R2CoherenceBranches.NonOpen, erasePairV3,
      R2CoherenceV31.scrubLStageV3, R2CoherenceV31.startClosing,
      R2CoherenceV31.setControl, R2CoherenceV31.eraseCellV3,
      R2CoherenceV31.eraseTokenV3, hsFalse]

private theorem pairMutation_scrubL
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2CoherenceV31.Cell ψ κ τ)
    (hb : R2CoherenceV31.branchAtV3 hψ h2 l r = .scrubL) :
    R2CoherenceBranches.PairQuarantineMutation
      (R2CoherenceV31.eraseCellV3 l) (R2CoherenceV31.eraseCellV3 r)
      (erasePairV3
        (R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2 l r)) := by
  rcases branch_scrubL_conditions hψ h2 l r hb with
    ⟨hSeek, hSweep, hCommit, hRelease, hScrub⟩
  unfold R2CoherenceV31.rowV3
  rw [if_neg hSeek, if_neg hSweep, if_neg hCommit,
    if_neg hRelease, if_pos hScrub]
  exact pairMutation_scrubLStageV3 l r

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

theorem release_preservation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    R2CoherenceV31.ReleasePreservationObligationV3
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hRec hb
  rcases hRec with ⟨hGeom, hCoh, hSound⟩
  have hPairGeom := rowV3_geometry_release hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hSame := sameGeometry_stepV3_of_pair hψ h2 ring C e hPairGeom
  refine ⟨admitted_of_sameGeometryV3 hψ ring hSame hGeom, ?_,
    R2CoherenceV31.controllerSoundV3_step hψ h2 ring C e hSound⟩
  by_cases hs :
      R2CoherenceV31.successorB (C e) (C (ring.rightNeighbor e)) = true
  · have hRow := erase_rowV3_release_of_successor hψ h2
      (C e) (C (ring.rightNeighbor e)) hb hs
    have hStep := erase_stepV3_of_row hψ h2 ring C e hRow
    have hOld : R2Coherence.CoherentPrefixes ring
        (R2Coherence.step hψ h2 ring (R2CoherenceV31.eraseCfgV3 C) e) :=
      R2CoherenceBranches.release_preservation
        (κ := κ) (τ := τ) hψ h2 ring
        (R2CoherenceV31.eraseCfgV3 C) e hGeom hCoh
        (erase_branchAtV3_release hψ h2 ring C e hb)
    change R2Coherence.CoherentPrefixes ring
      (R2CoherenceV31.eraseCfgV3
        (R2CoherenceV31.stepV3 hψ h2 ring C e))
    rw [hStep]
    exact hOld
  · have hsFalse :
        R2CoherenceV31.successorB (C e) (C (ring.rightNeighbor e)) = false := by
      cases hq : R2CoherenceV31.successorB
          (C e) (C (ring.rightNeighbor e)) with
      | false => rfl
      | true => exact (hs hq).elim
    have hPair := pairMutation_release_bad hψ h2
      (C e) (C (ring.rightNeighbor e)) hb hsFalse
    have hMut := quarantineMutation_erase_stepV3_of_pair
      hψ h2 ring C e hPair
    change R2Coherence.CoherentPrefixes ring
      (R2CoherenceV31.eraseCfgV3
        (R2CoherenceV31.stepV3 hψ h2 ring C e))
    exact R2CoherenceBranches.coherentPrefixes_of_quarantineMutation
      ring hMut hCoh

/-- The new backward scrub is entirely quarantine-safe: every physical change
is a clearMain behind a releasing controller; malformed/root-garbage arms are
control-only fresh-seek restarts. -/
theorem scrubL_preservation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    R2CoherenceV31.ScrubLPreservationObligationV3
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hRec hb
  rcases hRec with ⟨hGeom, hCoh, hSound⟩
  have hPairGeom := rowV3_geometry_scrubL hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hSame := sameGeometry_stepV3_of_pair hψ h2 ring C e hPairGeom
  refine ⟨admitted_of_sameGeometryV3 hψ ring hSame hGeom, ?_,
    R2CoherenceV31.controllerSoundV3_step hψ h2 ring C e hSound⟩
  have hPair := pairMutation_scrubL hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hMut := quarantineMutation_erase_stepV3_of_pair
    hψ h2 ring C e hPair
  change R2Coherence.CoherentPrefixes ring
    (R2CoherenceV31.eraseCfgV3
      (R2CoherenceV31.stepV3 hψ h2 ring C e))
  exact R2CoherenceBranches.coherentPrefixes_of_quarantineMutation
    ring hMut hCoh

end R2CoherenceV31Branches3

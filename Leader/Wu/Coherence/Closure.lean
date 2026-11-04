import Leader.Wu.Coherence.CollisionClosureCounterexample
import Leader.Wu.Coherence.ErasureReleaseScrubL


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31Closure


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches


variable {n ψ κ τ : Nat}


/-- The exact deletion-closed label geometry used by V3.1 coherence closure.
Every directed edge either enters a label-zero group boundary or is a literal
non-wrap successor.  The root need not currently carry a leader. -/
def ElectionGeometryV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ i : Fin n,
    passiveEdgeOKV3 (C i) (C (ring.rightNeighbor i)) = true


instance electionGeometryV31Decidable
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    Decidable (ElectionGeometryV31 ring C) := by
  unfold ElectionGeometryV31
  infer_instance


/-- Coherence closure no longer bundles the stronger leader-sensitive
post-birth geometry. -/
def CoherenceClosedV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) : Prop :=
  ElectionGeometryV31 ring C ∧
    CoherentPrefixesV3 ring C ∧
    ControllerSoundV3 hψ h2 ring C


/-- Geometry is now a separate physical/election invariant leaf. -/
def ElectionGeometryStepV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ElectionGeometryV31 ring C →
      ElectionGeometryV31 ring (stepV3 hψ h2 ring C e)


/-- Restated branch closure: prove only CHECK/ID coherence and controller
soundness.  Geometry closure is `ElectionGeometryStepV31`. -/
def BranchCoherenceObligationV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (b : BranchV3) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    CoherenceClosedV31 hψ h2 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = b →
      CoherentPrefixesV3 ring (stepV3 hψ h2 ring C e) ∧
      ControllerSoundV3 hψ h2 ring (stepV3 hψ h2 ring C e)


/-- Old admitted geometry implies the weaker root-or-successor geometry. -/
theorem admitted_implies_electionGeometryV31
    (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ)
    (hGeom : AdmittedPostBirthGeometryV3 hψ ring C) :
    ElectionGeometryV31 ring C := by
  unfold ElectionGeometryV31
  intro e
  change R2Coherence.AdmittedPostBirthGeometry hψ ring (eraseCfgV3 C) at hGeom
  have hEdge := hGeom.2 e
  change
    (raw (C (ring.rightNeighbor e))).leader = true ∨
      (raw (C (ring.rightNeighbor e))).label =
        ⟨((raw (C e)).label.val + 1) % ψ, Nat.mod_lt _ hψ⟩ at hEdge
  rcases hEdge with hLeader | hSucc
  · have hLeader' :
        (R2Coherence.raw
          ((eraseCfgV3 C) (ring.rightNeighbor e))).leader = true := by
      change (raw (C (ring.rightNeighbor e))).leader = true
      exact hLeader
    have hZero := hGeom.1 (ring.rightNeighbor e) hLeader'
    change
      (raw (C (ring.rightNeighbor e))).label = ⟨0, hψ⟩ at hZero
    have hv : (raw (C (ring.rightNeighbor e))).label.val = 0 := by
      simpa using congrArg Fin.val hZero
    simp [passiveEdgeOKV3, atRootB, hv]
  · have hv :
        (raw (C (ring.rightNeighbor e))).label.val =
          ((raw (C e)).label.val + 1) % ψ := by
      simpa using congrArg Fin.val hSucc
    by_cases hr0 : (raw (C (ring.rightNeighbor e))).label.val = 0
    · simp [passiveEdgeOKV3, atRootB, hr0]
    · have hle : (raw (C e)).label.val + 1 ≤ ψ := by
        omega
      have hne : (raw (C e)).label.val + 1 ≠ ψ := by
        intro heq
        have hz : (raw (C (ring.rightNeighbor e))).label.val = 0 := by
          calc
            (raw (C (ring.rightNeighbor e))).label.val =
                ((raw (C e)).label.val + 1) % ψ := hv
            _ = 0 := by rw [heq, Nat.mod_self]
        exact hr0 hz
      have hlt : (raw (C e)).label.val + 1 < ψ := by
        omega
      have hs :
          (raw (C (ring.rightNeighbor e))).label.val =
            (raw (C e)).label.val + 1 := by
        simpa [Nat.mod_eq_of_lt hlt] using hv
      simp [passiveEdgeOKV3, successorB, hs]


/-- `ElectionGeometryV31` depends only on labels.  This is the direct bridge
for leader-deleting, label-preserving collision services. -/
theorem electionGeometryV31_of_same_labels
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hC : ElectionGeometryV31 ring C)
    (hLab : ∀ i : Fin n, (raw (D i)).label = (raw (C i)).label) :
    ElectionGeometryV31 ring D := by
  intro i
  have h := hC i
  unfold passiveEdgeOKV3 at h ⊢
  unfold atRootB successorB at h ⊢
  rw [hLab i, hLab (ring.rightNeighbor i)]
  exact h


private def erasePairV31
    (q : Cell ψ κ τ × Cell ψ κ τ) :
    R2Coherence.Cell ψ κ τ × R2Coherence.Cell ψ κ τ :=
  (eraseCellV3 q.1, eraseCellV3 q.2)


private theorem quarantineMutation_stepV31_of_pair
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hPair : PairQuarantineMutation
      (eraseCellV3 (C e))
      (eraseCellV3 (C (ring.rightNeighbor e)))
      (erasePairV31
        (rowV3 hψ (by decide : 0 < 2) h2
          (C e) (C (ring.rightNeighbor e))))) :
    QuarantineMutation
      (eraseCfgV3 C)
      (eraseCfgV3 (stepV3 hψ h2 ring C e)) := by
  rcases hPair with ⟨hLM, hRM, hLN, hRN⟩
  intro p
  by_cases hpe : p = e
  · subst p
    simpa [eraseCfgV3, erasePairV31, stepV3, protocolV3,
      PopulationProtocol.step] using And.intro hLM hLN
  · by_cases hpj : p = ring.rightNeighbor e
    · subst p
      simpa [eraseCfgV3, erasePairV31, stepV3, protocolV3,
        PopulationProtocol.step, hpe] using And.intro hRM hRN
    · have hSame :
        (((eraseCfgV3 C) p).phys ≠ ((eraseCfgV3 C) p).phys →
            NonOpen ((eraseCfgV3 C) p)) ∧
          (NonOpen ((eraseCfgV3 C) p) →
            NonOpen ((eraseCfgV3 C) p)) :=
        ⟨fun h => (h rfl).elim, fun h => h⟩
      simpa [eraseCfgV3, stepV3, protocolV3,
        PopulationProtocol.step, hpe, hpj] using hSame


private theorem pairMutation_selfV31
    (l r : Cell ψ κ τ) :
    PairQuarantineMutation (eraseCellV3 l) (eraseCellV3 r)
      (erasePairV31 (l, r)) := by
  simp [PairQuarantineMutation, erasePairV31]


private theorem pairMutation_seekStageV31
    (l r : Cell ψ κ τ) :
    PairQuarantineMutation (eraseCellV3 l) (eraseCellV3 r)
      (erasePairV31 (seekStageV3 l r)) := by
  unfold seekStageV3
  repeat' split <;>
    simp [PairQuarantineMutation, NonOpen, erasePairV31,
      setControl, eraseCellV3, eraseTokenV3]


private theorem pairMutation_sweepStageV31
    (l r : Cell ψ κ τ) :
    PairQuarantineMutation (eraseCellV3 l) (eraseCellV3 r)
      (erasePairV31 (sweepStageV3 l r)) := by
  unfold sweepStageV3
  split <;>
    simp [PairQuarantineMutation, NonOpen, erasePairV31,
      clearMain, startClosing, setControl, eraseCellV3, eraseTokenV3]


private theorem pairMutation_commitStageV31
    (l r : Cell ψ κ τ) :
    PairQuarantineMutation (eraseCellV3 l) (eraseCellV3 r)
      (erasePairV31 (commitStageV3 l r)) := by
  unfold commitStageV3
  dsimp only
  repeat' split <;>
    simp [PairQuarantineMutation, NonOpen, erasePairV31,
      clearMain, setControl, eraseCellV3, eraseTokenV3]


private theorem pairMutation_releaseStageV31
    (l r : Cell ψ κ τ) :
    PairQuarantineMutation (eraseCellV3 l) (eraseCellV3 r)
      (erasePairV31 (releaseStageV3 l r)) := by
  unfold releaseStageV3
  repeat' split <;>
    simp [PairQuarantineMutation, NonOpen, erasePairV31,
      startClosing, setControl, eraseCellV3, eraseTokenV3]


private theorem pairMutation_scrubLStageV31
    (l r : Cell ψ κ τ) :
    PairQuarantineMutation (eraseCellV3 l) (eraseCellV3 r)
      (erasePairV31 (scrubLStageV3 l r)) := by
  unfold scrubLStageV3
  repeat' split <;>
    simp [PairQuarantineMutation, NonOpen, erasePairV31,
      clearMain, startClosing, setControl, eraseCellV3, eraseTokenV3]


private theorem pairMutation_normalizePassiveV31_good
    (l r : Cell ψ κ τ)
    (hGood : passiveEdgeOKV3 l r = true) :
    PairQuarantineMutation (eraseCellV3 l) (eraseCellV3 r)
      (erasePairV31 (normalizePassiveV3 l r)) := by
  rw [normalizePassiveV3_good_edge l r hGood]
  simp [PairQuarantineMutation, NonOpen, erasePairV31,
    startClosing, setControl, eraseCellV3, eraseTokenV3]


private theorem pairMutation_openStageV31_hazard
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ)
    (hHaz :
      let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
      pairHazardV3 l.phys r.phys q.1 q.2 = true) :
    PairQuarantineMutation (eraseCellV3 l) (eraseCellV3 r)
      (erasePairV31
        (openStageV3 hψ (by decide : 0 < 2) h2 l r)) := by
  unfold openStageV3 at *
  dsimp only at hHaz
  rw [if_pos hHaz]
  split <;>
    simp [PairQuarantineMutation, NonOpen, erasePairV31,
      startClosing, setControl, eraseCellV3, eraseTokenV3]


private theorem branch_seek_conditions
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .seek) :
    r.ctl.tok = .seek := by
  unfold branchAtV3 at hb
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
                        pairHazardV3 l.phys r.phys
                            (proposalV3 hψ (by decide : 0 < 2) h2 l r).1
                            (proposalV3 hψ (by decide : 0 < 2) h2 l r).2 = true
                    · simp [hHaz] at hb
                    · simp [hHaz] at hb
                  · rw [if_neg hOpen] at hb
                    cases hb
              · rw [if_neg hNone] at hb
                cases hb



private theorem branch_sweep_conditions
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .sweep) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok = .sweep := by
  unfold branchAtV3 at hb
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
                        pairHazardV3 l.phys r.phys
                            (proposalV3 hψ (by decide : 0 < 2) h2 l r).1
                            (proposalV3 hψ (by decide : 0 < 2) h2 l r).2 = true
                    · simp [hHaz] at hb
                    · simp [hHaz] at hb
                  · rw [if_neg hOpen] at hb
                    cases hb
              · rw [if_neg hNone] at hb
                cases hb



private theorem branch_commit_conditions
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .commit) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok = .commit := by
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
                        pairHazardV3 l.phys r.phys
                            (proposalV3 hψ (by decide : 0 < 2) h2 l r).1
                            (proposalV3 hψ (by decide : 0 < 2) h2 l r).2 = true
                    · simp [hHaz] at hb
                    · simp [hHaz] at hb
                  · rw [if_neg hOpen] at hb
                    cases hb
              · rw [if_neg hNone] at hb
                cases hb



private theorem branch_release_conditions
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .release) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok = .release := by
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
                        pairHazardV3 l.phys r.phys
                            (proposalV3 hψ (by decide : 0 < 2) h2 l r).1
                            (proposalV3 hψ (by decide : 0 < 2) h2 l r).2 = true
                    · simp [hHaz] at hb
                    · simp [hHaz] at hb
                  · rw [if_neg hOpen] at hb
                    cases hb
              · rw [if_neg hNone] at hb
                cases hb



private theorem branch_scrubL_conditions
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .scrubL) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok ≠ .release ∧
      r.ctl.tok = .scrubL := by
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
                        pairHazardV3 l.phys r.phys
                            (proposalV3 hψ (by decide : 0 < 2) h2 l r).1
                            (proposalV3 hψ (by decide : 0 < 2) h2 l r).2 = true
                    · simp [hHaz] at hb
                    · simp [hHaz] at hb
                  · rw [if_neg hOpen] at hb
                    cases hb
              · rw [if_neg hNone] at hb
                cases hb



private theorem branch_openHazard_conditions
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openHazard) :
    l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
      l.ctl.mark = .open ∧ r.ctl.mark = .open ∧
      (let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
       pairHazardV3 l.phys r.phys q.1 q.2 = true) := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all


private theorem branch_mixed_priority_clear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .mixed) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok ≠ .release ∧
      r.ctl.tok ≠ .scrubL ∧ l.ctl.tok ≠ .openR := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all


private theorem pairMutation_seek
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .seek) :
    PairQuarantineMutation (eraseCellV3 l) (eraseCellV3 r)
      (erasePairV31 (rowV3 hψ (by decide : 0 < 2) h2 l r)) := by
  have hs := branch_seek_conditions hψ h2 l r hb
  unfold rowV3
  rw [if_pos hs]
  exact pairMutation_seekStageV31 l r


private theorem pairMutation_sweep
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .sweep) :
    PairQuarantineMutation (eraseCellV3 l) (eraseCellV3 r)
      (erasePairV31 (rowV3 hψ (by decide : 0 < 2) h2 l r)) := by
  rcases branch_sweep_conditions hψ h2 l r hb with ⟨hSeek, hSweep⟩
  unfold rowV3
  rw [if_neg hSeek, if_pos hSweep]
  exact pairMutation_sweepStageV31 l r


private theorem pairMutation_commit
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .commit) :
    PairQuarantineMutation (eraseCellV3 l) (eraseCellV3 r)
      (erasePairV31 (rowV3 hψ (by decide : 0 < 2) h2 l r)) := by
  rcases branch_commit_conditions hψ h2 l r hb with
    ⟨hSeek, hSweep, hCommit⟩
  unfold rowV3
  rw [if_neg hSeek, if_neg hSweep, if_pos hCommit]
  exact pairMutation_commitStageV31 l r


private theorem pairMutation_release
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .release) :
    PairQuarantineMutation (eraseCellV3 l) (eraseCellV3 r)
      (erasePairV31 (rowV3 hψ (by decide : 0 < 2) h2 l r)) := by
  rcases branch_release_conditions hψ h2 l r hb with
    ⟨hSeek, hSweep, hCommit, hRelease⟩
  unfold rowV3
  rw [if_neg hSeek, if_neg hSweep, if_neg hCommit, if_pos hRelease]
  exact pairMutation_releaseStageV31 l r


private theorem pairMutation_scrubL
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .scrubL) :
    PairQuarantineMutation (eraseCellV3 l) (eraseCellV3 r)
      (erasePairV31 (rowV3 hψ (by decide : 0 < 2) h2 l r)) := by
  rcases branch_scrubL_conditions hψ h2 l r hb with
    ⟨hSeek, hSweep, hCommit, hRelease, hScrub⟩
  unfold rowV3
  rw [if_neg hSeek, if_neg hSweep, if_neg hCommit,
    if_neg hRelease, if_pos hScrub]
  exact pairMutation_scrubLStageV31 l r


private theorem pairMutation_openHazard
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openHazard) :
    PairQuarantineMutation (eraseCellV3 l) (eraseCellV3 r)
      (erasePairV31 (rowV3 hψ (by decide : 0 < 2) h2 l r)) := by
  rcases branch_openHazard_conditions hψ h2 l r hb with
    ⟨hln, hrn, hlo, hro, hHaz⟩
  simpa [rowV3, ordinaryStageV3, hln, hrn, hlo, hro] using
    (pairMutation_openStageV31_hazard hψ h2 l r hHaz)


private theorem pairMutation_mixed
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hGood : passiveEdgeOKV3 l r = true)
    (hb : branchAtV3 hψ h2 l r = .mixed) :
    PairQuarantineMutation (eraseCellV3 l) (eraseCellV3 r)
      (erasePairV31 (rowV3 hψ (by decide : 0 < 2) h2 l r)) := by
  rcases branch_mixed_priority_clear hψ h2 l r hb with
    ⟨hSeek, hSweep, hCommit, hRelease, hScrub, hOpenR⟩
  by_cases hNone : l.ctl.tok = .none ∧ r.ctl.tok = .none
  · have hSeal : ¬ (l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed) := by
      intro hs
      have h := hb
      simp [branchAtV3, hSeek, hSweep, hCommit, hRelease,
        hScrub, hOpenR, hNone, hs] at h
    have hOpen : ¬ (l.ctl.mark = .open ∧ r.ctl.mark = .open) := by
      intro ho
      have h := hb
      unfold branchAtV3 at h
      simp [hSeek, hSweep, hCommit, hRelease,
        hScrub, hOpenR, hNone, hSeal, ho] at h
      split at h <;> simp_all
    simpa [rowV3, ordinaryStageV3, hSeek, hSweep, hCommit,
      hRelease, hScrub, hOpenR, hNone, hSeal, hOpen] using
      (pairMutation_normalizePassiveV31_good l r hGood)
  · simpa [rowV3, ordinaryStageV3, hSeek, hSweep, hCommit,
      hRelease, hScrub, hOpenR, hNone] using
      (pairMutation_selfV31 l r)


private theorem coherenceSound_of_pairMutation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hCoh : CoherentPrefixesV3 ring C)
    (hSound : ControllerSoundV3 hψ h2 ring C)
    (hPair : PairQuarantineMutation
      (eraseCellV3 (C e))
      (eraseCellV3 (C (ring.rightNeighbor e)))
      (erasePairV31
        (rowV3 hψ (by decide : 0 < 2) h2
          (C e) (C (ring.rightNeighbor e))))) :
    CoherentPrefixesV3 ring (stepV3 hψ h2 ring C e) ∧
      ControllerSoundV3 hψ h2 ring (stepV3 hψ h2 ring C e) := by
  have hMut := quarantineMutation_stepV31_of_pair
    hψ h2 ring C e hPair
  constructor
  · change R2Coherence.CoherentPrefixes ring
      (eraseCfgV3 (stepV3 hψ h2 ring C e))
    exact coherentPrefixes_of_quarantineMutation ring hMut hCoh
  · exact controllerSoundV3_step hψ h2 ring C e hSound


theorem seek_coherence
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    BranchCoherenceObligationV31 (κ := κ) (τ := τ)
      hψ h2 ring .seek := by
  intro C e hClosed hb
  rcases hClosed with ⟨_, hCoh, hSound⟩
  exact coherenceSound_of_pairMutation hψ h2 ring C e hCoh hSound
    (pairMutation_seek hψ h2
      (C e) (C (ring.rightNeighbor e)) hb)


theorem sweep_coherence
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    BranchCoherenceObligationV31 (κ := κ) (τ := τ)
      hψ h2 ring .sweep := by
  intro C e hClosed hb
  rcases hClosed with ⟨_, hCoh, hSound⟩
  exact coherenceSound_of_pairMutation hψ h2 ring C e hCoh hSound
    (pairMutation_sweep hψ h2
      (C e) (C (ring.rightNeighbor e)) hb)


theorem commit_coherence
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    BranchCoherenceObligationV31 (κ := κ) (τ := τ)
      hψ h2 ring .commit := by
  intro C e hClosed hb
  rcases hClosed with ⟨_, hCoh, hSound⟩
  exact coherenceSound_of_pairMutation hψ h2 ring C e hCoh hSound
    (pairMutation_commit hψ h2
      (C e) (C (ring.rightNeighbor e)) hb)


theorem release_coherence
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    BranchCoherenceObligationV31 (κ := κ) (τ := τ)
      hψ h2 ring .release := by
  intro C e hClosed hb
  rcases hClosed with ⟨_, hCoh, hSound⟩
  exact coherenceSound_of_pairMutation hψ h2 ring C e hCoh hSound
    (pairMutation_release hψ h2
      (C e) (C (ring.rightNeighbor e)) hb)


theorem scrubL_coherence
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    BranchCoherenceObligationV31 (κ := κ) (τ := τ)
      hψ h2 ring .scrubL := by
  intro C e hClosed hb
  rcases hClosed with ⟨_, hCoh, hSound⟩
  exact coherenceSound_of_pairMutation hψ h2 ring C e hCoh hSound
    (pairMutation_scrubL hψ h2
      (C e) (C (ring.rightNeighbor e)) hb)


theorem openHazard_coherence
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    BranchCoherenceObligationV31 (κ := κ) (τ := τ)
      hψ h2 ring .openHazard := by
  intro C e hClosed hb
  rcases hClosed with ⟨_, hCoh, hSound⟩
  exact coherenceSound_of_pairMutation hψ h2 ring C e hCoh hSound
    (pairMutation_openHazard hψ h2
      (C e) (C (ring.rightNeighbor e)) hb)


theorem mixed_coherence
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    BranchCoherenceObligationV31 (κ := κ) (τ := τ)
      hψ h2 ring .mixed := by
  intro C e hClosed hb
  rcases hClosed with ⟨hElection, hCoh, hSound⟩
  have hGood := hElection e
  exact coherenceSound_of_pairMutation hψ h2 ring C e hCoh hSound
    (pairMutation_mixed hψ h2
      (C e) (C (ring.rightNeighbor e)) hGood hb)


end R2CoherenceV31Closure

import Leader.Wu.Coherence.ReachableSweepOwnerFootprint


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31ReachableSweepFresh3


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePlus2
open R2CoherenceV31MainClearTruth R2CoherenceV31FreshnessClear
open R2CoherenceV31ReachableSweepFresh2
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31ReachableSoundFresh


variable {n ψ κ τ : Nat}


def OpenRNonterminalV31 (C : FC n ψ κ τ) : Prop :=
  ∀ o : Fin n, (C o).ctl.tok = .openR →
    (raw (C o)).label.val + 1 < ψ


private theorem row_openRNonterminal_sf3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hl : l.ctl.tok = .openR → (raw l).label.val + 1 < ψ)
    (hr : r.ctl.tok = .openR → (raw r).label.val + 1 < ψ) :
    let q := rowV3 hψ (by decide : 0 < 2) h2 l r
    (q.1.ctl.tok = .openR → (raw q.1).label.val + 1 < ψ) ∧
    (q.2.ctl.tok = .openR → (raw q.2).label.val + 1 < ψ) := by
  dsimp only
  let good := fun q : Cell ψ κ τ × Cell ψ κ τ =>
    (q.1.ctl.tok = .openR → (raw q.1).label.val + 1 < ψ) ∧
    (q.2.ctl.tok = .openR → (raw q.2).label.val + 1 < ψ)
  change good (rowV3 hψ (by decide : 0 < 2) h2 l r)

  have hSeek : good (seekStageV3 l r) := by
    dsimp [good]
    unfold seekStageV3
    repeat' split <;> simp_all [setControl, raw]

  have hSweep : good (sweepStageV3 l r) := by
    dsimp [good]
    by_cases hs : successorB l r = true
    · by_cases ht : atTerminalB r = true
      · simp [sweepStageV3, hs, ht, clearMain, setControl, raw]
      · simp [sweepStageV3, hs, ht, clearMain, setControl, raw]
    · rw [show sweepStageV3 l r = (startClosing l, r) by
        simp [sweepStageV3, hs]]
      constructor
      · intro ho
        simp [startClosing, setControl] at ho
      · exact hr

  have hCommit : good (commitStageV3 l r) := by
    dsimp [good]
    unfold commitStageV3
    dsimp only
    repeat' split <;>
      simp_all [clearMain, setControl, raw]

  have hRelease : good (releaseStageV3 l r) := by
    dsimp [good]
    unfold releaseStageV3
    repeat' split <;>
      simp_all [startClosing, setControl, raw]

  have hScrub : good (scrubLStageV3 l r) := by
    dsimp [good]
    by_cases hs : successorB l r = true
    · by_cases hrr : atRootB r = true
      · rw [show scrubLStageV3 l r = (l, startClosing r) by
          simp [scrubLStageV3, hs, hrr]]
        constructor
        · exact hl
        · intro ho
          simp [startClosing, setControl] at ho
      · by_cases hrl : atRootB l = true
        · rw [show scrubLStageV3 l r =
            (setControl (clearMain l) .releasing .openR,
             setControl (clearMain r) .releasing .none) by
            simp [scrubLStageV3, hs, hrr, hrl]]
          constructor
          · intro _ho
            have hz : (raw l).label.val = 0 := by
              simpa [atRootB] using hrl
            have hlt : (raw l).label.val + 1 < ψ := by
              omega
            simpa [clearMain, setControl, raw] using hlt
          · intro ho
            simp [setControl] at ho
        · rw [show scrubLStageV3 l r =
            (setControl (clearMain l) .releasing .scrubL,
             setControl (clearMain r) .releasing .none) by
            simp [scrubLStageV3, hs, hrr, hrl]]
          constructor <;> intro ho <;> simp [setControl] at ho
    · rw [show scrubLStageV3 l r = (l, startClosing r) by
        simp [scrubLStageV3, hs]]
      constructor
      · exact hl
      · intro ho
        simp [startClosing, setControl] at ho

  have hOpenR : good (openRStageV3 l r) := by
    dsimp [good]
    by_cases hs : successorB l r = true
    · by_cases ht : atTerminalB r = true
      · simp [openRStageV3, hs, ht, clearMain, setControl, raw]
      · rw [show openRStageV3 l r =
            (setControl (clearMain l) .open .none,
             setControl (clearMain r) .releasing .openR) by
            simp [openRStageV3, hs, ht]]
        constructor
        · intro ho
          simp [setControl] at ho
        · intro _ho
          have hne : (raw r).label.val + 1 ≠ ψ := by
            intro heq
            apply ht
            simp [atTerminalB, heq]
          have hri : (raw r).label.val < ψ := (raw r).label.isLt
          have hlt : (raw r).label.val + 1 < ψ := by
            omega
          simpa [clearMain, setControl, raw] using hlt
    · rw [show openRStageV3 l r = (startClosing l, r) by
        simp [openRStageV3, hs]]
      constructor
      · intro ho
        simp [startClosing, setControl] at ho
      · exact hr

  have hOrdinary :
      good (ordinaryStageV3 hψ (by decide : 0 < 2) h2 l r) := by
    dsimp [good]
    unfold ordinaryStageV3
    split
    · split
      · unfold sealedStageV3
        repeat' split <;> simp_all [install, setControl]
      · split
        · unfold openStageV3
          dsimp only
          repeat' split <;>
            simp_all [install, startClosing, setControl]
        · unfold normalizePassiveV3
          split <;>
            simp_all [clearMain, startClosing, setControl]
    · exact ⟨hl, hr⟩

  unfold rowV3
  split
  · exact hSeek
  · split
    · exact hSweep
    · split
      · exact hCommit
      · split
        · exact hRelease
        · split
          · exact hScrub
          · split
            · exact hOpenR
            · exact hOrdinary


theorem openRNonterminal_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) (h : OpenRNonterminalV31 C) :
    OpenRNonterminalV31 (stepV3 hψ h2 ring C e) := by
  have hr := row_openRNonterminal_sf3 hψ h2
    (C e) (C (ring.rightNeighbor e)) (h e) (h (ring.rightNeighbor e))
  dsimp only at hr
  intro p ho
  by_cases hp : p = e
  · subst p
    have hx : (rowV3 hψ (by decide : 0 < 2) h2
        (C e) (C (ring.rightNeighbor e))).1.ctl.tok = .openR := by
      simpa [stepV3, protocolV3, PopulationProtocol.step] using ho
    simpa [stepV3, protocolV3, PopulationProtocol.step] using hr.1 hx
  · by_cases hq : p = ring.rightNeighbor e
    · subst p
      have hx : (rowV3 hψ (by decide : 0 < 2) h2
          (C e) (C (ring.rightNeighbor e))).2.ctl.tok = .openR := by
        simpa [stepV3, protocolV3, PopulationProtocol.step, hp] using ho
      simpa [stepV3, protocolV3, PopulationProtocol.step, hp] using hr.2 hx
    · rw [stepV3_other hψ h2 ring C e p hp hq] at ho ⊢
      exact h p ho


theorem openRNonterminal_entrance
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (hB : BirthEntranceV1 hψ h2 ring C) :
    OpenRNonterminalV31 C := by
  rcases hB.1 with ⟨_, D, _, hEq⟩
  rw [hEq]
  intro o ho
  simp [quarantineInitV31, setControl] at ho


theorem openRNonterminal_of_reachable
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (hR : ReachableFromQuarantineV31 hψ h2 ring C) :
    OpenRNonterminalV31 C := by
  rcases hR with ⟨C0, w, hB, rfl⟩
  have carry : ∀ (v : List (Fin n)) (D : FC n ψ κ τ),
      OpenRNonterminalV31 D →
      OpenRNonterminalV31 (v.foldl (stepV3 hψ h2 ring) D) := by
    intro v
    induction v with
    | nil => intro D h; simpa using h
    | cons a v ih =>
        intro D h
        simp only [List.foldl_cons]
        exact ih _ (openRNonterminal_step hψ h2 ring D a h)
  exact carry w C0 (openRNonterminal_entrance hψ h2 ring C0 hB)


private theorem h3_sf3 : 0 < 3 := by decide
private theorem h23_sf3 : 2 ≤ 3 := by decide
private def ring3_sf3 : DirectedRing 3 := ⟨by decide⟩


theorem q14161_terminalOpenR_shape_unreachable
    (C : FC 3 3 3 48)
    (ho : (C (2 : Fin 3)).ctl.tok = .openR)
    (hl : (raw (C (2 : Fin 3))).label.val = 2) :
    ¬ ReachableFromQuarantineV31 h3_sf3 h23_sf3 ring3_sf3 C := by
  intro hR
  have hlt := (openRNonterminal_of_reachable
    h3_sf3 h23_sf3 ring3_sf3 C hR) (2 : Fin 3) ho
  omega



private theorem seek_token_sf3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .seek) : r.ctl.tok = .seek := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind


private theorem row_seek_sf3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .seek) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = seekStageV3 l r := by
  simp [rowV3, seek_token_sf3 hψ h2 l r hb]


private theorem seekStage_phys_sf3 (l r : Cell ψ κ τ) :
    (seekStageV3 l r).1.phys = l.phys ∧
    (seekStageV3 l r).2.phys = r.phys := by
  unfold seekStageV3
  repeat' split <;> simp [setControl]


private theorem seek_step_phys_sf3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    ∀ p, (stepV3 hψ h2 ring C e p).phys = (C p).phys := by
  intro p
  have hr := row_seek_sf3 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  have hs := seekStage_phys_sf3 (C e) (C (ring.rightNeighbor e))
  by_cases hp : p = e
  · subst p
    simpa [stepV3, protocolV3, PopulationProtocol.step, hr] using hs.1
  · by_cases hq : p = ring.rightNeighbor e
    · subst p
      simpa [stepV3, protocolV3, PopulationProtocol.step, hr, hp] using hs.2
    · exact congrArg Cell.phys (stepV3_other hψ h2 ring C e p hp hq)


private theorem seek_step_raw_sf3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    raw (stepV3 hψ h2 ring C e p) = raw (C p) := by
  change (stepV3 hψ h2 ring C e p).phys.base.core.core =
    (C p).phys.base.core.core
  exact congrArg (fun x : R2.Cell ψ κ τ => x.base.core.core)
    (seek_step_phys_sf3 hψ h2 ring C e hb p)


private theorem seek_step_ctl_shape_sf3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    (stepV3 hψ h2 ring C e p).ctl = (C p).ctl ∨
      ((stepV3 hψ h2 ring C e p).ctl.mark = .closing ∧
       ((stepV3 hψ h2 ring C e p).ctl.tok = .none ∨
        (stepV3 hψ h2 ring C e p).ctl.tok = .seek ∨
        ((stepV3 hψ h2 ring C e p).ctl.tok = .sweep ∧
          atRootB (C p) = true))) := by
  have hr := row_seek_sf3 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  by_cases hp : p = e
  · subst p
    cases hR : atRootB (C (ring.rightNeighbor e)) <;>
      cases hL : atRootB (C e) <;>
      simp [stepV3, protocolV3, PopulationProtocol.step, hr,
        seekStageV3, hR, hL, setControl]
  · by_cases hq : p = ring.rightNeighbor e
    · subst p
      cases hR : atRootB (C (ring.rightNeighbor e)) <;>
        cases hL : atRootB (C e) <;>
        simp [stepV3, protocolV3, PopulationProtocol.step, hr, hp,
          seekStageV3, hR, hL, setControl]
    · left
      rw [stepV3_other hψ h2 ring C e p hp hq]


private theorem seek_post_openR_before_sf3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek)
    (ho : (stepV3 hψ h2 ring C e p).ctl.tok = .openR) :
    (C p).ctl.tok = .openR := by
  rcases seek_step_ctl_shape_sf3 hψ h2 ring C e p hb with h | h
  · rw [h] at ho; exact ho
  · rcases h.2 with hn | hs | hw
    · have hx : (TokenV3.openR : TokenV3) = .none := ho.symm.trans hn
      cases hx
    · have hx : (TokenV3.openR : TokenV3) = .seek := ho.symm.trans hs
      cases hx
    · have hx : (TokenV3.openR : TokenV3) = .sweep := ho.symm.trans hw.1
      cases hx



def CurrentOpenRFootprintFreshProvenanceV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ owner p : Fin n,
    (C owner).ctl.tok = .openR →
    InOpenRFreshFootprintV31 ring C owner p →
      FreshnessClearV31 (C p)


def CurrentOpenRProvenanceV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  OpenRNonterminalV31 C ∧
    CurrentOpenRFootprintFreshProvenanceV31 ring C


def ReachableCurrentOpenRProvenanceV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : FC n ψ κ τ,
    ReachableFromQuarantineV31 (κ := κ) (τ := τ) hψ h2 ring C →
      CurrentOpenRProvenanceV31 (κ := κ) (τ := τ) ring C


private theorem gp_sf3
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hL : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 D) i k =
      R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (D i)).label.val) k =
    R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [hL i]


private theorem pp_sf3
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hL : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change R2Coherence.back ring i ((raw (D i)).label.val - k) =
    R2Coherence.back ring i ((raw (C i)).label.val - k)
  rw [hL i]


private theorem footprintBack_sf3
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hL : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (owner p : Fin n)
    (hf : InOpenRFreshFootprintV31 ring D owner p) :
    InOpenRFreshFootprintV31 ring C owner p := by
  rcases hf with ⟨j, ko, q, ho, kD, hp⟩
  rw [gp_sf3 ring hL j ko.val] at ho
  let f := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hq : R2Coherence.groupPos ring (eraseCfgV3 D) j q.val = f := by
    simpa [f] using gp_sf3 ring hL j q.val
  have hv :
      (raw (D (R2Coherence.groupPos ring (eraseCfgV3 D) j q.val))).label.val =
        (raw (C f)).label.val := by
    rw [hq]
    exact congrArg Fin.val (hL f)
  let kC : Fin ((raw (C f)).label.val + 1) :=
    ⟨kD.val, by simpa only [hv] using kD.isLt⟩
  refine ⟨j, ko, q, ho, kC, ?_⟩
  have hp' : R2Coherence.prefixPos ring (eraseCfgV3 D) f kD.val = p := by
    simpa only [hq] using hp
  simpa [f, kC] using (pp_sf3 ring hL f kD.val).symm.trans hp'


theorem currentOpenRFootprintFreshProvenance_seek_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hP : CurrentOpenRFootprintFreshProvenanceV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    CurrentOpenRFootprintFreshProvenanceV31 ring
      (stepV3 hψ h2 ring C e) := by
  intro owner p hoD hfD
  have hoC := seek_post_openR_before_sf3 hψ h2 ring C e owner hb hoD
  have hLab := stepV3_labels_eq_or_held hψ h2 ring C e
  have hfC := footprintBack_sf3 ring hLab owner p hfD
  have hc := hP owner p hoC hfC
  unfold FreshnessClearV31 at hc ⊢
  rw [seek_step_raw_sf3 hψ h2 ring C e p hb]
  exact hc


theorem currentOpenRProvenance_entrance
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (hB : BirthEntranceV1 hψ h2 ring C) :
    CurrentOpenRProvenanceV31 ring C := by
  refine ⟨openRNonterminal_entrance hψ h2 ring C hB, ?_⟩
  rcases hB.1 with ⟨_, D, _, hEq⟩
  rw [hEq]
  intro owner p ho
  simp [quarantineInitV31, setControl] at ho


theorem currentOpenRProvenance_seek_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hP : CurrentOpenRProvenanceV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    CurrentOpenRProvenanceV31 ring (stepV3 hψ h2 ring C e) := by
  exact ⟨openRNonterminal_step hψ h2 ring C e hP.1,
    currentOpenRFootprintFreshProvenance_seek_step
      hψ h2 ring C e hP.2 hb⟩


theorem reachableCurrentOpenRSweepFootprintFresh_of_provenance
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hP : ReachableCurrentOpenRProvenanceV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    ReachableCurrentOpenRSweepFootprintFreshV31
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C hR sweep owner p _hs ho _hr hf
  exact (hP C hR).2 owner p ho hf


end R2CoherenceV31ReachableSweepFresh3

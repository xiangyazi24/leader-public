import Leader.Wu.Coherence.LabelPreservation


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31OpenNoHazard


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2


variable {n ψ κ τ : Nat}


private theorem bool_false_of_not_true (b : Bool) (h : b ≠ true) :
    b = false := by
  cases b <;> simp_all


private theorem branch_openNoHazard_conditions
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openNoHazard) :
    l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
      l.ctl.mark = .open ∧ r.ctl.mark = .open ∧
      (let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
       pairHazardV3 l.phys r.phys q.1 q.2 = false) := by
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
                    · exact ⟨hNone.1, hNone.2, hOpen.1, hOpen.2,
                        bool_false_of_not_true _ hHaz⟩
                  · rw [if_neg hOpen] at hb
                    cases hb
              · rw [if_neg hNone] at hb
                cases hb


private theorem pairHazardV3_false_pairWrites
    (l r ql qr : R2.Cell ψ κ τ)
    (h : pairHazardV3 l r ql qr = false) :
    R2Coherence.pairWrites l r ql qr = false := by
  cases hw : R2Coherence.pairWrites l r ql qr with
  | false => rfl
  | true =>
      simp [pairHazardV3, R2Coherence.pairHazard, hw] at h


private theorem pairHazardV3_false_pairRelabels
    (l r ql qr : R2.Cell ψ κ τ)
    (h : pairHazardV3 l r ql qr = false) :
    R2Coherence.pairRelabels l r ql qr = false := by
  cases hr : R2Coherence.pairRelabels l r ql qr with
  | false => rfl
  | true =>
      simp [pairHazardV3, R2Coherence.pairHazard, hr] at h


private theorem pairHazardV3_false_pairPaths
    (l r ql qr : R2.Cell ψ κ τ)
    (h : pairHazardV3 l r ql qr = false) :
    pairPathChangesV3 l r ql qr = false := by
  cases hp : pairPathChangesV3 l r ql qr with
  | false => rfl
  | true => simp [pairHazardV3, hp] at h


private theorem pairWrites_false_bits
    (l r ql qr : R2.Cell ψ κ τ)
    (h : R2Coherence.pairWrites l r ql qr = false) :
    l.base.core.core.bit = ql.base.core.core.bit ∧
      r.base.core.core.bit = qr.base.core.core.bit := by
  simpa [R2Coherence.pairWrites, R2Coherence.bitChanged] using h


private theorem pairRelabels_false_labels
    (l r ql qr : R2.Cell ψ κ τ)
    (h : R2Coherence.pairRelabels l r ql qr = false) :
    l.base.core.core.label = ql.base.core.core.label ∧
      r.base.core.core.label = qr.base.core.core.label := by
  simpa [R2Coherence.pairRelabels, R2Coherence.labelChanged] using h


private theorem pairPaths_false_paths
    (l r ql qr : R2.Cell ψ κ τ)
    (h : pairPathChangesV3 l r ql qr = false) :
    l.base.core.core.path = ql.base.core.core.path ∧
      r.base.core.core.path = qr.base.core.core.path := by
  simpa [pairPathChangesV3, pathChangedV3] using h


/-- The fields on which `CoherentPrefixes` depends, apart from `state`. -/
def OpenNoHazardFrameV31 (C D : FC n ψ κ τ) : Prop :=
  ∀ i : Fin n,
    (raw (D i)).label = (raw (C i)).label ∧
    (raw (D i)).bit = (raw (C i)).bit ∧
    (raw (D i)).path = (raw (C i)).path ∧
    (D i).ctl = (C i).ctl


private theorem rowV3_openNoHazard_frame
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openNoHazard) :
    let q := rowV3 hψ (by decide : 0 < 2) h2 l r
    ((raw q.1).label = (raw l).label ∧
      (raw q.1).bit = (raw l).bit ∧
      (raw q.1).path = (raw l).path ∧ q.1.ctl = l.ctl) ∧
    ((raw q.2).label = (raw r).label ∧
      (raw q.2).bit = (raw r).bit ∧
      (raw q.2).path = (raw r).path ∧ q.2.ctl = r.ctl) := by
  rcases branch_openNoHazard_conditions hψ h2 l r hb with
    ⟨hln, hrn, hlo, hro, hHaz⟩
  let p := proposalV3 hψ (by decide : 0 < 2) h2 l r
  have hW := pairHazardV3_false_pairWrites l.phys r.phys p.1 p.2 hHaz
  have hR := pairHazardV3_false_pairRelabels l.phys r.phys p.1 p.2 hHaz
  have hP := pairHazardV3_false_pairPaths l.phys r.phys p.1 p.2 hHaz
  have hBits := pairWrites_false_bits l.phys r.phys p.1 p.2 hW
  have hLabs := pairRelabels_false_labels l.phys r.phys p.1 p.2 hR
  have hPaths := pairPaths_false_paths l.phys r.phys p.1 p.2 hP
  have hrow :
      rowV3 hψ (by decide : 0 < 2) h2 l r =
        (install l p.1, install r p.2) := by
    simp [rowV3, ordinaryStageV3, openStageV3,
      hln, hrn, hlo, hro, p, hHaz]
  rw [hrow]
  constructor
  · refine ⟨?_, ?_, ?_, rfl⟩
    · simpa [install, raw] using hLabs.1.symm
    · simpa [install, raw] using hBits.1.symm
    · simpa [install, raw] using hPaths.1.symm
  · refine ⟨?_, ?_, ?_, rfl⟩
    · simpa [install, raw] using hLabs.2.symm
    · simpa [install, raw] using hBits.2.symm
    · simpa [install, raw] using hPaths.2.symm


/-- Whole-configuration frame for one open-no-hazard service. -/
theorem openNoHazard_step_frame
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) =
      .openNoHazard) :
    OpenNoHazardFrameV31 C (stepV3 hψ h2 ring C e) := by
  intro i
  have hp := rowV3_openNoHazard_frame hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  by_cases hie : i = e
  · subst i
    simpa [stepV3, protocolV3, PopulationProtocol.step] using hp.1
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      simpa [stepV3, protocolV3, PopulationProtocol.step, hie] using hp.2
    · simp [stepV3, protocolV3, PopulationProtocol.step, hie, hij]


private theorem prefixPos_eq_of_openFrame
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D)
    (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change R2Coherence.back ring i ((raw (D i)).label.val - k) =
    R2Coherence.back ring i ((raw (C i)).label.val - k)
  rw [(hF i).1]


private theorem groupPos_eq_of_openFrame
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D)
    (i : Fin n) (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 D) i k =
      R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change
    R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (D i)).label.val) k =
    R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [(hF i).1]


private theorem freshComponent_of_openFrame
    {C D : FC n ψ κ τ} (hF : OpenNoHazardFrameV31 C D)
    (p : Fin n) (k : Nat)
    (h : R2Coherence.freshComponent (eraseCellV3 (C p)) k) :
    R2Coherence.freshComponent (eraseCellV3 (D p)) k := by
  change
    (raw (D p)).label.val = k ∧
      match (raw (D p)).path with
      | .bot => False
      | .some lab b =>
          lab.val = k ∧ b.val = (if (raw (D p)).bit then 1 else 0)
  change
    (raw (C p)).label.val = k ∧
      match (raw (C p)).path with
      | .bot => False
      | .some lab b =>
          lab.val = k ∧ b.val = (if (raw (C p)).bit then 1 else 0) at h
  rcases hF p with ⟨hlab, hbit, hpath, _⟩
  rw [hlab, hbit, hpath]
  exact h


private theorem prefixDead_of_openFrame
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D) (i : Fin n)
    (h : R2Coherence.PrefixDead ring (eraseCfgV3 C) i) :
    R2Coherence.PrefixDead ring (eraseCfgV3 D) i := by
  rcases h with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hp := groupPos_eq_of_openFrame ring hF i k.val
  rw [hp]
  have hc := (hF
    (R2Coherence.groupPos ring (eraseCfgV3 C) i k.val)).2.2.2
  simpa [eraseCfgV3, eraseCellV3, hc] using hk


private theorem existing_equal_coherent_of_openFrame
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D)
    (hC : CoherentPrefixesV3 ring C)
    (i : Fin n) (heq : (raw (C i)).state = .equal) :
    R2Coherence.FreshEqualPrefix ring (eraseCfgV3 D) i := by
  have heq' :
      (R2Coherence.raw ((eraseCfgV3 C) i)).state = .equal := by
    exact heq
  have hOld := hC i heq'
  intro _
  rcases hOld with hdead | hfresh
  · exact Or.inl (prefixDead_of_openFrame ring hF i hdead)
  · right
    have hlabel :
        (R2Coherence.raw ((eraseCfgV3 D) i)).label =
          (R2Coherence.raw ((eraseCfgV3 C) i)).label := by
      exact (hF i).1
    rw [hlabel]
    intro k
    have hp := prefixPos_eq_of_openFrame ring hF i k.val
    rw [hp]
    exact freshComponent_of_openFrame hF _ _ (hfresh k)



/-- Exact remaining physical leaf.  This deliberately says only what is new:
if an open-no-hazard service creates a new `.equal`, its complete current
prefix is fresh.  Existing equals are handled by the frame theorem above.


Source route for proving this proposition:
* `checkSigCheckL_new_equal_fresh` supplies the label-0 base component;
* `checkSigCheckR_new_equal_fresh` supplies the responder component;
* `checkSigCheckR` requires the left CHECK result to be `.equal`, so induction
  extends the already-coherent prefix by exactly one component;
* the missing exported bridge is from a new `.equal` in final `R2.row` to the
  corresponding raw CHECK result inside `doneThroughCheckEntryWidth`. -/
def OpenNoHazardNewEqualPrefixV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ElectionGeometryV31 ring C →
    CoherentPrefixesV3 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openNoHazard →
    let D := stepV3 hψ h2 ring C e
    ∀ i : Fin n,
      (raw (D i)).state = .equal →
      (raw (C i)).state ≠ .equal →
      ∀ k : Fin ((raw (D i)).label.val + 1),
        R2Coherence.freshComponent
          (eraseCellV3
            (D (R2Coherence.prefixPos ring (eraseCfgV3 D) i k.val))) k.val


/-- Once the single final-row CHECK provenance leaf above is exported/proved,
the requested branch theorem has no further semantic obligation. -/
theorem openNoHazard_coherence_of_newEqualPrefix
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hNew : OpenNoHazardNewEqualPrefixV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    BranchCoherenceObligationV31 (κ := κ) (τ := τ)
      hψ h2 ring .openNoHazard := by
  intro C e hClosed hb
  rcases hClosed with ⟨hGeom, hCoh, hSound⟩
  let D := stepV3 hψ h2 ring C e
  have hF : OpenNoHazardFrameV31 C D := by
    simpa [D] using openNoHazard_step_frame hψ h2 ring C e hb
  constructor
  · change R2Coherence.CoherentPrefixes ring (eraseCfgV3 D)
    intro i
    intro heqD0
    have heqD : (raw (D i)).state = .equal := by
      exact heqD0
    by_cases heqC : (raw (C i)).state = .equal
    · exact existing_equal_coherent_of_openFrame ring hF hCoh i heqC heqD0
    · right
      exact hNew C e hGeom hCoh hb i heqD heqC
  · simpa [D] using controllerSoundV3_step hψ h2 ring C e hSound


end R2CoherenceV31OpenNoHazard

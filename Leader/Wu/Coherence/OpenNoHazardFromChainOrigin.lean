import Leader.Wu.Coherence.OpenNoHazardChainOrigin
import Leader.Wu.Coherence.StepClosure

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31OpenNoHazardClose

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31OpenNoHazard
open R2CoherenceV31OpenNoHazardExt
open R2CoherenceV31Step
open R2NewEqualLocal

variable {n ψ κ τ width : Nat}

/-- Strengthened final-row seam.  Freshness and CHECK-chain origin are exported
in one proposition so the V3.1 assembly never has to reconstruct CHECK internals. -/
def SanitizedR2NewEqualFreshChainOriginNoMainMutation
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ) : Prop :=
  ∀ (l r : R2.Cell ψ κ τ),
    let q := R2.row hψ hw hle
      (sanitizeReadyPhys l) (sanitizeReadyPhys r)
    R2MainCarrierFrame l r q →
      (q.1.base.core.core.state = .equal →
        l.base.core.core.state ≠ .equal →
        R2FreshAtOwnLabel q.1 ∧
          q.1.base.core.core.label.val = 0) ∧
      (q.2.base.core.core.state = .equal →
        r.base.core.core.state ≠ .equal →
        R2FreshAtOwnLabel q.2 ∧
          (q.2.base.core.core.label.val = 0 ∨
            q.1.base.core.core.state = .equal))

private theorem bool_false_of_not_true_close
    (b : Bool) (h : b ≠ true) : b = false := by
  cases b <;> simp_all

private theorem branch_openNoHazard_conditions_close
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
                        bool_false_of_not_true_close _ hHaz⟩
                  · rw [if_neg hOpen] at hb
                    cases hb
              · rw [if_neg hNone] at hb
                cases hb

private theorem pairHazardV3_false_pairWrites_close
    (l r ql qr : R2.Cell ψ κ τ)
    (h : pairHazardV3 l r ql qr = false) :
    R2Coherence.pairWrites l r ql qr = false := by
  cases hw : R2Coherence.pairWrites l r ql qr with
  | false => rfl
  | true => simp [pairHazardV3, R2Coherence.pairHazard, hw] at h

private theorem pairHazardV3_false_pairRelabels_close
    (l r ql qr : R2.Cell ψ κ τ)
    (h : pairHazardV3 l r ql qr = false) :
    R2Coherence.pairRelabels l r ql qr = false := by
  cases hr : R2Coherence.pairRelabels l r ql qr with
  | false => rfl
  | true => simp [pairHazardV3, R2Coherence.pairHazard, hr] at h

private theorem pairHazardV3_false_pairPaths_close
    (l r ql qr : R2.Cell ψ κ τ)
    (h : pairHazardV3 l r ql qr = false) :
    pairPathChangesV3 l r ql qr = false := by
  cases hp : pairPathChangesV3 l r ql qr with
  | false => rfl
  | true => simp [pairHazardV3, hp] at h

private theorem pairWrites_false_bits_close
    (l r ql qr : R2.Cell ψ κ τ)
    (h : R2Coherence.pairWrites l r ql qr = false) :
    l.base.core.core.bit = ql.base.core.core.bit ∧
      r.base.core.core.bit = qr.base.core.core.bit := by
  simpa [R2Coherence.pairWrites, R2Coherence.bitChanged] using h

private theorem pairRelabels_false_labels_close
    (l r ql qr : R2.Cell ψ κ τ)
    (h : R2Coherence.pairRelabels l r ql qr = false) :
    l.base.core.core.label = ql.base.core.core.label ∧
      r.base.core.core.label = qr.base.core.core.label := by
  simpa [R2Coherence.pairRelabels, R2Coherence.labelChanged] using h

private theorem pairPaths_false_paths_close
    (l r ql qr : R2.Cell ψ κ τ)
    (h : pairPathChangesV3 l r ql qr = false) :
    l.base.core.core.path = ql.base.core.core.path ∧
      r.base.core.core.path = qr.base.core.core.path := by
  simpa [pairPathChangesV3, pathChangedV3] using h

private theorem proposal_main_frame_close
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openNoHazard) :
    let p := proposalV3 hψ (by decide : 0 < 2) h2 l r
    R2MainCarrierFrame l.phys r.phys p := by
  rcases branch_openNoHazard_conditions_close hψ h2 l r hb with
    ⟨_, _, _, _, hHaz⟩
  let p := proposalV3 hψ (by decide : 0 < 2) h2 l r
  have hW := pairHazardV3_false_pairWrites_close
    l.phys r.phys p.1 p.2 hHaz
  have hR := pairHazardV3_false_pairRelabels_close
    l.phys r.phys p.1 p.2 hHaz
  have hP := pairHazardV3_false_pairPaths_close
    l.phys r.phys p.1 p.2 hHaz
  have hBits := pairWrites_false_bits_close l.phys r.phys p.1 p.2 hW
  have hLabs := pairRelabels_false_labels_close l.phys r.phys p.1 p.2 hR
  have hPaths := pairPaths_false_paths_close l.phys r.phys p.1 p.2 hP
  change R2MainCarrierFrame l.phys r.phys p
  unfold R2MainCarrierFrame
  exact ⟨hLabs.1.symm, hBits.1.symm, hPaths.1.symm,
    hLabs.2.symm, hBits.2.symm, hPaths.2.symm⟩

private theorem rowV3_openNoHazard_eq_install_close
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openNoHazard) :
    let p := proposalV3 hψ (by decide : 0 < 2) h2 l r
    rowV3 hψ (by decide : 0 < 2) h2 l r =
      (install l p.1, install r p.2) := by
  rcases branch_openNoHazard_conditions_close hψ h2 l r hb with
    ⟨hln, hrn, hlo, hro, hHaz⟩
  let p := proposalV3 hψ (by decide : 0 < 2) h2 l r
  change rowV3 hψ (by decide : 0 < 2) h2 l r =
    (install l p.1, install r p.2)
  simp [rowV3, ordinaryStageV3, openStageV3,
    hln, hrn, hlo, hro, p, hHaz]

private theorem step_left_eq_proposal_close
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) =
      .openNoHazard) :
    let p := proposalV3 hψ (by decide : 0 < 2) h2
      (C e) (C (ring.rightNeighbor e))
    (stepV3 hψ h2 ring C e) e = install (C e) p.1 := by
  let p := proposalV3 hψ (by decide : 0 < 2) h2
    (C e) (C (ring.rightNeighbor e))
  have hrow :
      rowV3 hψ (by decide : 0 < 2) h2
          (C e) (C (ring.rightNeighbor e)) =
        (install (C e) p.1,
          install (C (ring.rightNeighbor e)) p.2) := by
    simpa [p] using
      (rowV3_openNoHazard_eq_install_close hψ h2
        (C e) (C (ring.rightNeighbor e)) hb)
  change (stepV3 hψ h2 ring C e) e = install (C e) p.1
  simpa [stepV3, protocolV3, PopulationProtocol.step] using
    congrArg Prod.fst hrow

private theorem step_right_eq_proposal_close
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) =
      .openNoHazard) :
    let p := proposalV3 hψ (by decide : 0 < 2) h2
      (C e) (C (ring.rightNeighbor e))
    (stepV3 hψ h2 ring C e) (ring.rightNeighbor e) =
      install (C (ring.rightNeighbor e)) p.2 := by
  let p := proposalV3 hψ (by decide : 0 < 2) h2
    (C e) (C (ring.rightNeighbor e))
  have hrow :
      rowV3 hψ (by decide : 0 < 2) h2
          (C e) (C (ring.rightNeighbor e)) =
        (install (C e) p.1,
          install (C (ring.rightNeighbor e)) p.2) := by
    simpa [p] using
      (rowV3_openNoHazard_eq_install_close hψ h2
        (C e) (C (ring.rightNeighbor e)) hb)
  change (stepV3 hψ h2 ring C e) (ring.rightNeighbor e) =
    install (C (ring.rightNeighbor e)) p.2
  simpa [stepV3, protocolV3, PopulationProtocol.step, hne] using
    congrArg Prod.snd hrow

private theorem prefixPos_eq_of_openFrame_close
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D)
    (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change R2Coherence.back ring i ((raw (D i)).label.val - k) =
    R2Coherence.back ring i ((raw (C i)).label.val - k)
  rw [(hF i).1]

private theorem groupPos_eq_of_openFrame_close
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

private theorem freshComponent_of_openFrame_close
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

private theorem prefixDead_of_openFrame_close
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D) (i : Fin n)
    (h : R2Coherence.PrefixDead ring (eraseCfgV3 C) i) :
    R2Coherence.PrefixDead ring (eraseCfgV3 D) i := by
  rcases h with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hp := groupPos_eq_of_openFrame_close ring hF i k.val
  rw [hp]
  have hc := (hF
    (R2Coherence.groupPos ring (eraseCfgV3 C) i k.val)).2.2.2
  simpa [eraseCfgV3, eraseCellV3, hc] using hk

private theorem existing_equal_coherent_of_openFrame_close
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
  · exact Or.inl (prefixDead_of_openFrame_close ring hF i hdead)
  · right
    have hlabel :
        (R2Coherence.raw ((eraseCfgV3 D) i)).label =
          (R2Coherence.raw ((eraseCfgV3 C) i)).label := by
      exact (hF i).1
    rw [hlabel]
    intro k
    have hp := prefixPos_eq_of_openFrame_close ring hF i k.val
    rw [hp]
    exact freshComponent_of_openFrame_close hF _ _ (hfresh k)

private theorem freshComponent_install_of_own_close
    (u : Cell ψ κ τ) (p : R2.Cell ψ κ τ)
    (h : R2FreshAtOwnLabel p) :
    R2Coherence.freshComponent (eraseCellV3 (install u p))
      p.base.core.core.label.val := by
  unfold R2FreshAtOwnLabel at h
  change
    p.base.core.core.label.val = p.base.core.core.label.val ∧
      match p.base.core.core.path with
      | .bot => False
      | .some lab b =>
          lab.val = p.base.core.core.label.val ∧
            b.val = (if p.base.core.core.bit then 1 else 0)
  exact ⟨rfl, h⟩

private theorem prefixPos_own_r2_close
    (ring : DirectedRing n) (C : R2Coherence.FC n ψ κ τ)
    (i : Fin n) :
    R2Coherence.prefixPos ring C i
        (R2Coherence.raw (C i)).label.val = i := by
  apply Fin.ext
  simp only [R2Coherence.prefixPos, R2Coherence.back,
    Nat.sub_self, Nat.zero_mod, Nat.sub_zero]
  rw [Nat.add_mod, Nat.mod_eq_of_lt i.isLt, Nat.mod_self,
    Nat.add_zero, Nat.mod_eq_of_lt i.isLt]

private theorem freshPrefix_zero_of_own_close
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n)
    (hzero : (raw (C i)).label.val = 0)
    (hOwn :
      R2Coherence.freshComponent (eraseCellV3 (C i))
        (raw (C i)).label.val) :
    ∀ k : Fin ((raw (C i)).label.val + 1),
      R2Coherence.freshComponent
        (eraseCellV3
          (C (R2Coherence.prefixPos ring (eraseCfgV3 C) i k.val))) k.val := by
  intro k
  have hk : k.val = (raw (C i)).label.val := by
    have hlt := k.isLt
    omega
  have hp := prefixPos_own_r2_close ring (eraseCfgV3 C) i
  change
    R2Coherence.prefixPos ring (eraseCfgV3 C) i
        (raw (C i)).label.val = i at hp
  rw [hk, hp]
  exact hOwn

/-- No extra CHECK-origin seam clause is needed for successor geometry.
A non-root right endpoint plus `ElectionGeometryV31` makes the pre-edge a
successor, and the open-no-hazard frame transports that label equation. -/
private theorem successor_of_election_nonroot_frame_close
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hGeom : ElectionGeometryV31 ring C)
    (hF : OpenNoHazardFrameV31 C D) (e : Fin n)
    (hnz : (raw (D (ring.rightNeighbor e))).label.val ≠ 0) :
    successorB (D e) (D (ring.rightNeighbor e)) = true := by
  have hnzC : (raw (C (ring.rightNeighbor e))).label.val ≠ 0 := by
    intro hz
    apply hnz
    have hv := congrArg Fin.val (hF (ring.rightNeighbor e)).1
    exact hv.trans hz
  have hRoot : atRootB (C (ring.rightNeighbor e)) = false := by
    simp [atRootB, hnzC]
  have hEdge := hGeom e
  unfold passiveEdgeOKV3 at hEdge
  rw [hRoot] at hEdge
  have hsC : successorB (C e) (C (ring.rightNeighbor e)) = true := by
    simpa using hEdge
  have hLe := congrArg Fin.val (hF e).1
  have hLr := congrArg Fin.val (hF (ring.rightNeighbor e)).1
  change decide
    ((raw (D (ring.rightNeighbor e))).label.val =
      (raw (D e)).label.val + 1) = true
  change decide
    ((raw (C (ring.rightNeighbor e))).label.val =
      (raw (C e)).label.val + 1) = true at hsC
  rw [hLr, hLe]
  exact hsC

/-- The open/no-hazard branch closes from the strengthened final-row CHECK
origin seam.  Old equal frontiers are transported by the open frame; a new
root equality is a singleton fresh prefix; and a new non-root right equality
extends the left output prefix with `freshEqualPrefix_successor_ext`. -/
theorem openNoHazard_coherence_of_chainOrigin
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    SanitizedR2NewEqualFreshChainOriginNoMainMutation
        (κ := κ) (τ := τ) hψ (by decide : 0 < 2) h2 →
      OpenNoHazardCoherenceV31 (κ := κ) (τ := τ) hψ h2 ring := by
  intro hChain
  unfold OpenNoHazardCoherenceV31
  intro C e hClosed hb
  rcases hClosed with ⟨hGeom, hCoh, hSound⟩
  let D := stepV3 hψ h2 ring C e
  let p := proposalV3 hψ (by decide : 0 < 2) h2
    (C e) (C (ring.rightNeighbor e))
  have hF : OpenNoHazardFrameV31 C D := by
    simpa [D] using openNoHazard_step_frame hψ h2 ring C e hb
  have hMain :
      R2MainCarrierFrame (C e).phys (C (ring.rightNeighbor e)).phys p := by
    simpa [p] using
      (proposal_main_frame_close hψ h2
        (C e) (C (ring.rightNeighbor e)) hb)
  have hMainR2 :
      R2MainCarrierFrame (C e).phys (C (ring.rightNeighbor e)).phys
        (R2.row hψ (by decide : 0 < 2) h2
          (sanitizeReadyPhys (C e).phys)
          (sanitizeReadyPhys (C (ring.rightNeighbor e)).phys)) := by
    simpa [p, proposalV3] using hMain
  have hPair0 := hChain
    (C e).phys (C (ring.rightNeighbor e)).phys hMainR2
  have hPair :
      (p.1.base.core.core.state = .equal →
        (C e).phys.base.core.core.state ≠ .equal →
        R2FreshAtOwnLabel p.1 ∧
          p.1.base.core.core.label.val = 0) ∧
      (p.2.base.core.core.state = .equal →
        (C (ring.rightNeighbor e)).phys.base.core.core.state ≠ .equal →
        R2FreshAtOwnLabel p.2 ∧
          (p.2.base.core.core.label.val = 0 ∨
            p.1.base.core.core.state = .equal)) := by
    simpa [p, proposalV3] using hPair0
  have hDe : D e = install (C e) p.1 := by
    simpa [D, p] using
      (step_left_eq_proposal_close hψ h2 ring C e hb)
  constructor
  · change R2Coherence.CoherentPrefixes ring (eraseCfgV3 D)
    intro i heqD0
    have heqD : (raw (D i)).state = .equal := heqD0
    by_cases heqC : (raw (C i)).state = .equal
    · exact
        (existing_equal_coherent_of_openFrame_close
          ring hF hCoh i heqC) heqD0
    · by_cases hie : i = e
      · subst i
        have heqP1 : p.1.base.core.core.state = .equal := by
          have h := heqD
          rw [hDe] at h
          simpa [install, raw] using h
        have hneL : (C e).phys.base.core.core.state ≠ .equal := by
          simpa [raw] using heqC
        have hNewL := hPair.1 heqP1 hneL
        have hOwn0 :=
          freshComponent_install_of_own_close (C e) p.1 hNewL.1
        have hOwnD :
            R2Coherence.freshComponent (eraseCellV3 (D e))
              (raw (D e)).label.val := by
          rw [hDe]
          simpa [install, raw] using hOwn0
        have hzD : (raw (D e)).label.val = 0 := by
          rw [hDe]
          simpa [install, raw] using hNewL.2
        right
        exact freshPrefix_zero_of_own_close ring D e hzD hOwnD
      · by_cases hir : i = ring.rightNeighbor e
        · subst i
          have hneRE : ring.rightNeighbor e ≠ e := hie
          have hDr :
              D (ring.rightNeighbor e) =
                install (C (ring.rightNeighbor e)) p.2 := by
            simpa [D, p] using
              (step_right_eq_proposal_close
                hψ h2 ring C e hneRE hb)
          have heqP2 : p.2.base.core.core.state = .equal := by
            have h := heqD
            rw [hDr] at h
            simpa [install, raw] using h
          have hneR :
              (C (ring.rightNeighbor e)).phys.base.core.core.state ≠
                .equal := by
            simpa [raw] using heqC
          have hNewR := hPair.2 heqP2 hneR
          have hOwnR0 :=
            freshComponent_install_of_own_close
              (C (ring.rightNeighbor e)) p.2 hNewR.1
          have hOwnR :
              R2Coherence.freshComponent
                (eraseCellV3 (D (ring.rightNeighbor e)))
                (raw (D (ring.rightNeighbor e))).label.val := by
            rw [hDr]
            simpa [install, raw] using hOwnR0
          by_cases hzR : (raw (D (ring.rightNeighbor e))).label.val = 0
          · right
            exact freshPrefix_zero_of_own_close
              ring D (ring.rightNeighbor e) hzR hOwnR
          · have heqP1 : p.1.base.core.core.state = .equal := by
              rcases hNewR.2 with hzP | hEq
              · have hzD' :
                    (raw (D (ring.rightNeighbor e))).label.val = 0 := by
                  rw [hDr]
                  simpa [install, raw] using hzP
                exact (hzR hzD').elim
              · exact hEq
            have heqLD : (raw (D e)).state = .equal := by
              rw [hDe]
              simpa [install, raw] using heqP1
            have hLeftD :
                R2Coherence.FreshEqualPrefix ring (eraseCfgV3 D) e := by
              by_cases heqCL : (raw (C e)).state = .equal
              · exact existing_equal_coherent_of_openFrame_close
                  ring hF hCoh e heqCL
              · have hneLP :
                    (C e).phys.base.core.core.state ≠ .equal := by
                  simpa [raw] using heqCL
                have hNewL := hPair.1 heqP1 hneLP
                have hOwnL0 :=
                  freshComponent_install_of_own_close
                    (C e) p.1 hNewL.1
                have hOwnL :
                    R2Coherence.freshComponent (eraseCellV3 (D e))
                      (raw (D e)).label.val := by
                  rw [hDe]
                  simpa [install, raw] using hOwnL0
                have hzL : (raw (D e)).label.val = 0 := by
                  rw [hDe]
                  simpa [install, raw] using hNewL.2
                intro _
                exact Or.inr
                  (freshPrefix_zero_of_own_close ring D e hzL hOwnL)
            have hsD :
                successorB (D e) (D (ring.rightNeighbor e)) = true :=
              successor_of_election_nonroot_frame_close
                ring hGeom hF e hzR
            exact
              (freshEqualPrefix_successor_ext
                ring D e hsD heqLD hLeftD hOwnR) heqD0
        · have hsame : D i = C i := by
            simp [D, stepV3, protocolV3,
              PopulationProtocol.step, hie, hir]
          have heqCi : (raw (C i)).state = .equal := by
            rw [← hsame]
            exact heqD
          exact (heqC heqCi).elim
  · simpa [D] using controllerSoundV3_step hψ h2 ring C e hSound


end R2CoherenceV31OpenNoHazardClose

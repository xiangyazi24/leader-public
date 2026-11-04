import Leader.Wu.Coherence.FootprintCoverReleaseSeam
import Leader.Wu.Coherence.ReachableReleaseOwnerAdjacentRoot

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReleaseCoverGeneral

open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure2
open R2CoherenceV31ReachablePlus2 R2CoherenceV31ReachableAdjacentRoot
open R2CoherenceV31ReachableReleaseOwner
open R2CoherenceV31ReachableReleaseOwner2
open R2CoherenceV31FootprintCover3

variable {n ψ κ τ : Nat}

private theorem fwd_zero_general
    (ring : DirectedRing n) (i : Fin n) :
    R2Coherence.fwd ring i 0 = i := by
  apply Fin.ext
  simp [R2Coherence.fwd, Nat.mod_eq_of_lt i.isLt]

/-- General-psi arithmetic classification of a computed window which hits
`owner`: offset zero is anchored; otherwise the hit is at one of the
positive offsets 1,...,psi-1 from the computed group start. -/
def GeneralIncomingOwnerWindowClassifiedV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ (owner j : Fin n) (ko : Fin ψ),
    R2Coherence.groupPos ring (eraseCfgV3 C) j ko.val = owner →
      (ko.val = 0 ∧
        R2Coherence.groupStart ring (eraseCfgV3 C) j = owner) ∨
      (0 < ko.val ∧ ko.val < ψ ∧
        R2Coherence.fwd ring
          (R2Coherence.groupStart ring (eraseCfgV3 C) j) ko.val = owner)

theorem generalIncomingOwnerWindowClassified
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    GeneralIncomingOwnerWindowClassifiedV31 ring C := by
  intro owner j ko hhit
  by_cases hk : ko.val = 0
  · left
    refine ⟨hk, ?_⟩
    change R2Coherence.fwd ring
      (R2Coherence.groupStart ring (eraseCfgV3 C) j) ko.val = owner at hhit
    rw [hk, fwd_zero_general] at hhit
    exact hhit
  · right
    have hkpos : 0 < ko.val := by omega
    refine ⟨hkpos, ko.isLt, ?_⟩
    change R2Coherence.fwd ring
      (R2Coherence.groupStart ring (eraseCfgV3 C) j) ko.val = owner at hhit
    exact hhit

private theorem branchReleaseConditionsGeneral
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .release) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok = .release := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem rowReleaseGeneral
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .release) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = releaseStageV3 l r := by
  rcases branchReleaseConditionsGeneral hψ h2 l r hb with
    ⟨hs, hw, hc, hr⟩
  simp [rowV3, hs, hw, hc, hr]

/-- A scrubL token which is genuinely new in a RELEASE step can only be the
right responder, and RELEASE emits it only on its terminal arm. -/
private theorem releaseNewScrubLOrigin
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release)
    (hnew : (stepV3 hψ h2 ring C e p).ctl.tok = .scrubL)
    (hold : (C p).ctl.tok ≠ .scrubL) :
    p = ring.rightNeighbor e ∧
      atTerminalB (C (ring.rightNeighbor e)) = true := by
  have hr := rowReleaseGeneral hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  by_cases hpe : p = e
  · subst p
    have hx : stepV3 hψ h2 ring C e e =
        (releaseStageV3 (C e) (C (ring.rightNeighbor e))).1 := by
      simp [stepV3, protocolV3, PopulationProtocol.step, hr]
    rw [hx] at hnew
    unfold releaseStageV3 at hnew
    repeat' split at hnew <;> simp_all [setControl, startClosing]
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p
      have hx : stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
          (releaseStageV3 (C e) (C (ring.rightNeighbor e))).2 := by
        simp [stepV3, protocolV3, PopulationProtocol.step, hr, hpe]
      rw [hx] at hnew
      unfold releaseStageV3 at hnew
      repeat' split at hnew <;> simp_all [setControl, startClosing]
    · rw [stepV3_other hψ h2 ring C e p hpe hpr] at hnew
      exact (hold hnew).elim

/-- Exact RELEASE collapse: every genuinely new pending owner forces psi=2. -/
theorem releaseNewPending_forces_psi_two
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release)
    (hD : PendingOpenROwnerV31 ring (stepV3 hψ h2 ring C e) owner)
    (hC : ¬ PendingOpenROwnerV31 ring C owner) :
    ψ = 2 := by
  have h0 := congrArg Fin.val
    (stepV3_labels_eq_or_held hψ h2 ring C e owner)
  have h1 := congrArg Fin.val
    (stepV3_labels_eq_or_held hψ h2 ring C e (ring.rightNeighbor owner))
  have hroot : atRootB (C owner) = true := by
    simpa [atRootB, h0] using hD.2.2
  have hsucc : successorB (C owner) (C (ring.rightNeighbor owner)) = true := by
    simpa [successorB, h0, h1] using hD.2.1
  have hold : (C (ring.rightNeighbor owner)).ctl.tok ≠ .scrubL := by
    intro ht
    exact hC ⟨ht, hsucc, hroot⟩
  have ho := releaseNewScrubLOrigin hψ h2 ring C e
    (ring.rightNeighbor owner) hb hD.1 hold
  have hterm : atTerminalB (C (ring.rightNeighbor owner)) = true := by
    rw [ho.1]
    exact ho.2
  exact (root_successor_terminal_forces_psi_two
    (C owner) (C (ring.rightNeighbor owner)) hroot hsucc hterm).1

/-- On the C-final domain this whole residual is vacuous. -/
theorem releaseNewPendingForeign_of_gt_two
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (h3 : 2 < ψ)
    (ring : DirectedRing n) :
    ReleaseNewPendingForeignFootprintMainClearV31
      (κ := κ) (τ := τ) hψ h2 ring := by
  unfold ReleaseNewPendingForeignFootprintMainClearV31
  intro C e owner p _hg _ht _hp hb
  dsimp only
  intro hD hC _hFoot _hOut
  have hEq := releaseNewPending_forces_psi_two hψ h2 ring C e owner hb hD hC
  omega



/-- The only nonvacuous RELEASE-cover producer debt after the general theorem. -/
def ReleasePsi2PostCoverPrimitivesV31
    (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n 2 κ τ) (e : Fin n),
    branchAtV3 (by decide : 0 < 2) (by decide : 2 ≤ 2)
      (C e) (C (ring.rightNeighbor e)) = .release →
    let D := stepV3 (by decide : 0 < 2) (by decide : 2 ≤ 2) ring C e
    AdjacentRootPredecessorMainClearPsi2V31 ring D ∧
      Psi2PendingFootprintDichotomyV31 ring D

theorem releaseNewPendingForeign_of_psi2_post_primitives
    (ring : DirectedRing n)
    (hPost : ReleasePsi2PostCoverPrimitivesV31 (κ := κ) (τ := τ) ring) :
    ReleaseNewPendingForeignFootprintMainClearV31
      (κ := κ) (τ := τ)
      (by decide : 0 < 2) (by decide : 2 ≤ 2) ring := by
  unfold ReleaseNewPendingForeignFootprintMainClearV31
  intro C e owner p _hg _ht _hp hb
  dsimp only
  intro hD _hC hFoot hOut
  have hP := hPost C e hb
  dsimp only at hP
  exact releaseNewPendingForeign_of_psi2_primitives
    ring (stepV3 (by decide) (by decide) ring C e)
    hP.1 hP.2 owner p hD hFoot hOut

theorem releaseNewPendingForeign_general_of_psi2_post
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hPost : ReleasePsi2PostCoverPrimitivesV31 (κ := κ) (τ := τ) ring) :
    ReleaseNewPendingForeignFootprintMainClearV31
      (κ := κ) (τ := τ) hψ h2 ring := by
  by_cases heq : ψ = 2
  · subst ψ
    simpa using releaseNewPendingForeign_of_psi2_post_primitives
      (n := n) (κ := κ) (τ := τ) ring hPost
  · have h3 : 2 < ψ := by omega
    exact releaseNewPendingForeign_of_gt_two hψ h2 h3 ring


end R2CoherenceV31ReleaseCoverGeneral

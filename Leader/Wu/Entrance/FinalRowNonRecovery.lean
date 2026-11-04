import Leader.Wu.Entrance.ComposedRow

set_option autoImplicit false
set_option Elab.async false

namespace FinalCandidateR2C
namespace FinalCandidateR2C

variable {ψ κ τ : Nat}

/--
The old row selects the SWEEP lane only after ruling out the earlier right-SEEK
priority.  This predicate names exactly the malformed SWEEP geometry that then
falls through `sweepStage`'s `successorB = false` identity arm.
-/
def finalMalformedActiveSweep
    (l r : P ψ κ τ) : Prop :=
  r.ctl.tok ≠ .seek ∧
    l.ctl.tok = .sweep ∧
      R2Coherence.successorB l r = false

/--
The old row selects the RELEASE lane only after ruling out right-SEEK,
left-SWEEP, and right-COMMIT.  This predicate names exactly the malformed
RELEASE geometry that then falls through `releaseStage`'s
`successorB = false` identity arm.
-/
def finalMalformedActiveRelease
    (l r : P ψ κ τ) : Prop :=
  r.ctl.tok ≠ .seek ∧
    l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧
        l.ctl.tok = .release ∧
          R2Coherence.successorB l r = false

/--
The MIXED lane: both directional tokens are absent, but the
marks are neither the coherent sealed pair nor the coherent open pair.
The intended repair is fail-closed `(l, startClosing r)`, not the V3.1
clear-and-reopen normalizer.
-/
def finalTokenFreeMixed
    (l r : P ψ κ τ) : Prop :=
  l.ctl.tok = .none ∧
    r.ctl.tok = .none ∧
      ¬ (l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed) ∧
      ¬ (l.ctl.mark = .open ∧ r.ctl.mark = .open)

/--
The exact non-recovery normalization obligation for the C-final row.

It deliberately says only what the downstream anti-plateau consumer needs:
* malformed SWEEP restarts leftward by `startClosing` on the left;
* malformed RELEASE does the same;
* token-free MIXED fails closed by `startClosing` on the right.

Each conclusion pins the complete stored R2C physical carrier (`CellP.phys`),
not merely its raw labels or bits.  Thus the repair is controller-only on these
three lanes and cannot silently mutate the R2 physical state.
-/
def rowFinal_nonRecovery_normalization_contract
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : Port (κ := κ) (τ := τ) hψ h2) : Prop :=
  ∀ l r : Cell ψ κ τ,
    ¬ FinalGarbage hψ l r →
      (finalMalformedActiveSweep l.phys r.phys →
        let q := rowFinal hψ h2 port l r
        q.1.phys = R2Coherence.startClosing l.phys ∧
          q.2.phys = r.phys) ∧
      (finalMalformedActiveRelease l.phys r.phys →
        let q := rowFinal hψ h2 port l r
        q.1.phys = R2Coherence.startClosing l.phys ∧
          q.2.phys = r.phys) ∧
      (finalTokenFreeMixed l.phys r.phys →
        let q := rowFinal hψ h2 port l r
        q.1.phys = l.phys ∧
          q.2.phys = R2Coherence.startClosing r.phys)

/-- Current main really does stutter on the malformed SWEEP inner lane. -/
theorem r2_row_malformedActiveSweep_is_identity
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : P ψ κ τ)
    (h : finalMalformedActiveSweep l r) :
    R2Coherence.row hψ (by decide : 0 < 2) h2 l r = (l, r) := by
  unfold finalMalformedActiveSweep at h
  rcases h with ⟨hSeek, hSweep, hSucc⟩
  simp [R2Coherence.row, hSeek, hSweep,
    R2Coherence.sweepStage, hSucc]

/-- Current main really does stutter on the malformed RELEASE inner lane. -/
theorem r2_row_malformedActiveRelease_is_identity
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : P ψ κ τ)
    (h : finalMalformedActiveRelease l r) :
    R2Coherence.row hψ (by decide : 0 < 2) h2 l r = (l, r) := by
  unfold finalMalformedActiveRelease at h
  rcases h with ⟨hSeek, hSweep, hCommit, hRelease, hSucc⟩
  simp [R2Coherence.row, hSeek, hSweep, hCommit, hRelease,
    R2Coherence.releaseStage, hSucc]

/-- Current main really does stutter on the token-free MIXED inner lane. -/
theorem r2_row_tokenFreeMixed_is_identity
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : P ψ κ τ)
    (h : finalTokenFreeMixed l r) :
    R2Coherence.row hψ (by decide : 0 < 2) h2 l r = (l, r) := by
  unfold finalTokenFreeMixed at h
  rcases h with ⟨hlTok, hrTok, hSealed, hOpen⟩
  simp [R2Coherence.row, R2Coherence.ordinaryStage,
    hlTok, hrTok, hSealed, hOpen]

/-- Recovery already dominates the final row and bypasses any future
non-recovery normalizer. -/
theorem rowFinal_recovery_of_garbage
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : Port (κ := κ) (τ := τ) hψ h2)
    (l r : Cell ψ κ τ)
    (hg : FinalGarbage hψ l r) :
    rowFinal hψ h2 port l r = recoverPair hψ l r := by
  classical
  unfold rowFinal finalAction
  simp [hg]

end FinalCandidateR2C
end FinalCandidateR2C

import Leader.Wu.Coherence.RingGuardsForceNoToken

set_option autoImplicit false
set_option Elab.async false

namespace ZZV31StageNonIdentity

open R2CoherenceV31

variable {n ψ κ τ width : Nat}

/-- The first `rowV3` guard is on the right SEEK token.  Every branch
consumes it: SEEK -> SWEEP at a root responder, otherwise SEEK -> NONE. -/
theorem seekStageV3_ne_of_right_seek
    (l r : Cell ψ κ τ) (hTok : r.ctl.tok = TokenV3.seek) :
    seekStageV3 l r ≠ (l, r) := by
  intro hEq
  unfold seekStageV3 at hEq
  split at hEq
  · have ht := congrArg
      (fun p : Cell ψ κ τ × Cell ψ κ τ => p.2.ctl.tok) hEq
    change TokenV3.sweep = r.ctl.tok at ht
    rw [hTok] at ht
    cases ht
  · split at hEq
    · have ht := congrArg
        (fun p : Cell ψ κ τ × Cell ψ κ τ => p.2.ctl.tok) hEq
      change TokenV3.none = r.ctl.tok at ht
      rw [hTok] at ht
      cases ht
    · have ht := congrArg
        (fun p : Cell ψ κ τ × Cell ψ κ τ => p.2.ctl.tok) hEq
      change TokenV3.none = r.ctl.tok at ht
      rw [hTok] at ht
      cases ht

/-- The left SWEEP guard is consumed on both geometry branches. -/
theorem sweepStageV3_ne_of_left_sweep
    (l r : Cell ψ κ τ) (hTok : l.ctl.tok = TokenV3.sweep) :
    sweepStageV3 l r ≠ (l, r) := by
  intro hEq
  unfold sweepStageV3 at hEq
  split at hEq
  · dsimp only at hEq
    have ht := congrArg
      (fun p : Cell ψ κ τ × Cell ψ κ τ => p.1.ctl.tok) hEq
    change TokenV3.none = l.ctl.tok at ht
    rw [hTok] at ht
    cases ht
  · have ht := congrArg
      (fun p : Cell ψ κ τ × Cell ψ κ τ => p.1.ctl.tok) hEq
    change TokenV3.seek = l.ctl.tok at ht
    rw [hTok] at ht
    cases ht

/-- The right COMMIT token is replaced by NONE before every branch test. -/
theorem commitStageV3_ne_of_right_commit
    (l r : Cell ψ κ τ) (hTok : r.ctl.tok = TokenV3.commit) :
    commitStageV3 l r ≠ (l, r) := by
  intro hEq
  unfold commitStageV3 at hEq
  dsimp only at hEq
  split at hEq
  · have ht := congrArg
      (fun p : Cell ψ κ τ × Cell ψ κ τ => p.2.ctl.tok) hEq
    change TokenV3.none = r.ctl.tok at ht
    rw [hTok] at ht
    cases ht
  · split at hEq
    · have ht := congrArg
        (fun p : Cell ψ κ τ × Cell ψ κ τ => p.2.ctl.tok) hEq
      change TokenV3.none = r.ctl.tok at ht
      rw [hTok] at ht
      cases ht
    · have ht := congrArg
        (fun p : Cell ψ κ τ × Cell ψ κ τ => p.2.ctl.tok) hEq
      change TokenV3.none = r.ctl.tok at ht
      rw [hTok] at ht
      cases ht

/-- Every RELEASE branch consumes the left RELEASE token. -/
theorem releaseStageV3_ne_of_left_release
    (l r : Cell ψ κ τ) (hTok : l.ctl.tok = TokenV3.release) :
    releaseStageV3 l r ≠ (l, r) := by
  intro hEq
  unfold releaseStageV3 at hEq
  split at hEq
  · split at hEq
    · dsimp only at hEq
      have ht := congrArg
        (fun p : Cell ψ κ τ × Cell ψ κ τ => p.1.ctl.tok) hEq
      change TokenV3.none = l.ctl.tok at ht
      rw [hTok] at ht
      cases ht
    · split at hEq
      · have ht := congrArg
          (fun p : Cell ψ κ τ × Cell ψ κ τ => p.1.ctl.tok) hEq
        change TokenV3.none = l.ctl.tok at ht
        rw [hTok] at ht
        cases ht
      · have ht := congrArg
          (fun p : Cell ψ κ τ × Cell ψ κ τ => p.1.ctl.tok) hEq
        change TokenV3.commit = l.ctl.tok at ht
        rw [hTok] at ht
        cases ht
  · have ht := congrArg
      (fun p : Cell ψ κ τ × Cell ψ κ τ => p.1.ctl.tok) hEq
    change TokenV3.seek = l.ctl.tok at ht
    rw [hTok] at ht
    cases ht

/-- Every SCRUBL branch consumes the right SCRUBL token. -/
theorem scrubLStageV3_ne_of_right_scrubL
    (l r : Cell ψ κ τ) (hTok : r.ctl.tok = TokenV3.scrubL) :
    scrubLStageV3 l r ≠ (l, r) := by
  intro hEq
  unfold scrubLStageV3 at hEq
  split at hEq
  · split at hEq
    · have ht := congrArg
        (fun p : Cell ψ κ τ × Cell ψ κ τ => p.2.ctl.tok) hEq
      change TokenV3.seek = r.ctl.tok at ht
      rw [hTok] at ht
      cases ht
    · dsimp only at hEq
      split at hEq
      · have ht := congrArg
          (fun p : Cell ψ κ τ × Cell ψ κ τ => p.2.ctl.tok) hEq
        change TokenV3.none = r.ctl.tok at ht
        rw [hTok] at ht
        cases ht
      · have ht := congrArg
          (fun p : Cell ψ κ τ × Cell ψ κ τ => p.2.ctl.tok) hEq
        change TokenV3.none = r.ctl.tok at ht
        rw [hTok] at ht
        cases ht
  · have ht := congrArg
      (fun p : Cell ψ κ τ × Cell ψ κ τ => p.2.ctl.tok) hEq
    change TokenV3.seek = r.ctl.tok at ht
    rw [hTok] at ht
    cases ht

/-- The previously unchecked case: OPENR also cannot stutter.
On successor geometry the left token becomes NONE on both terminal branches;
on invalid geometry `startClosing` changes it to SEEK. -/
theorem openRStageV3_ne_of_left_openR
    (l r : Cell ψ κ τ) (hTok : l.ctl.tok = TokenV3.openR) :
    openRStageV3 l r ≠ (l, r) := by
  intro hEq
  unfold openRStageV3 at hEq
  split at hEq
  · dsimp only at hEq
    split at hEq
    · have ht := congrArg
        (fun p : Cell ψ κ τ × Cell ψ κ τ => p.1.ctl.tok) hEq
      change TokenV3.none = l.ctl.tok at ht
      rw [hTok] at ht
      cases ht
    · have ht := congrArg
        (fun p : Cell ψ κ τ × Cell ψ κ τ => p.1.ctl.tok) hEq
      change TokenV3.none = l.ctl.tok at ht
      rw [hTok] at ht
      cases ht
  · have ht := congrArg
      (fun p : Cell ψ κ τ × Cell ψ κ τ => p.1.ctl.tok) hEq
    change TokenV3.seek = l.ctl.tok at ht
    rw [hTok] at ht
    cases ht

/-- If every actual `rowV3` service is the identity, all six directional
guards must fail edge by edge; R261 then collapses every ring token to NONE. -/
theorem rowV3_identity_forces_none
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : R2CoherenceV31.FC n ψ κ τ)
    (hid : ∀ e : Fin n,
      rowV3 hψ hw hle (C e) (C (ring.rightNeighbor e)) =
        (C e, C (ring.rightNeighbor e))) :
    ∀ i : Fin n, (C i).ctl.tok = TokenV3.none := by
  have hGuards : ∀ e : Fin n,
      ((C e).ctl.tok ≠ TokenV3.sweep ∧
       (C e).ctl.tok ≠ TokenV3.release ∧
       (C e).ctl.tok ≠ TokenV3.openR) ∧
      ((C (ring.rightNeighbor e)).ctl.tok ≠ TokenV3.seek ∧
       (C (ring.rightNeighbor e)).ctl.tok ≠ TokenV3.commit ∧
       (C (ring.rightNeighbor e)).ctl.tok ≠ TokenV3.scrubL) := by
    intro e
    have hId := hid e
    have hSeek :
        (C (ring.rightNeighbor e)).ctl.tok ≠ TokenV3.seek := by
      intro hTok
      have hEq := hId
      unfold rowV3 at hEq
      rw [if_pos hTok] at hEq
      exact
        (seekStageV3_ne_of_right_seek
          (C e) (C (ring.rightNeighbor e)) hTok) hEq
    have hSweep : (C e).ctl.tok ≠ TokenV3.sweep := by
      intro hTok
      have hEq := hId
      unfold rowV3 at hEq
      rw [if_neg hSeek, if_pos hTok] at hEq
      exact
        (sweepStageV3_ne_of_left_sweep
          (C e) (C (ring.rightNeighbor e)) hTok) hEq
    have hCommit :
        (C (ring.rightNeighbor e)).ctl.tok ≠ TokenV3.commit := by
      intro hTok
      have hEq := hId
      unfold rowV3 at hEq
      rw [if_neg hSeek, if_neg hSweep, if_pos hTok] at hEq
      exact
        (commitStageV3_ne_of_right_commit
          (C e) (C (ring.rightNeighbor e)) hTok) hEq
    have hRelease : (C e).ctl.tok ≠ TokenV3.release := by
      intro hTok
      have hEq := hId
      unfold rowV3 at hEq
      rw [if_neg hSeek, if_neg hSweep, if_neg hCommit,
        if_pos hTok] at hEq
      exact
        (releaseStageV3_ne_of_left_release
          (C e) (C (ring.rightNeighbor e)) hTok) hEq
    have hScrubL :
        (C (ring.rightNeighbor e)).ctl.tok ≠ TokenV3.scrubL := by
      intro hTok
      have hEq := hId
      unfold rowV3 at hEq
      rw [if_neg hSeek, if_neg hSweep, if_neg hCommit,
        if_neg hRelease, if_pos hTok] at hEq
      exact
        (scrubLStageV3_ne_of_right_scrubL
          (C e) (C (ring.rightNeighbor e)) hTok) hEq
    have hOpenR : (C e).ctl.tok ≠ TokenV3.openR := by
      intro hTok
      have hEq := hId
      unfold rowV3 at hEq
      rw [if_neg hSeek, if_neg hSweep, if_neg hCommit,
        if_neg hRelease, if_neg hScrubL, if_pos hTok] at hEq
      exact
        (openRStageV3_ne_of_left_openR
          (C e) (C (ring.rightNeighbor e)) hTok) hEq
    exact
      ⟨⟨hSweep, hRelease, hOpenR⟩,
       ⟨hSeek, hCommit, hScrubL⟩⟩
  exact
    ZZV31RingTokenCollapse.ring_all_none_of_guards_fail
      ring hn C (fun e => (hGuards e).1) (fun e => (hGuards e).2)

end ZZV31StageNonIdentity

#print axioms ZZV31StageNonIdentity.seekStageV3_ne_of_right_seek
#print axioms ZZV31StageNonIdentity.sweepStageV3_ne_of_left_sweep
#print axioms ZZV31StageNonIdentity.commitStageV3_ne_of_right_commit
#print axioms ZZV31StageNonIdentity.releaseStageV3_ne_of_left_release
#print axioms ZZV31StageNonIdentity.scrubLStageV3_ne_of_right_scrubL
#print axioms ZZV31StageNonIdentity.openRStageV3_ne_of_left_openR
#print axioms ZZV31StageNonIdentity.rowV3_identity_forces_none

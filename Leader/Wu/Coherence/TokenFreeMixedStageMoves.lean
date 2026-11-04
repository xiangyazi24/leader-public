import Leader.Wu.Coherence.Controller

set_option autoImplicit false
set_option Elab.async false

namespace ZZV31EscapesTokenFreeMixed

variable {ψ κ τ width : Nat}

/--
V3.1 cannot stutter on the token-free mixed/passive lane.

Both directional tokens are absent, while the marks are neither the coherent
sealed pair nor the coherent open pair.  Therefore `ordinaryStageV3` selects
`normalizePassiveV3`; its good-edge branch installs `.seek` on the right, and
its bad-edge branch makes both marks `.open`.  Either change contradicts an
identity output.
-/
theorem ordinaryStageV3_tokenFreeMixed_ne
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : R2CoherenceV31.Cell ψ κ τ)
    (hlTok : l.ctl.tok = R2CoherenceV31.TokenV3.none)
    (hrTok : r.ctl.tok = R2CoherenceV31.TokenV3.none)
    (hNotSealed :
      ¬ (l.ctl.mark = R2Coherence.Mark.sealed ∧
         r.ctl.mark = R2Coherence.Mark.sealed))
    (hNotOpen :
      ¬ (l.ctl.mark = R2Coherence.Mark.open ∧
         r.ctl.mark = R2Coherence.Mark.open)) :
    R2CoherenceV31.ordinaryStageV3 hψ hw hle l r ≠ (l, r) := by
  have hTok :
      l.ctl.tok = R2CoherenceV31.TokenV3.none ∧
        r.ctl.tok = R2CoherenceV31.TokenV3.none :=
    ⟨hlTok, hrTok⟩
  unfold R2CoherenceV31.ordinaryStageV3
  rw [if_pos hTok, if_neg hNotSealed, if_neg hNotOpen]
  cases hPass : R2CoherenceV31.passiveEdgeOKV3 l r with
  | false =>
      rw [R2CoherenceV31.normalizePassiveV3_bad_edge l r hPass]
      intro hEq
      have hLeftMark := congrArg
        (fun q : R2CoherenceV31.Cell ψ κ τ × R2CoherenceV31.Cell ψ κ τ =>
          q.1.ctl.mark) hEq
      have hRightMark := congrArg
        (fun q : R2CoherenceV31.Cell ψ κ τ × R2CoherenceV31.Cell ψ κ τ =>
          q.2.ctl.mark) hEq
      have hlOpen : l.ctl.mark = R2Coherence.Mark.open := by
        simpa [R2CoherenceV31.setControl] using hLeftMark.symm
      have hrOpen : r.ctl.mark = R2Coherence.Mark.open := by
        simpa [R2CoherenceV31.setControl] using hRightMark.symm
      exact hNotOpen ⟨hlOpen, hrOpen⟩
  | true =>
      rw [R2CoherenceV31.normalizePassiveV3_good_edge l r hPass]
      intro hEq
      have hRightTok := congrArg
        (fun q : R2CoherenceV31.Cell ψ κ τ × R2CoherenceV31.Cell ψ κ τ =>
          q.2.ctl.tok) hEq
      have hBad :
          R2CoherenceV31.TokenV3.seek =
            R2CoherenceV31.TokenV3.none := by
        simpa [R2CoherenceV31.startClosing,
          R2CoherenceV31.setControl, hrTok] using hRightTok
      cases hBad

#print axioms ZZV31EscapesTokenFreeMixed.ordinaryStageV3_tokenFreeMixed_ne

end ZZV31EscapesTokenFreeMixed

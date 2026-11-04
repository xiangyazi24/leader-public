import Leader.Wu.Coherence.Controller

set_option autoImplicit false
set_option Elab.async false

namespace ZZRowV32Post

open R2CoherenceV31

variable {ψ κ τ width : Nat}

/-- V3.2 post-row stutter normalizer: keep every moving
V3.1 output, and when V3.1 returns the input pair verbatim, close the responder
instead.  Controller-only write. -/
def rowV32 (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  let q := rowV3 hψ hw hle l r
  if q = (l, r) then (l, startClosing r) else q

/-- The token-free behavior of V3.1 is preserved whenever the row moved. -/
theorem rowV32_of_moves (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) (h : rowV3 hψ hw hle l r ≠ (l, r)) :
    rowV32 hψ hw hle l r = rowV3 hψ hw hle l r := by
  unfold rowV32
  simp only [h, if_false]

/-- On a stuttering input the normalizer changes the responder's controller to
the closing lane, so the pair is no longer fixed. -/
theorem rowV32_stutter_moves (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) (h : rowV3 hψ hw hle l r = (l, r))
    (hne : startClosing r ≠ r) :
    rowV32 hψ hw hle l r ≠ (l, r) := by
  unfold rowV32
  simp only [h, if_true]
  intro hc
  exact hne (Prod.ext_iff.mp hc).2

#print axioms rowV32_of_moves
#print axioms rowV32_stutter_moves

end ZZRowV32Post

import Leader.Wu.Coherence.StrandedTokenNormalizer
import Leader.Wu.Coherence.Controller

set_option autoImplicit false
set_option Elab.async false

namespace ZZRowV32

open R2CoherenceV31

private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide

/-- V3.2 priority repair: stranded pairs are normalized before the six guards. -/
def rowV32
    (l r : R2CoherenceV31.Cell 3 3 48) :
    R2CoherenceV31.Cell 3 3 48 × R2CoherenceV31.Cell 3 3 48 :=
  if h : ZZStrandedNormalizerV32.StrandedTokenV3 l r then
    ZZStrandedNormalizerV32.normalizeStrandedV3 l r
  else
    rowV3 h3 (by decide : 0 < 2) h23 l r

@[simp] theorem rowV32_tokenFree_eq_rowV3
    (l r : R2CoherenceV31.Cell 3 3 48)
    (hl : l.ctl.tok = .none) (hr : r.ctl.tok = .none) :
    rowV32 l r = rowV3 h3 (by decide : 0 < 2) h23 l r := by
  simp [rowV32, ZZStrandedNormalizerV32.StrandedTokenV3, hl, hr]

theorem rowV32_moves_stranded
    (l r : R2CoherenceV31.Cell 3 3 48)
    (h : ZZStrandedNormalizerV32.StrandedTokenV3 l r) :
    rowV32 l r ≠ (l, r) := by
  simp only [rowV32, dif_pos h]
  exact ZZStrandedNormalizerV32.normalizeStrandedV3_moves l r h

theorem rowV32_no_stranded_output
    (l r : R2CoherenceV31.Cell 3 3 48) :
    ¬ ZZStrandedNormalizerV32.StrandedTokenV3
        (ZZStrandedNormalizerV32.normalizeStrandedV3 l r).1
        (ZZStrandedNormalizerV32.normalizeStrandedV3 l r).2 := by
  exact ZZStrandedNormalizerV32.normalizeStrandedV3_not_stranded l r

#print axioms rowV32_moves_stranded
#print axioms rowV32_tokenFree_eq_rowV3

end ZZRowV32

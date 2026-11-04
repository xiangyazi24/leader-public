import Leader.Wu.Splice.SealedLaneRecoveryMoves

set_option autoImplicit false

namespace ZZSealedRowIdentity

open R2CoherenceV31

/-- The sealed cells of the witness: if `rowV3` is the identity on them, the
`u` of the construction is row-frozen. -/
theorem sealed_rowV3_identity :
    rowV3 (by decide : 0 < 3) (by decide : 0 < 2) (by decide : 2 ≤ 3)
      ZZV31SealedInstalled.inner ZZV31SealedInstalled.inner =
      (ZZV31SealedInstalled.inner, ZZV31SealedInstalled.inner) := by
  decide +kernel

end ZZSealedRowIdentity

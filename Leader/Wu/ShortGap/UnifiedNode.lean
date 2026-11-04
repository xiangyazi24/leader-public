import Leader.Wu.ShortGap.SpliceDemotionTable

open ShortGapLiteralGapRows
open ShortGapCaptureCommitRows
open ShortGapSpliceCommit

namespace ShortGapUnifiedNode

set_option autoImplicit false

/--
The exclusive interior-traffic tag for the first unified-node layer.

Selection, capture, and splice are represented by their real carrier payload
alphabets `CwPort`, `CommitCarrier`, and `SnapPhase`.  `RetireWitness` and
`DeclFlush` are splice control state rather than separate interior payload
families, so they remain fields of `UNode` instead of constructors here.
-/
inductive UTraffic where
  | selection (c : CwPort)
  | capture (k : CommitCarrier)
  | splice (s : SnapPhase)
  | empty
  deriving DecidableEq

/--
A flat node containing the complete old `SNode` state plus one exclusive
traffic tag.  Relative to independent traffic-option fields, `UTraffic`
deletes the impossible combinations selection+capture, selection+splice,
capture+splice, and any live traffic family simultaneously with `empty`.
This first file intentionally adds no guard tying the tag to legacy fields
inside `core`; that synchronization belongs to the later dispatcher merge.
-/
structure UNode where
  core : CNode
  bridge : Option SnapPhase
  payload : Option SnapPhase
  splice : SpliceCtl
  witness : RetireWitness
  flush : DeclFlush
  traffic : UTraffic
  deriving DecidableEq

/-- Embed an old splice-layer node with no new unified traffic selected. -/
def ofSNode : SNode → UNode
  | ⟨core, bridge, payload, splice, witness, flush⟩ =>
      ⟨core, bridge, payload, splice, witness, flush, .empty⟩

/-- Forget the new exclusive traffic tag and recover the old splice node. -/
def toSNode : UNode → SNode
  | ⟨core, bridge, payload, splice, witness, flush, _⟩ =>
      ⟨core, bridge, payload, splice, witness, flush⟩

theorem toSNode_ofSNode : ∀ a, toSNode (ofSNode a) = a := by
  intro a
  cases a
  rfl

end ShortGapUnifiedNode

#print axioms ShortGapUnifiedNode.toSNode_ofSNode

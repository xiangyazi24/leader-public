import Leader.Wu.ShortGap.UnifiedNode

open ShortGapLiteralGapRows
open ShortGapCaptureReservation
open ShortGapCaptureCommitRows
open ShortGapSpliceCommit
open ShortGapSpliceFusedRow
open ShortGapSpliceDemotion
open ShortGapUnifiedNode

namespace ShortGapUnifiedGuards

set_option autoImplicit false

/-- All splice-layer guards below mention only fields retained by `UNode`.
The new `traffic` tag is intentionally irrelevant to this equivalence layer,
so no requested guard has to be skipped. -/
def UFreshFlush (a b : UNode) : Prop :=
  a.flush = .unflushed ∧
  b.core.raw.ccwPort = some .heldDenial ∧
  b.flush = .none

theorem UFreshFlush_iff (a b : SNode) :
    UFreshFlush (ofSNode a) (ofSNode b) ↔ FreshFlush a b := by
  cases a
  cases b
  rfl

def UFreshLaunch (a b : UNode) : Prop :=
  a.splice = .armed ∧
  a.flush = .unflushed ∧
  a.core.raw.cwPort = some .toSend ∧
  (b.core.raw = emptyRaw ∧ b.core.carrier = .none) ∧
  b.flush = .none

theorem UFreshLaunch_iff (a b : SNode) :
    UFreshLaunch (ofSNode a) (ofSNode b) ↔ FreshLaunch a b := by
  cases a
  cases b
  rfl

def UFreshForward (a b : UNode) : Prop :=
  a.flush = .unflushed ∧
  a.core.raw = declRaw ∧
  (b.core.raw = emptyRaw ∧ b.core.carrier = .none) ∧
  b.flush = .none

theorem UFreshForward_iff (a b : SNode) :
    UFreshForward (ofSNode a) (ofSNode b) ↔ FreshForward a b := by
  cases a
  cases b
  rfl

def URetireLaunch (a b : UNode) : Prop :=
  (a.core.raw = emptyRaw ∧ a.core.carrier = .none) ∧
  a.witness = .none ∧
  b.splice = .bridged ∧
  b.core.leader = false ∧
  settledCw b.core.raw = true ∧
  b.witness = .none

theorem URetireLaunch_iff (a b : SNode) :
    URetireLaunch (ofSNode a) (ofSNode b) ↔ RetireLaunch a b := by
  cases a
  cases b
  rfl

def URetireBackward (a b : UNode) : Prop :=
  (a.core.raw = emptyRaw ∧ a.core.carrier = .none) ∧
  a.witness = .none ∧
  (b.core.raw = emptyRaw ∧ b.core.carrier = .none) ∧
  b.witness = .token

theorem URetireBackward_iff (a b : SNode) :
    URetireBackward (ofSNode a) (ofSNode b) ↔ RetireBackward a b := by
  cases a
  cases b
  rfl

def URetireDeposit (a b : UNode) : Prop :=
  a.splice = .adopted ∧
  (b.core.raw = emptyRaw ∧ b.core.carrier = .none) ∧
  b.witness = .token

theorem URetireDeposit_iff (a b : SNode) :
    URetireDeposit (ofSNode a) (ofSNode b) ↔ RetireDeposit a b := by
  cases a
  cases b
  rfl

def URetireFused (a b : UNode) : Prop :=
  a.splice = .adopted ∧
  a.witness = .none ∧
  b.splice = .bridged ∧
  b.core.leader = false ∧
  settledCw b.core.raw = true ∧
  b.witness = .none ∧
  ¬ (a.core.raw = emptyRaw ∧ a.core.carrier = .none)

theorem URetireFused_iff (a b : SNode) :
    URetireFused (ofSNode a) (ofSNode b) ↔ RetireFused a b := by
  cases a
  cases b
  rfl

def UAdoptDeposit (a b : UNode) : Prop :=
  Deposit a.core b.core ∧
  b.payload ≠ none ∧
  a.splice = .inactive

theorem UAdoptDeposit_iff (a b : SNode) :
    UAdoptDeposit (ofSNode a) (ofSNode b) ↔ AdoptDeposit a b := by
  cases a
  cases b
  rfl

def UDirectAdopt (a : UNode) : Prop :=
  a.splice = .inactive ∧
  a.payload ≠ none ∧
  rawOwner a.core.raw = true ∧
  a.core.outgoing = .clean

theorem UDirectAdopt_iff (a : SNode) :
    UDirectAdopt (ofSNode a) ↔ DirectAdopt a := by
  cases a
  rfl

def UHandoffArm (a : UNode) : Prop :=
  a.splice = .retired ∧
  a.core.raw.cwPort ≠ none

theorem UHandoffArm_iff (a : SNode) :
    UHandoffArm (ofSNode a) ↔ HandoffArm a := by
  cases a
  rfl

def USpentBridge (b : UNode) : Prop :=
  b.core.leader = false ∧
  b.splice = .drained ∧
  b.core.carrier = .none ∧
  b.payload = none ∧
  b.witness = .none ∧
  b.flush = .none

theorem USpentBridge_iff (b : SNode) :
    USpentBridge (ofSNode b) ↔ SpentBridge b := by
  cases b
  rfl

def UDemotionEnabled (a b : UNode) : Prop :=
  USpentBridge b ∧ a.splice = .armed

theorem UDemotionEnabled_iff (a b : SNode) :
    UDemotionEnabled (ofSNode a) (ofSNode b) ↔ DemotionEnabled a b := by
  cases a
  cases b
  rfl

#print axioms ShortGapUnifiedGuards.UFreshFlush_iff
#print axioms ShortGapUnifiedGuards.UFreshLaunch_iff
#print axioms ShortGapUnifiedGuards.UFreshForward_iff
#print axioms ShortGapUnifiedGuards.URetireLaunch_iff
#print axioms ShortGapUnifiedGuards.URetireBackward_iff
#print axioms ShortGapUnifiedGuards.URetireDeposit_iff
#print axioms ShortGapUnifiedGuards.URetireFused_iff
#print axioms ShortGapUnifiedGuards.UAdoptDeposit_iff
#print axioms ShortGapUnifiedGuards.UDirectAdopt_iff
#print axioms ShortGapUnifiedGuards.UHandoffArm_iff
#print axioms ShortGapUnifiedGuards.USpentBridge_iff
#print axioms ShortGapUnifiedGuards.UDemotionEnabled_iff

end ShortGapUnifiedGuards

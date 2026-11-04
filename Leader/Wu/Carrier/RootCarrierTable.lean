import Leader.Core.Basic

/-!
# Literal PPLL-v2 root/carrier table

This file is the Lean transcription of
`scripts/positive_gap_radius_one_model.py`.  The root alphabet has exactly
26 values and a carrier is the product of three lane marks with thirteen
mobile-head values, hence exactly 39 values.  The three ordered local rows
below follow the source model's priority order.

`repairedCellRootStep` is the private QMAT overlay.  It changes only

`F:query-S | target-hold -> F:deny-keep | T`

and delegates every other input to the literal table.  Keeping the complete
alphabet and total rows here prevents the held-validator refinement from
silently replacing the physical table by a four-state toy semantics.
-/

namespace PPLLV2LiteralTable

set_option autoImplicit false
set_option warningAsError true

inductive RootMode where
  | wash (incoming outgoing : Bool)
  | armed
  | fixed (bit incoming outgoing : Bool)
  | probeSource (bit : Bool)
  | ack1Ready
  | commitSource
  | ack2Ready
  | targetReq
  | targetHold
  | stableSource
  | stableTarget
  | spentSource
  | validateSource
  | validateTarget
  | aborting
  deriving DecidableEq, Repr

inductive Mark where
  | empty
  | frozen
  | release
  deriving DecidableEq, Repr

inductive Head where
  | none
  | q0
  | q1
  | ack1
  | denyKeep
  | nack
  | commit
  | ack2
  | release
  | abortRelease
  | querySource
  | queryTarget
  | rollLeft
  deriving DecidableEq, Repr

structure CellMode where
  mark : Mark
  head : Head
  deriving DecidableEq, Repr

def headless (mark : Mark) : CellMode := ⟨mark, .none⟩

def sourceResident : RootMode → Bool
  | .probeSource _ | .ack1Ready | .commitSource | .ack2Ready
  | .spentSource | .validateSource => true
  | _ => false

def localRole : RootMode → Option Bool
  | .stableSource | .spentSource | .validateSource => some false
  | .stableTarget | .validateTarget => some true
  | _ => none

def validationRole (root : RootMode) : Option Bool :=
  if root = .targetHold then some true else localRole root

def advanceWash (incomingEdge : Bool) : RootMode → RootMode
  | .wash incoming outgoing =>
      if incoming && outgoing then .armed
      else if incomingEdge then .wash true outgoing
      else .wash incoming true
  | root => root

def setFixedIncoming : RootMode → RootMode
  | .fixed bit _ outgoing => .fixed bit true outgoing
  | root => root

def cancelSource : RootMode → RootMode
  | .validateSource => .stableSource
  | root => if sourceResident root then .wash false false else root

def isRightHead : Head → Bool
  | .q0 | .q1 | .commit | .release | .abortRelease | .querySource => true
  | _ => false

def isLeftHead : Head → Bool
  | .ack1 | .denyKeep | .nack | .ack2 | .queryTarget | .rollLeft => true
  | _ => false

/-! ## Root-to-carrier row -/

/-- Exact literal outgoing-root-port row `root | carrier`. -/
def rootCellStep (root : RootMode) (carrier : CellMode) :
    RootMode × CellMode :=
  match carrier.head with
  | .queryTarget =>
      let reply := if validationRole root = some false then
        Head.release else Head.abortRelease
      let root' := if root = .spentSource then .stableSource else root
      (root', ⟨.release, reply⟩)
  | .rollLeft =>
      if root = .ack2Ready then (.spentSource, ⟨.release, .release⟩)
      else if root = .stableSource ∨ root = .spentSource then
        (root, ⟨.release, .release⟩)
      else (cancelSource root, ⟨.release, .abortRelease⟩)
  | .ack1 =>
      if root = .probeSource true then (.ack1Ready, headless .release)
      else (cancelSource root, ⟨.release, .abortRelease⟩)
  | .denyKeep =>
      if root = .probeSource false then
        (.fixed false false true, headless .empty)
      else if root = .probeSource true then
        (.fixed true false true, headless .empty)
      else if root = .validateSource then
        (.stableSource, headless .empty)
      else (cancelSource root, headless .empty)
  | .nack =>
      if root = .validateSource then (.wash false false, headless .empty)
      else (cancelSource root, headless .empty)
  | .ack2 =>
      if root = .commitSource then (.ack2Ready, headless .release)
      else (cancelSource root, ⟨.release, .abortRelease⟩)
  | .none =>
      if root = .ack1Ready ∧ carrier.mark = .release then
        (.commitSource, carrier)
      else if root = .commitSource ∧ carrier.mark = .release then
        (.commitSource, ⟨.frozen, .commit⟩)
      else if root = .ack2Ready ∧ carrier.mark = .release then
        (.spentSource, ⟨.release, .release⟩)
      else if root = .spentSource then
        (.spentSource, ⟨.release, .release⟩)
      else if root = .stableSource then
        match carrier.mark with
        | .empty | .frozen => (.validateSource, ⟨.frozen, .querySource⟩)
        | .release => (.stableSource, ⟨.release, .release⟩)
      else if root = .validateSource then
        match carrier.mark with
        | .frozen => (.validateSource, ⟨.frozen, .querySource⟩)
        | .empty => (.stableSource, headless .empty)
        | .release => (.stableSource, ⟨.release, .abortRelease⟩)
      else match root with
        | .fixed bit _incoming _outgoing =>
            if carrier.mark = .empty then
              (.probeSource bit,
                ⟨.frozen, if bit then .q1 else .q0⟩)
            else if carrier.mark = .frozen then
              (root, ⟨.frozen, .nack⟩)
            else (root, ⟨.release, .abortRelease⟩)
        | .probeSource bit =>
            if carrier.mark = .empty then
              (root, ⟨.frozen, if bit then .q1 else .q0⟩)
            else if carrier.mark = .frozen then
              (root, ⟨.frozen, if bit then .q1 else .q0⟩)
            else (.wash false false, ⟨.release, .abortRelease⟩)
        | .ack1Ready | .commitSource | .ack2Ready =>
            if root = .commitSource ∧ carrier.mark = .frozen then
              (root, ⟨.frozen, .commit⟩)
            else (.wash false false,
              ⟨carrier.mark,
                if carrier.mark = .release then .abortRelease else .none⟩)
        | .aborting => (.wash false false, carrier)
        | .wash _ _ => (advanceWash false root, carrier)
        | .armed => (.fixed false false false, carrier)
        | .stableSource | .stableTarget | .validateTarget => (root, carrier)
        | _ =>
            if carrier.mark = .frozen then (root, ⟨.frozen, .nack⟩)
            else if carrier.mark = .release then
              (root, ⟨.release, .abortRelease⟩)
            else (root, carrier)
  | _ => (root, carrier)

/-! ## Carrier-to-root row -/

def queryAtTarget (probeBit : Bool) (target : RootMode) : Head × RootMode :=
  match target with
  | .wash incoming outgoing =>
      if incoming then
        (if probeBit then .nack else .denyKeep,
          advanceWash true target)
      else (if probeBit then .q1 else .q0, .wash true outgoing)
  | .armed => (if probeBit then .q1 else .q0, .fixed false false false)
  | .fixed targetBit _incoming outgoing =>
      if probeBit then
        if targetBit then (.nack, .fixed targetBit true outgoing)
        else (.ack1, .targetReq)
      else if targetBit then
        (.denyKeep, .fixed targetBit true outgoing)
      else (.denyKeep, .wash false false)
  | root => (if probeBit then .nack else .denyKeep, root)

def sourceValidatorAtTarget (target : RootMode) : Head :=
  if validationRole target = some true then .denyKeep else .nack

/-- Exact literal incoming-root-port row `carrier | root`. -/
def literalCellRootStep (carrier : CellMode) (root : RootMode) :
    CellMode × RootMode :=
  match carrier.head with
  | .querySource => (⟨.frozen, sourceValidatorAtTarget root⟩, root)
  | .q0 =>
      let out := queryAtTarget false root
      (⟨.frozen, out.1⟩, out.2)
  | .q1 =>
      let out := queryAtTarget true root
      (⟨.frozen, out.1⟩, out.2)
  | .commit =>
      if root = .targetReq then (⟨.frozen, .ack2⟩, .targetHold)
      else (⟨.frozen, .nack⟩, root)
  | .release =>
      if root = .validateTarget then (headless .empty, .stableTarget)
      else if root = .targetHold then (headless .empty, .stableTarget)
      else if validationRole root = some true then (headless .empty, root)
      else if root = .targetReq then (headless .empty, .wash false false)
      else ( ⟨.empty, .nack⟩,
        if root = .aborting then .wash false false else root)
  | .abortRelease =>
      if root = .validateTarget then (headless .empty, .wash false false)
      else if root = .targetHold ∨ root = .targetReq then
        (headless .empty, .wash false false)
      else (headless .empty,
        if root = .aborting then .wash false false else root)
  | .none =>
      if root = .targetReq then
        match carrier.mark with
        | .frozen => (⟨.frozen, .ack1⟩, root)
        | .release => (carrier, root)
        | .empty => (headless .empty, .wash false false)
      else if root = .targetHold then
        match carrier.mark with
        | .frozen => (⟨.frozen, .ack2⟩, root)
        | .release => (⟨.release, .rollLeft⟩, root)
        | .empty => (headless .empty, .stableTarget)
      else if root = .stableTarget then
        (⟨.release, .queryTarget⟩, .validateTarget)
      else if root = .validateTarget then
        if carrier.mark = .release then
          (⟨.release, .queryTarget⟩, root)
        else (headless .empty, .stableTarget)
      else match root with
        | .aborting => (carrier, .wash false false)
        | .wash _ _ => (carrier, advanceWash true root)
        | .armed => (carrier, .fixed false false false)
        | .stableSource | .stableTarget | .validateSource => (carrier, root)
        | _ =>
            if carrier.mark = .frozen then (⟨.frozen, .nack⟩, root)
            else if carrier.mark = .release then (headless .empty, root)
            else (carrier, root)
  | _ => (carrier, root)

/-- QMAT: the sole repaired physical row. -/
def repairedCellRootStep (carrier : CellMode) (root : RootMode) :
    CellMode × RootMode :=
  if carrier = ⟨.frozen, .querySource⟩ ∧ root = .targetHold then
    (⟨.frozen, .denyKeep⟩, .stableTarget)
  else literalCellRootStep carrier root

@[simp] theorem literal_querySource_targetHold :
    literalCellRootStep ⟨.frozen, .querySource⟩ .targetHold =
      (⟨.frozen, .denyKeep⟩, .targetHold) := by rfl

@[simp] theorem repaired_querySource_targetHold :
    repairedCellRootStep ⟨.frozen, .querySource⟩ .targetHold =
      (⟨.frozen, .denyKeep⟩, .stableTarget) := by
  simp [repairedCellRootStep]

theorem repairedCellRootStep_eq_literal_of_ne
    (carrier : CellMode) (root : RootMode)
    (hne : (carrier, root) ≠ (⟨.frozen, .querySource⟩, .targetHold)) :
    repairedCellRootStep carrier root = literalCellRootStep carrier root := by
  simp only [repairedCellRootStep]
  rw [if_neg]
  simpa [Prod.ext_iff] using hne

/-! ## Carrier-to-carrier row -/

def splitAbort (leftMark rightMark : Mark) : CellMode × CellMode :=
  (⟨leftMark, .nack⟩, ⟨rightMark, .abortRelease⟩)

/-- Exact literal directed carrier row. -/
def cellCellStep (left right : CellMode) : CellMode × CellMode :=
  let lm := left.mark
  let lh := left.head
  let rm := right.mark
  let rh := right.head
  if lh ≠ .none ∧ rh ≠ .none then
    if lh = .querySource ∧ rh = .queryTarget then
      (⟨.frozen, .denyKeep⟩, ⟨.release, .release⟩)
    else if lh = .querySource ∧ (rh = .denyKeep ∨ rh = .nack) then
      (⟨.frozen, rh⟩, headless .empty)
    else if (lh = .release ∨ lh = .abortRelease) ∧ rh = .queryTarget then
      (headless .empty, ⟨.release, lh⟩)
    else if (lh = .release ∨ lh = .abortRelease) ∧ rh = .rollLeft then
      (headless .empty, ⟨.release, lh⟩)
    else if (lh = .denyKeep ∨ lh = .nack) ∧ rh = .queryTarget then
      (⟨.frozen, lh⟩,
        ⟨.release, if lh = .denyKeep then .release else .abortRelease⟩)
    else if lh = .querySource ∧ (rh = .release ∨ rh = .abortRelease) then
      (⟨.frozen,
          if rh = .release then .denyKeep else .nack⟩,
        ⟨.release, rh⟩)
    else if lh = rh ∧ isRightHead lh then
      (headless (if lh = .release ∨ lh = .abortRelease then .empty else .frozen),
        right)
    else if lh = rh ∧ isLeftHead lh then
      (left,
        headless (if lh = .ack1 ∨ lh = .ack2 ∨ lh = .queryTarget ∨
          lh = .rollLeft then .release else .empty))
    else if isLeftHead lh ∧ isRightHead rh then (left, right)
    else splitAbort lm rm
  else if lh = .q0 ∨ lh = .q1 ∨ lh = .querySource then
    if rm = .empty ∨ rm = .frozen then
      (headless .frozen, ⟨.frozen, lh⟩)
    else splitAbort .frozen rm
  else if lh = .commit then
    if rm = .release ∨ rm = .frozen then
      (headless .frozen, ⟨.frozen, .commit⟩)
    else splitAbort .frozen rm
  else if lh = .release ∨ lh = .abortRelease then
    (headless .empty, ⟨rm, lh⟩)
  else if isLeftHead lh then (left, right)
  else if rh = .ack1 ∨ rh = .ack2 then (⟨lm, rh⟩, headless .release)
  else if rh = .queryTarget ∨ rh = .rollLeft then
    if lm = .empty ∨ lm = .release then
      (⟨.release, rh⟩, headless .release)
    else splitAbort lm .release
  else if rh = .denyKeep ∨ rh = .nack then
    (⟨lm, rh⟩, headless .empty)
  else if isRightHead rh then (left, right)
  else if lm = rm then (left, right)
  else if lm = .frozen ∧ rm = .empty then (⟨.frozen, .nack⟩, right)
  else if lm = .empty ∧ rm = .release then (left, ⟨.release, .abortRelease⟩)
  else if lm = .frozen ∧ rm = .release then splitAbort .frozen .release
  else if lm = .empty ∧ rm = .frozen then (left, ⟨.frozen, .nack⟩)
  else if lm = .release ∧ rm = .empty then (⟨.release, .abortRelease⟩, right)
  else splitAbort .release .frozen

/-! The rows used by the parametric held-validator grammar. -/

@[simp] theorem stableSource_empty :
    rootCellStep .stableSource (headless .empty) =
      (.validateSource, ⟨.frozen, .querySource⟩) := by rfl

@[simp] theorem validateSource_frozen :
    rootCellStep .validateSource (headless .frozen) =
      (.validateSource, ⟨.frozen, .querySource⟩) := by rfl

@[simp] theorem validateSource_query :
    rootCellStep .validateSource ⟨.frozen, .querySource⟩ =
      (.validateSource, ⟨.frozen, .querySource⟩) := by rfl

@[simp] theorem validateSource_deny :
    rootCellStep .validateSource ⟨.frozen, .denyKeep⟩ =
      (.stableSource, headless .empty) := by rfl

@[simp] theorem query_empty :
    cellCellStep ⟨.frozen, .querySource⟩ (headless .empty) =
      (headless .frozen, ⟨.frozen, .querySource⟩) := by
  simp [cellCellStep, headless]

@[simp] theorem frozen_deny :
    cellCellStep (headless .frozen) ⟨.frozen, .denyKeep⟩ =
      (⟨.frozen, .denyKeep⟩, headless .empty) := by
  simp [cellCellStep, headless, isLeftHead]

@[simp] theorem query_deny :
    cellCellStep ⟨.frozen, .querySource⟩ ⟨.frozen, .denyKeep⟩ =
      (⟨.frozen, .denyKeep⟩, headless .empty) := by
  simp [cellCellStep, headless]

@[simp] theorem empty_targetHold :
    repairedCellRootStep (headless .empty) .targetHold =
      (headless .empty, .stableTarget) := by
  simp [repairedCellRootStep, literalCellRootStep, headless]

#print axioms repairedCellRootStep_eq_literal_of_ne
#print axioms query_empty
#print axioms query_deny

end PPLLV2LiteralTable

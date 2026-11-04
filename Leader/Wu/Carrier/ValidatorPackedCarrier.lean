import Leader.Wu.Carrier.ValidatorCorridorDenyEdges
import Leader.Wu.Carrier.ParallelGeometryPacked

/-!
# QMAT on the actual packed carrier

The 65 literal endpoint modes are encoded injectively in the existing
`role × rootCtl` fields of `PackedControl`: roots use role `0` and controls
`0..25`; cells `0..31` use role `1`; cells `32..38` use role `2` and controls
`0..6`.  The two payload bits, message, and trail fields are preserved by the
row.  Thus the construction uses the existing `PackedCell h` state space and
does not introduce a sum-valued carrier.
-/

namespace PPLLV2ValidatorPhysicalRefinement

open PPLLV2LiteralTable
open PPLLParallelGeometryLift
open PPLLParallelGeometryPacked
open PPLLLinearCarrierPacking
open PPLLPeriodHColorVoter

set_option autoImplicit false
set_option warningAsError true

inductive PackedLiteralMode where
  | root (mode : RootMode)
  | cell (mode : CellMode)
  deriving DecidableEq, Repr

def rootIndex : RootMode → Fin 26
  | .wash false false => 0
  | .wash false true => 1
  | .wash true false => 2
  | .wash true true => 3
  | .armed => 4
  | .fixed false false false => 5
  | .fixed false false true => 6
  | .fixed false true false => 7
  | .fixed false true true => 8
  | .fixed true false false => 9
  | .fixed true false true => 10
  | .fixed true true false => 11
  | .fixed true true true => 12
  | .probeSource false => 13
  | .probeSource true => 14
  | .ack1Ready => 15
  | .commitSource => 16
  | .ack2Ready => 17
  | .targetReq => 18
  | .targetHold => 19
  | .stableSource => 20
  | .stableTarget => 21
  | .spentSource => 22
  | .validateSource => 23
  | .validateTarget => 24
  | .aborting => 25

def decodeRootIndex : Fin 26 → RootMode
  | ⟨0, _⟩ => .wash false false
  | ⟨1, _⟩ => .wash false true
  | ⟨2, _⟩ => .wash true false
  | ⟨3, _⟩ => .wash true true
  | ⟨4, _⟩ => .armed
  | ⟨5, _⟩ => .fixed false false false
  | ⟨6, _⟩ => .fixed false false true
  | ⟨7, _⟩ => .fixed false true false
  | ⟨8, _⟩ => .fixed false true true
  | ⟨9, _⟩ => .fixed true false false
  | ⟨10, _⟩ => .fixed true false true
  | ⟨11, _⟩ => .fixed true true false
  | ⟨12, _⟩ => .fixed true true true
  | ⟨13, _⟩ => .probeSource false
  | ⟨14, _⟩ => .probeSource true
  | ⟨15, _⟩ => .ack1Ready
  | ⟨16, _⟩ => .commitSource
  | ⟨17, _⟩ => .ack2Ready
  | ⟨18, _⟩ => .targetReq
  | ⟨19, _⟩ => .targetHold
  | ⟨20, _⟩ => .stableSource
  | ⟨21, _⟩ => .stableTarget
  | ⟨22, _⟩ => .spentSource
  | ⟨23, _⟩ => .validateSource
  | ⟨24, _⟩ => .validateTarget
  | ⟨25, _⟩ => .aborting
  | ⟨n + 26, h⟩ => False.elim (by omega)

@[simp] theorem decodeRootIndex_rootIndex (root : RootMode) :
    decodeRootIndex (rootIndex root) = root := by
  cases root with
  | wash incoming outgoing => cases incoming <;> cases outgoing <;> rfl
  | fixed bit incoming outgoing =>
      cases bit <;> cases incoming <;> cases outgoing <;> rfl
  | probeSource bit => cases bit <;> rfl
  | armed | ack1Ready | commitSource | ack2Ready | targetReq | targetHold
    | stableSource | stableTarget | spentSource | validateSource
    | validateTarget | aborting => rfl

def markIndex : Mark → Fin 3
  | .empty => 0
  | .frozen => 1
  | .release => 2

def headIndex : Head → Fin 13
  | .none => 0
  | .q0 => 1
  | .q1 => 2
  | .ack1 => 3
  | .denyKeep => 4
  | .nack => 5
  | .commit => 6
  | .ack2 => 7
  | .release => 8
  | .abortRelease => 9
  | .querySource => 10
  | .queryTarget => 11
  | .rollLeft => 12

def decodeMarkIndex : Fin 3 → Mark
  | ⟨0, _⟩ => .empty
  | ⟨1, _⟩ => .frozen
  | ⟨2, _⟩ => .release
  | ⟨n + 3, h⟩ => False.elim (by omega)

def decodeHeadIndex : Fin 13 → Head
  | ⟨0, _⟩ => .none
  | ⟨1, _⟩ => .q0
  | ⟨2, _⟩ => .q1
  | ⟨3, _⟩ => .ack1
  | ⟨4, _⟩ => .denyKeep
  | ⟨5, _⟩ => .nack
  | ⟨6, _⟩ => .commit
  | ⟨7, _⟩ => .ack2
  | ⟨8, _⟩ => .release
  | ⟨9, _⟩ => .abortRelease
  | ⟨10, _⟩ => .querySource
  | ⟨11, _⟩ => .queryTarget
  | ⟨12, _⟩ => .rollLeft
  | ⟨n + 13, h⟩ => False.elim (by omega)

def cellIndex (cell : CellMode) : Fin 39 :=
  ⟨(cell.mark |> markIndex).val * 13 + (cell.head |> headIndex).val, by
    have hm := (markIndex cell.mark).isLt
    have hh := (headIndex cell.head).isLt
    omega⟩

def decodeCellIndex (code : Fin 39) : CellMode :=
  ⟨decodeMarkIndex ⟨code.val / 13, by omega⟩,
    decodeHeadIndex ⟨code.val % 13, Nat.mod_lt _ (by omega)⟩⟩

@[simp] theorem decodeCellIndex_cellIndex (cell : CellMode) :
    decodeCellIndex (cellIndex cell) = cell := by
  rcases cell with ⟨mark, head⟩
  cases mark <;> cases head <;> rfl

/-- The reserved `role × rootCtl` tag for one literal mode. -/
def literalTag : PackedLiteralMode →
    PPLLPairedFivePassCarrier.Role4 × PPLLPairedFivePassCarrier.RootCtl32
  | .root root => (0, ⟨(rootIndex root).val, by omega⟩)
  | .cell cell =>
      if hlow : (cellIndex cell).val < 32 then
        (1, ⟨(cellIndex cell).val, hlow⟩)
      else (2, ⟨(cellIndex cell).val - 32, by omega⟩)

/-- Partial decoder.  Unreserved tags return `none`; the packed row frames
such inputs. -/
def decodeLiteralTag
    (role : PPLLPairedFivePassCarrier.Role4)
    (control : PPLLPairedFivePassCarrier.RootCtl32) :
    Option PackedLiteralMode :=
  if hroot : role.val = 0 ∧ control.val < 26 then
    some (.root (decodeRootIndex ⟨control.val, hroot.2⟩))
  else if hlow : role.val = 1 then
    some (.cell (decodeCellIndex ⟨control.val, by omega⟩))
  else if hhigh : role.val = 2 ∧ control.val < 7 then
    some (.cell (decodeCellIndex ⟨control.val + 32, by omega⟩))
  else none

@[simp] theorem decodeLiteralTag_literalTag (mode : PackedLiteralMode) :
    decodeLiteralTag (literalTag mode).1 (literalTag mode).2 = some mode := by
  cases mode with
  | root root =>
      simp [literalTag, decodeLiteralTag, decodeRootIndex_rootIndex]
  | cell cell =>
      by_cases hlow : (cellIndex cell).val < 32
      · simp [literalTag, hlow, decodeLiteralTag,
          decodeCellIndex_cellIndex]
      · have hhigh : (cellIndex cell).val - 32 < 7 := by
          have := (cellIndex cell).isLt
          omega
        have hrecover : (cellIndex cell).val - 32 + 32 =
            (cellIndex cell).val := by omega
        simp [literalTag, hlow, decodeLiteralTag, hhigh, hrecover,
          decodeCellIndex_cellIndex]

/-- Canonical packed control for a literal mode. -/
def encodeLiteral (mode : PackedLiteralMode) : PackedControl :=
  { activeBit := false
    stagingBit := false
    role := (literalTag mode).1
    rootCtl := (literalTag mode).2
    message := 0
    trail := 0 }

@[simp] theorem decodeLiteral_encodeLiteral (mode : PackedLiteralMode) :
    decodeLiteralTag (encodeLiteral mode).role (encodeLiteral mode).rootCtl =
      some mode := decodeLiteralTag_literalTag mode

/-- A packed control carries a literal mode exactly when its two reserved tag
fields decode to that mode.  The payload bits, message, and trail remain free. -/
def CarriesLiteral (control : PackedControl) (mode : PackedLiteralMode) : Prop :=
  decodeLiteralTag control.role control.rootCtl = some mode

@[simp] theorem encodeLiteral_carries (mode : PackedLiteralMode) :
    CarriesLiteral (encodeLiteral mode) mode := decodeLiteral_encodeLiteral mode

/-- A packed control's reserved tag decodes to at most one literal mode. -/
theorem carriesLiteral_unique {control : PackedControl}
    {left right : PackedLiteralMode}
    (hleft : CarriesLiteral control left)
    (hright : CarriesLiteral control right) : left = right := by
  exact Option.some.inj (hleft.symm.trans hright)

theorem encodeLiteral_injective : Function.Injective encodeLiteral := by
  intro left right heq
  have hrole := congrArg PackedControl.role heq
  have hctl := congrArg PackedControl.rootCtl heq
  have hdecode :
      decodeLiteralTag (encodeLiteral left).role
          (encodeLiteral left).rootCtl =
        decodeLiteralTag (encodeLiteral right).role
          (encodeLiteral right).rootCtl := by
    rw [hrole, hctl]
  simpa using hdecode

/-- Replace only the two tag fields, preserving the other four packed control
fields verbatim. -/
def writeLiteral (base : PackedControl) (mode : PackedLiteralMode) :
    PackedControl :=
  { base with
    role := (literalTag mode).1
    rootCtl := (literalTag mode).2 }

@[simp] theorem writeLiteral_encodeLiteral (before after : PackedLiteralMode) :
    writeLiteral (encodeLiteral before) after = encodeLiteral after := by
  cases before <;> cases after <;> rfl

/-- The complete literal/QMAT row on decoded modes.  Adjacent roots frame;
that case is excluded by corridor coherence. -/
def packedLiteralModeStep : PackedLiteralMode → PackedLiteralMode →
    PackedLiteralMode × PackedLiteralMode
  | .root left, .cell right =>
      let out := rootCellStep left right
      (.root out.1, .cell out.2)
  | .cell left, .root right =>
      let out := repairedCellRootStep left right
      (.cell out.1, .root out.2)
  | .cell left, .cell right =>
      let out := cellCellStep left right
      (.cell out.1, .cell out.2)
  | .root left, .root right => (.root left, .root right)

/-- Total packed control row.  A malformed/unreserved tag frames; on decoded
inputs the row preserves payload/message/trail and writes only the mode tag. -/
def packedLiteralStep (left right : PackedControl) :
    PackedControl × PackedControl :=
  match decodeLiteralTag left.role left.rootCtl,
      decodeLiteralTag right.role right.rootCtl with
  | some leftMode, some rightMode =>
      let out := packedLiteralModeStep leftMode rightMode
      (writeLiteral left out.1, writeLiteral right out.2)
  | _, _ => (left, right)

/-- QMAT changes only the two literal tag fields.  In particular it neither
produces nor transports the active/staging payload banks used by the later
publication layer. -/
theorem packedLiteralStep_payload_framed (left right : PackedControl) :
    let out := packedLiteralStep left right
    out.1.activeBit = left.activeBit ∧
      out.2.activeBit = right.activeBit ∧
      out.1.stagingBit = left.stagingBit ∧
      out.2.stagingBit = right.stagingBit ∧
      out.1.message = left.message ∧
      out.2.message = right.message ∧
      out.1.trail = left.trail ∧
      out.2.trail = right.trail := by
  cases hleft : decodeLiteralTag left.role left.rootCtl <;>
    cases hright : decodeLiteralTag right.role right.rootCtl <;>
    simp [packedLiteralStep, hleft, hright, writeLiteral]

theorem packedLiteralStep_of_carries (left right : PackedControl)
    (leftMode rightMode : PackedLiteralMode)
    (hleft : CarriesLiteral left leftMode)
    (hright : CarriesLiteral right rightMode) :
    packedLiteralStep left right =
      let out := packedLiteralModeStep leftMode rightMode
      (writeLiteral left out.1, writeLiteral right out.2) := by
  simp only [CarriesLiteral] at hleft hright
  simp [packedLiteralStep, hleft, hright]

@[simp] theorem packedLiteralStep_encodeLiteral
    (left right : PackedLiteralMode) :
    packedLiteralStep (encodeLiteral left) (encodeLiteral right) =
      (encodeLiteral (packedLiteralModeStep left right).1,
        encodeLiteral (packedLiteralModeStep left right).2) := by
  simp [packedLiteralStep]

def packedQmatControlRow (h : Nat) : PackedControlRow h :=
  fun left right => packedLiteralStep left.2 right.2

/-- The actual packed control row agrees exactly with the 26/39/QMAT row on
the encoding image, independently of the two endpoint positions. -/
theorem packedQmatControlRow_encoded {h : Nat} (leftPos rightPos : Fin h)
    (left right : PackedLiteralMode) :
    packedQmatControlRow h (leftPos, encodeLiteral left)
        (rightPos, encodeLiteral right) =
      (encodeLiteral (packedLiteralModeStep left right).1,
        encodeLiteral (packedLiteralModeStep left right).2) := by
  exact packedLiteralStep_encodeLiteral left right

/-! ## Disjoint staging/sanitation reservation -/

/-- Role `3` is reserved for the independent staging/sanitation row. -/
def stagingRole : PPLLPairedFivePassCarrier.Role4 := ⟨3, by omega⟩

def StagingReserved (control : PackedControl) : Bool :=
  control.role == stagingRole

theorem encodeLiteral_not_stagingReserved (mode : PackedLiteralMode) :
    StagingReserved (encodeLiteral mode) = false := by
  have hne0 : (0 : PPLLPairedFivePassCarrier.Role4) ≠ stagingRole := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = 3 at hv
    omega
  have hne1 : (1 : PPLLPairedFivePassCarrier.Role4) ≠ stagingRole := by
    intro h
    have hv := congrArg Fin.val h
    change 1 = 3 at hv
    omega
  have hne2 : (2 : PPLLPairedFivePassCarrier.Role4) ≠ stagingRole := by
    intro h
    have hv := congrArg Fin.val h
    change 2 = 3 at hv
    omega
  cases mode with
  | root root => simp [StagingReserved, encodeLiteral, literalTag, hne0]
  | cell cell =>
      by_cases hlow : (cellIndex cell).val < 32 <;>
        simp [StagingReserved, encodeLiteral, literalTag, hlow, hne1, hne2]

theorem decodeLiteralTag_role_three
    (control : PPLLPairedFivePassCarrier.RootCtl32) :
    decodeLiteralTag stagingRole control = none := by
  have hzero : stagingRole.val ≠ 0 := by
    intro h
    change 3 = 0 at h
    omega
  have hone : stagingRole.val ≠ 1 := by
    intro h
    change 3 = 1 at h
    omega
  have htwo : stagingRole.val ≠ 2 := by
    intro h
    change 3 = 2 at h
    omega
  simp [decodeLiteralTag, hzero, hone, htwo]

def reserveStaging (control : PackedControl) : PackedControl :=
  { control with role := stagingRole }

@[simp] theorem reserveStaging_reserved (control : PackedControl) :
    StagingReserved (reserveStaging control) = true := by
  simp [StagingReserved, reserveStaging]

/-- Higher-priority composition with an arbitrary position-aware staging row.
Any endpoint already tagged by role `3` selects that row, and both outputs are
retagged `3`; otherwise the literal QMAT decoder runs.  This wrapper is needed
because the older staging code uses numeric `rootCtl` phases `24..28` while
preserving an arbitrary role, which is not by itself disjoint from the literal
tags. -/
def prioritizedPackedControlRow (h : Nat) (staging : PackedControlRow h) :
    PackedControlRow h :=
  fun left right =>
    if StagingReserved left.2 || StagingReserved right.2 then
      let out := staging left right
      (reserveStaging out.1, reserveStaging out.2)
    else packedLiteralStep left.2 right.2

/-- Canonically encoded literal inputs always select the QMAT branch. -/
theorem prioritizedPackedControlRow_encoded {h : Nat}
    (staging : PackedControlRow h) (leftPos rightPos : Fin h)
    (left right : PackedLiteralMode) :
    prioritizedPackedControlRow h staging (leftPos, encodeLiteral left)
        (rightPos, encodeLiteral right) =
      (encodeLiteral (packedLiteralModeStep left right).1,
        encodeLiteral (packedLiteralModeStep left right).2) := by
  simp [prioritizedPackedControlRow, encodeLiteral_not_stagingReserved]

/-- A reserved endpoint always selects the higher-priority row. -/
theorem prioritizedPackedControlRow_of_reserved_left {h : Nat}
    (staging : PackedControlRow h)
    (left right : ParallelCell h PackedControl)
    (hleft : StagingReserved left.2 = true) :
    prioritizedPackedControlRow h staging left right =
      let out := staging left right
      (reserveStaging out.1, reserveStaging out.2) := by
  simp [prioritizedPackedControlRow, hleft]

/-! ## Encoded owned corridors -/

structure PackedCorridor (ell : Nat) where
  left : PackedControl
  lane : Fin ell → PackedControl
  right : PackedControl

@[ext] theorem PackedCorridor.ext {ell : Nat} {left right : PackedCorridor ell}
    (hleft : left.left = right.left) (hlane : left.lane = right.lane)
    (hright : left.right = right.right) : left = right := by
  cases left
  cases right
  simp_all

def encodePackedCorridor {ell : Nat} (physical : Corridor ell) :
    PackedCorridor ell :=
  { left := encodeLiteral (.root physical.left)
    lane := fun i => encodeLiteral (.cell (physical.lane i))
    right := encodeLiteral (.root physical.right) }

def updatePackedAt {ell : Nat} (lane : Fin ell → PackedControl)
    (index : Fin ell) (value : PackedControl) : Fin ell → PackedControl :=
  fun i => if i = index then value else lane i

/-- The owned edge operation executed through the actual packed decoder/row.
This has the same edge indexing as `ownedStep`. -/
def packedOwnedStep {ell : Nat} (hell : 0 < ell)
    (physical : PackedCorridor ell) (edge : Fin (ell + 1)) :
    PackedCorridor ell := by
  by_cases hsource : edge.val = 0
  · let out := packedLiteralStep physical.left
        (physical.lane (firstCell hell))
    exact
      { left := out.1
        lane := updatePackedAt physical.lane (firstCell hell) out.2
        right := physical.right }
  · by_cases htarget : edge.val = ell
    · let out := packedLiteralStep (physical.lane (lastCell hell))
          physical.right
      exact
        { left := physical.left
          lane := updatePackedAt physical.lane (lastCell hell) out.1
          right := out.2 }
    · have hleft : edge.val - 1 < ell := by omega
      have hright : edge.val < ell := by omega
      let leftIndex : Fin ell := ⟨edge.val - 1, hleft⟩
      let rightIndex : Fin ell := ⟨edge.val, hright⟩
      let out := packedLiteralStep (physical.lane leftIndex)
        (physical.lane rightIndex)
      exact
        { left := physical.left
          lane := updatePackedAt
            (updatePackedAt physical.lane leftIndex out.1) rightIndex out.2
          right := physical.right }

/-- Encoding commutes with every owned local interaction.  This is the exact
bridge from the full literal table to the existing packed fields. -/
theorem packedOwnedStep_encode {ell : Nat} (hell : 0 < ell)
    (physical : Corridor ell) (edge : Fin (ell + 1)) :
    packedOwnedStep hell (encodePackedCorridor physical) edge =
      encodePackedCorridor (ownedStep hell physical edge) := by
  by_cases hsource : edge.val = 0
  · simp only [packedOwnedStep, ownedStep, hsource]
    dsimp only [encodePackedCorridor]
    simp only [packedLiteralStep_encodeLiteral, packedLiteralModeStep]
    apply PackedCorridor.ext
    · rfl
    · funext i
      by_cases hi : i = firstCell hell <;>
        simp [updatePackedAt, updateAt, hi]
    · rfl
  · by_cases htarget : edge.val = ell
    · have hellne : ell ≠ 0 := Nat.ne_of_gt hell
      simp only [packedOwnedStep, ownedStep, htarget, hellne]
      dsimp only [encodePackedCorridor]
      simp only [packedLiteralStep_encodeLiteral, packedLiteralModeStep]
      apply PackedCorridor.ext
      · rfl
      · funext i
        by_cases hi : i = lastCell hell <;>
          simp [updatePackedAt, updateAt, hi]
      · rfl
    · simp only [packedOwnedStep, ownedStep, hsource, htarget]
      dsimp only [encodePackedCorridor]
      simp only [packedLiteralStep_encodeLiteral, packedLiteralModeStep]
      apply PackedCorridor.ext
      · rfl
      · funext i
        let li : Fin ell := ⟨edge.val - 1, by omega⟩
        let ri : Fin ell := ⟨edge.val, by omega⟩
        by_cases hir : i = ri
        · simp [updatePackedAt, updateAt, ri, hir]
        by_cases hil : i = li
        · subst i
          have hne : edge.val - 1 ≠ edge.val := by omega
          simp [updatePackedAt, updateAt, li, hne]
        · simp [updatePackedAt, updateAt, li, ri, hir, hil]
      · rfl

/-- Actual-packed owned-edge refinement, stated without hiding the encoding
equality behind a new abstract transition. -/
theorem packed_ownedStep_refines {ell : Nat} (hell : 0 < ell)
    (physical : Corridor ell) (before : ValidatorPhase ell)
    (hphysical : Represents physical before) (hactive : before ≠ .exited)
    (edge : Fin (ell + 1)) :
    ∃ after : ValidatorPhase ell,
      packedOwnedStep hell (encodePackedCorridor physical) edge =
          encodePackedCorridor (ownedStep hell physical edge) ∧
        Represents (ownedStep hell physical edge) after ∧
        PPLLV2ValidatorRankRepair.Next before after := by
  obtain ⟨after, hrep, hnext⟩ :=
    active_ownedStep_refines hell physical before hphysical hactive edge
  exact ⟨after, packedOwnedStep_encode hell physical edge, hrep, hnext⟩

/-- The existing packed position voter frames its stabilized grid while the
literal transaction row executes in parallel. -/
theorem packed_qmat_positions_framed {n h : Nat} (hh : 0 < h)
    (ring : DirectedRing n) (q : Fin n → PackedCell h)
    (hgrid : PackedPositionGrid hh ring q) (edge : Fin n) :
    packedPositions
        (packedParallelStep hh ring (packedQmatControlRow h) q edge) =
      packedPositions q := by
  rw [packedPositions_parallelStep]
  exact periodRepairStep_eq_self_of_grid hh ring (packedPositions q) hgrid edge

#print axioms encodeLiteral_injective
#print axioms packedLiteralStep_encodeLiteral
#print axioms packedQmatControlRow_encoded
#print axioms prioritizedPackedControlRow_encoded
#print axioms packedOwnedStep_encode
#print axioms packed_ownedStep_refines
#print axioms packed_qmat_positions_framed

end PPLLV2ValidatorPhysicalRefinement

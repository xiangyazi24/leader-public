import Leader.Wu.Carrier.ValidatorPayloadBoundary

/-!
# Public physical QMAT refinement

This wrapper states the exact coherent single-corridor predicate on the
already-stabilized packed successor grid.  The footprint includes one empty
sentinel on each side, so the two boundary rows adjacent to the owned
source-to-target corridor can be checked against the literal table.

`ExternalCutFraming` names the remaining global closure seam: edges entering
the left sentinel or leaving the right sentinel (and any aliased external
edge) must preserve the cut controls.  It is not assumed by the owned-edge
rank theorem and is not hidden inside `GridCoherent`.
-/

namespace PPLLV2ValidatorPhysicalRefinement

open PPLLV2LiteralTable
open PPLLV2ValidatorRankRepair
open PPLLParallelGeometryLift
open PPLLParallelGeometryPacked
open PPLLLinearCarrierPacking

set_option autoImplicit false
set_option warningAsError true

/-- Consecutive injective cut
`empty | source | lane^ell | target | empty`. -/
structure CorridorCut {n : Nat} (ring : DirectedRing n) (ell : Nat) where
  site : Fin (ell + 4) → Fin n
  injective : Function.Injective site
  successor : ∀ edge : Fin (ell + 3),
    site ⟨edge.val + 1, by omega⟩ =
      ring.rightNeighbor (site ⟨edge.val, by omega⟩)

def predecessorSite {n ell : Nat} {ring : DirectedRing n}
    (cut : CorridorCut ring ell) : Fin n := cut.site ⟨0, by omega⟩

def leftSite {n ell : Nat} {ring : DirectedRing n}
    (cut : CorridorCut ring ell) : Fin n := cut.site ⟨1, by omega⟩

def laneSite {n ell : Nat} {ring : DirectedRing n}
    (cut : CorridorCut ring ell) (i : Fin ell) : Fin n :=
  cut.site ⟨i.val + 2, by omega⟩

def rightSite {n ell : Nat} {ring : DirectedRing n}
    (cut : CorridorCut ring ell) : Fin n :=
  cut.site ⟨ell + 2, by omega⟩

def successorSite {n ell : Nat} {ring : DirectedRing n}
    (cut : CorridorCut ring ell) : Fin n :=
  cut.site ⟨ell + 3, by omega⟩

def ownedCutEdge {n ell : Nat} {ring : DirectedRing n}
    (cut : CorridorCut ring ell) (edge : Fin (ell + 1)) : Fin n :=
  cut.site ⟨edge.val + 1, by omega⟩

/-- Exact coherent single-corridor predicate on the actual `PackedCell`
successor grid.  The reserved `role × rootCtl` tag fixes each literal mode;
the payload bits, message, and trail remain free, as do controls outside the
cut. -/
def GridCoherent {n h ell : Nat} (hh : 0 < h) (ring : DirectedRing n)
    (cut : CorridorCut ring ell) (q : Fin n → PackedCell h)
    (physical : Corridor ell) (phase : ValidatorPhase ell) : Prop :=
  PackedPositionGrid hh ring q ∧
  CarriesLiteral (splitPacked (q (predecessorSite cut))).2
      (.cell EmptyCell) ∧
  CarriesLiteral (splitPacked (q (leftSite cut))).2
      (.root physical.left) ∧
  (∀ i, CarriesLiteral (splitPacked (q (laneSite cut i))).2
      (.cell (physical.lane i))) ∧
  CarriesLiteral (splitPacked (q (rightSite cut))).2
      (.root physical.right) ∧
  CarriesLiteral (splitPacked (q (successorSite cut))).2
      (.cell EmptyCell) ∧
  Represents physical phase

/-- Exact named global seam.  A non-cut edge must preserve every packed
control on the extended cut.  The two exterior-facing edges are included;
this does not follow from the owned corridor grammar alone. -/
def ExternalCutFraming {n h ell : Nat} (hh : 0 < h)
    (ring : DirectedRing n) (cut : CorridorCut ring ell)
    (q : Fin n → PackedCell h) : Prop :=
  ∀ edge : Fin n,
    (∀ internal : Fin (ell + 3),
      edge ≠ cut.site ⟨internal.val, by omega⟩) →
    ∀ i : Fin (ell + 4),
      (splitPacked
        (packedParallelStep hh ring (packedQmatControlRow h) q edge
          (cut.site i))).2 =
        (splitPacked (q (cut.site i))).2

/-- Adjacent corridors cannot both satisfy the active packed grammar.  Their
shared physical root would have to decode simultaneously as the first
corridor's `targetHold` and the second corridor's source shape. -/
theorem adjacent_grid_coherence_exclusive
    {n h leftLength rightLength : Nat} (hh : 0 < h)
    (ring : DirectedRing n)
    (leftCut : CorridorCut ring leftLength)
    (rightCut : CorridorCut ring rightLength)
    (q : Fin n → PackedCell h)
    (leftPhysical : Corridor leftLength)
    (rightPhysical : Corridor rightLength)
    (leftPhase : ValidatorPhase leftLength)
    (rightPhase : ValidatorPhase rightLength)
    (hshared : rightSite leftCut = leftSite rightCut)
    (hleftGrid : GridCoherent hh ring leftCut q leftPhysical leftPhase)
    (hrightGrid : GridCoherent hh ring rightCut q rightPhysical rightPhase)
    (hleftActive : leftPhase ≠ .exited)
    (hrightActive : rightPhase ≠ .exited) : False := by
  rcases hleftGrid with
    ⟨_, _, _, _, hleftTarget, _, hleftRep⟩
  rcases hrightGrid with
    ⟨_, _, hrightSource, _, _, _, hrightRep⟩
  rw [hshared] at hleftTarget
  have hmode := carriesLiteral_unique hleftTarget hrightSource
  have hroot : leftPhysical.right = rightPhysical.left :=
    PackedLiteralMode.root.inj hmode
  exact adjacent_active_corridors_exclusive hroot
    ⟨leftPhase, hleftActive, hleftRep⟩
    ⟨rightPhase, hrightActive, hrightRep⟩

/-- Literal pair selected by an owned abstract edge. -/
def ownedModePair {ell : Nat} (hell : 0 < ell) (physical : Corridor ell)
    (edge : Fin (ell + 1)) : PackedLiteralMode × PackedLiteralMode := by
  by_cases hsource : edge.val = 0
  · exact (.root physical.left, .cell (physical.lane (firstCell hell)))
  · by_cases htarget : edge.val = ell
    · exact (.cell (physical.lane (lastCell hell)), .root physical.right)
    · exact
        (.cell (physical.lane ⟨edge.val - 1, by omega⟩),
          .cell (physical.lane ⟨edge.val, by omega⟩))

/-- A coherent packed grid exposes exactly the encoded literal input pair at
every owned physical edge. -/
theorem grid_owned_controls {n h ell : Nat} (hh : 0 < h)
    (ring : DirectedRing n) (cut : CorridorCut ring ell)
    (q : Fin n → PackedCell h) (physical : Corridor ell)
    (phase : ValidatorPhase ell)
    (hgrid : GridCoherent hh ring cut q physical phase)
    (hell : 0 < ell) (edge : Fin (ell + 1)) :
    CarriesLiteral (splitPacked (q (ownedCutEdge cut edge))).2
        (ownedModePair hell physical edge).1 ∧
      CarriesLiteral
        (splitPacked (q (ring.rightNeighbor (ownedCutEdge cut edge)))).2
        (ownedModePair hell physical edge).2 := by
  rcases hgrid with ⟨_, _hpred, hleft, hlane, hright, _hsucc, _hrep⟩
  have hnext := cut.successor ⟨edge.val + 1, by omega⟩
  change cut.site ⟨edge.val + 2, by omega⟩ =
      ring.rightNeighbor (ownedCutEdge cut edge) at hnext
  rw [← hnext]
  by_cases hsource : edge.val = 0
  · have hs : ownedCutEdge cut edge = leftSite cut := by
      apply congrArg cut.site
      apply Fin.ext
      simp [hsource]
    have hn : cut.site ⟨edge.val + 2, by omega⟩ =
        laneSite cut (firstCell hell) := by
      apply congrArg cut.site
      apply Fin.ext
      simp [firstCell, hsource]
    rw [hs, hn]
    have hpair : ownedModePair hell physical edge =
        (.root physical.left, .cell (physical.lane (firstCell hell))) := by
      simp [ownedModePair, hsource]
    rw [hpair]
    exact ⟨hleft, hlane (firstCell hell)⟩
  · by_cases htarget : edge.val = ell
    · have hs : ownedCutEdge cut edge = laneSite cut (lastCell hell) := by
        apply congrArg cut.site
        apply Fin.ext
        simp [lastCell, htarget]
        omega
      have hn : cut.site ⟨edge.val + 2, by omega⟩ = rightSite cut := by
        apply congrArg cut.site
        apply Fin.ext
        simp [htarget]
      rw [hs, hn]
      have hpair : ownedModePair hell physical edge =
          (.cell (physical.lane (lastCell hell)), .root physical.right) := by
        have hellne : ell ≠ 0 := Nat.ne_of_gt hell
        simp [ownedModePair, htarget, hellne]
      rw [hpair]
      exact ⟨hlane (lastCell hell), hright⟩
    · let li : Fin ell := ⟨edge.val - 1, by omega⟩
      let ri : Fin ell := ⟨edge.val, by omega⟩
      have hs : ownedCutEdge cut edge = laneSite cut li := by
        apply congrArg cut.site
        apply Fin.ext
        simp [li]
        omega
      have hn : cut.site ⟨edge.val + 2, by omega⟩ = laneSite cut ri := by
        apply congrArg cut.site
        apply Fin.ext
        simp [ri]
      rw [hs, hn]
      have hpair : ownedModePair hell physical edge =
          (.cell (physical.lane li), .cell (physical.lane ri)) := by
        simp [ownedModePair, hsource, htarget, li, ri]
      rw [hpair]
      exact ⟨hlane li, hlane ri⟩

/-- The actual packed row at an owned grid edge is exactly the encoded
26/39/QMAT output pair. -/
theorem grid_owned_control_row {n h ell : Nat} (hh : 0 < h)
    (ring : DirectedRing n) (cut : CorridorCut ring ell)
    (q : Fin n → PackedCell h) (physical : Corridor ell)
    (phase : ValidatorPhase ell)
    (hgrid : GridCoherent hh ring cut q physical phase)
    (hell : 0 < ell) (edge : Fin (ell + 1)) :
    packedQmatControlRow h
        (splitPacked (q (ownedCutEdge cut edge)))
        (splitPacked (q (ring.rightNeighbor (ownedCutEdge cut edge)))) =
      (writeLiteral (splitPacked (q (ownedCutEdge cut edge))).2
          (packedLiteralModeStep
            (ownedModePair hell physical edge).1
            (ownedModePair hell physical edge).2).1,
        writeLiteral
          (splitPacked
            (q (ring.rightNeighbor (ownedCutEdge cut edge)))).2
          (packedLiteralModeStep
            (ownedModePair hell physical edge).1
            (ownedModePair hell physical edge).2).2) := by
  have hcontrols := grid_owned_controls hh ring cut q physical phase hgrid
    hell edge
  exact packedLiteralStep_of_carries _ _ _ _ hcontrols.1 hcontrols.2

/-! ## Checked boundary sentinel rows -/

@[simp] theorem packed_empty_stableSource_frames :
    packedLiteralModeStep (.cell EmptyCell) (.root .stableSource) =
      (.cell EmptyCell, .root .stableSource) := by
  simp [packedLiteralModeStep, repairedCellRootStep, literalCellRootStep,
    EmptyCell, headless]

@[simp] theorem packed_empty_validateSource_frames :
    packedLiteralModeStep (.cell EmptyCell) (.root .validateSource) =
      (.cell EmptyCell, .root .validateSource) := by
  simp [packedLiteralModeStep, repairedCellRootStep, literalCellRootStep,
    EmptyCell, headless]

@[simp] theorem packed_targetHold_empty_frames :
    packedLiteralModeStep (.root .targetHold) (.cell EmptyCell) =
      (.root .targetHold, .cell EmptyCell) := by
  rfl

/-- For every active grammar phase, the two cut-boundary sentinel pairs frame
under the actual packed row.  This checks the boundary-touching rows inside
the extended cut; `ExternalCutFraming` still governs edges outside it. -/
theorem active_boundary_mode_rows_frame {ell : Nat} (physical : Corridor ell)
    (phase : ValidatorPhase ell) (hrep : Represents physical phase)
    (hactive : phase ≠ .exited) :
    packedLiteralModeStep (.cell EmptyCell) (.root physical.left) =
        (.cell EmptyCell, .root physical.left) ∧
      packedLiteralModeStep (.root physical.right) (.cell EmptyCell) =
        (.root physical.right, .cell EmptyCell) := by
  cases phase with
  | anchor =>
      rcases hrep with ⟨hleft, _, hright⟩
      simp [hleft, hright]
  | query frontier =>
      rcases hrep with ⟨hleft, _, _, _, hright⟩
      simp [hleft, hright]
  | deny frontier =>
      rcases hrep with ⟨hleft, _, _, _, hright⟩
      simp [hleft, hright]
  | exited => exact False.elim (hactive rfl)

/-- Public all-length result: actual packed owned-row execution, literal
physical state update, and abstract `Next` all agree. -/
theorem grid_packed_ownedStep_refines {n h ell : Nat} (hh : 0 < h)
    (ring : DirectedRing n) (cut : CorridorCut ring ell)
    (q : Fin n → PackedCell h) (physical : Corridor ell)
    (before : ValidatorPhase ell)
    (hgrid : GridCoherent hh ring cut q physical before)
    (hactive : before ≠ .exited) (hell : 0 < ell)
    (edge : Fin (ell + 1)) :
    ∃ after : ValidatorPhase ell,
      packedOwnedStep hell (encodePackedCorridor physical) edge =
          encodePackedCorridor (ownedStep hell physical edge) ∧
        Represents (ownedStep hell physical edge) after ∧
        Next before after ∧
        packedQmatControlRow h
            (splitPacked (q (ownedCutEdge cut edge)))
            (splitPacked (q (ring.rightNeighbor (ownedCutEdge cut edge)))) =
          (writeLiteral (splitPacked (q (ownedCutEdge cut edge))).2
              (packedLiteralModeStep
                (ownedModePair hell physical edge).1
                (ownedModePair hell physical edge).2).1,
            writeLiteral
              (splitPacked
                (q (ring.rightNeighbor (ownedCutEdge cut edge)))).2
              (packedLiteralModeStep
                (ownedModePair hell physical edge).1
                (ownedModePair hell physical edge).2).2) := by
  have hrep := hgrid.2.2.2.2.2.2
  obtain ⟨after, hpacked, hafter, hnext⟩ :=
    packed_ownedStep_refines hell physical before hrep hactive edge
  exact ⟨after, hpacked, hafter, hnext,
    grid_owned_control_row hh ring cut q physical before hgrid hell edge⟩

#print axioms represents_unique
#print axioms canonicalCorridor_represents
#print axioms adjacent_active_corridors_exclusive
#print axioms adjacent_grid_coherence_exclusive
#print axioms active_ownedStep_refines
#print axioms encodeLiteral_injective
#print axioms prioritizedPackedControlRow_encoded
#print axioms packedLiteralStep_payload_framed
#print axioms runPackedQmat_staging_framed
#print axioms pure_qmat_cannot_prepare_pair
#print axioms courierStateCode_injective
#print axioms decodeCourierCode_encodeCourierControl
#print axioms grid_packed_ownedStep_refines
#print axioms packed_qmat_positions_framed

end PPLLV2ValidatorPhysicalRefinement

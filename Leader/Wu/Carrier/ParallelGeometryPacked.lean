import Leader.Wu.Carrier.ParallelGeometry
import Leader.Wu.Carrier.LinearPacking

/-!
# Parallel geometry on the actual packed carrier

This module instantiates `PPLLParallelGeometryLift` on the repository's exact
`PackedCell h`.  Splitting off `pos` is a bijective view, not a new field or a
larger state type.  An arbitrary control row may inspect both positions and all
six remaining fields, but its outputs cannot overwrite `pos`; the combined
step repairs positions in parallel and writes the returned controls.
-/

namespace PPLLParallelGeometryPacked

open PPLLResearchFormulation PPLLLinearCarrierPacking
  PPLLPeriodHColorVoter PPLLParallelGeometryLift

set_option autoImplicit false
set_option warningAsError true

/-- Exactly the non-position fields already present in `PackedCell`. -/
structure PackedControl where
  activeBit : Bool
  stagingBit : Bool
  role : PPLLPairedFivePassCarrier.Role4
  rootCtl : PPLLPairedFivePassCarrier.RootCtl32
  message : PPLLPairedFivePassCarrier.Msg32
  trail : PPLLPairedFivePassCarrier.Trail16
  deriving DecidableEq, Repr

def splitPacked {h : Nat} (q : PackedCell h) : ParallelCell h PackedControl :=
  (q.pos,
    { activeBit := q.activeBit
      stagingBit := q.stagingBit
      role := q.role
      rootCtl := q.rootCtl
      message := q.message
      trail := q.trail })

def joinPacked {h : Nat} (q : ParallelCell h PackedControl) : PackedCell h :=
  { pos := q.1
    activeBit := q.2.activeBit
    stagingBit := q.2.stagingBit
    role := q.2.role
    rootCtl := q.2.rootCtl
    message := q.2.message
    trail := q.2.trail }

@[simp] theorem joinPacked_splitPacked {h : Nat} (q : PackedCell h) :
    joinPacked (splitPacked q) = q := by
  cases q
  rfl

@[simp] theorem splitPacked_joinPacked {h : Nat}
    (q : ParallelCell h PackedControl) :
    splitPacked (joinPacked q) = q := by
  rcases q with ⟨pos, control⟩
  cases control
  rfl

@[simp] theorem joinPacked_pos {h : Nat}
    (q : ParallelCell h PackedControl) :
    (joinPacked q).pos = q.1 := rfl

theorem splitPacked_bijective (h : Nat) :
    Function.Injective (splitPacked : PackedCell h ->
      ParallelCell h PackedControl) ∧
    Function.Surjective (splitPacked : PackedCell h ->
      ParallelCell h PackedControl) := by
  constructor
  · intro q r hqr
    have h := congrArg joinPacked hqr
    simpa using h
  · intro q
    exact ⟨joinPacked q, splitPacked_joinPacked q⟩

/-- Project an actual packed configuration to its one stored position field. -/
def packedPositions {n h : Nat} (q : Fin n -> PackedCell h) :
    Fin n -> Fin h :=
  fun i => (q i).pos

/-- The control row's input still contains current endpoint positions. -/
abbrev PackedControlRow (h : Nat) := ControlRow h PackedControl

/-- Parallel position/control step on the unchanged actual carrier. -/
def packedParallelStep {n h : Nat} (hh : 0 < h)
    (ring : DirectedRing n) (control : PackedControlRow h)
    (q : Fin n -> PackedCell h) (edge : Fin n) : Fin n -> PackedCell h :=
  fun i => joinPacked
    (parallelStep hh ring control (fun j => splitPacked (q j)) edge i)

/-- The actual packed transition has exactly the standalone voter marginal. -/
theorem packedPositions_parallelStep {n h : Nat} (hh : 0 < h)
    (ring : DirectedRing n) (control : PackedControlRow h)
    (q : Fin n -> PackedCell h) (edge : Fin n) :
    packedPositions (packedParallelStep hh ring control q edge) =
      periodRepairStep hh ring (packedPositions q) edge := by
  have hproj := positions_parallelStep hh ring control
    (fun j => splitPacked (q j)) edge
  have hsplit : positions (fun j => splitPacked (q j)) = packedPositions q := by
    rfl
  rw [hsplit] at hproj
  funext i
  have hi := congrFun hproj i
  simpa [packedPositions, packedParallelStep, positions] using hi

def PackedPositionGrid {n h : Nat} (hh : 0 < h)
    (ring : DirectedRing n) (q : Fin n -> PackedCell h) : Prop :=
  SuccessorGrid hh ring (packedPositions q)

/-- The actual packed grid is closed while arbitrary controls continue. -/
theorem packedPositionGrid_step {n h : Nat} (hh : 0 < h)
    (ring : DirectedRing n) (control : PackedControlRow h)
    (q : Fin n -> PackedCell h) (hq : PackedPositionGrid hh ring q)
    (edge : Fin n) :
    PackedPositionGrid hh ring (packedParallelStep hh ring control q edge) := by
  unfold PackedPositionGrid
  rw [packedPositions_parallelStep]
  have hfixed := periodRepairStep_eq_self_of_grid
    hh ring (packedPositions q) hq edge
  rw [hfixed]
  exact hq

noncomputable def packedGridWeightedMissTotal
    {n h : Nat} (hh : 0 < h)
    (ring : DirectedRing n) (control : PackedControlRow h)
    (q : Fin n -> PackedCell h) (t : Nat) : Nat :=
  rawParallelGridWeightedMissTotal hh ring control
    (fun i => splitPacked (q i)) t

/-- Uniform-iid truncated position-grid time on the unchanged packed carrier. -/
theorem packedGrid_truncated_expectation_le_half_cube
    {n h : Nat} (hh : 0 < h) (hdvd : h ∣ n)
    (hn2 : 1 < n) (ring : DirectedRing n)
    (control : PackedControlRow h) (q : Fin n -> PackedCell h) (t : Nat) :
    2 * (n * packedGridWeightedMissTotal hh ring control q t) <=
      n ^ t * n ^ 3 := by
  exact rawParallelGrid_truncated_expectation_le_half_cube
    hh hdvd hn2 ring control (fun i => splitPacked (q i)) t

/-- The instantiated state type is literally `PackedCell`, so its exact count
is the already-checked `262144*h`; the product view adds nothing. -/
theorem packedParallelStateCount (h : Nat) :
    (packedCellStates h).values.length = 262144 * h :=
  packedCellStates_length h

#print axioms splitPacked_bijective
#print axioms packedPositions_parallelStep
#print axioms packedPositionGrid_step
#print axioms packedGrid_truncated_expectation_le_half_cube
#print axioms packedParallelStateCount

end PPLLParallelGeometryPacked

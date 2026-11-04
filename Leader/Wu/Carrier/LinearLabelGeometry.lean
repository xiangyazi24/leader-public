import Leader.Wu.Birth.LabelGeometryStabilization
import Leader.Wu.Carrier.LinearPacking

/-!
# Dynamic label geometry for the linear PPLL carrier

The static packing width divides the physical ring on the large branch.  This
module feeds that arithmetic fact into the existing stopped P-prime label
sweep.  From any leaderless raw configuration, a word of length at most
`n - 1` therefore either creates a leader or aligns the single `Fin width`
field into a cyclic successor grid.  In the aligned branch, the number of
width-sized blocks still has the required `leastNonDivisor n` obstruction.

This is the dynamic position-grid bridge only.  It does not construct the
active/staging snapshot writer.
-/

namespace PPLLLinearCarrierGeometry

open AAFJExactN
open PPLL PPLLResearchFormulation PPLLWallSweepRepair
  PPLLPpsiLeaderCreationSchedule
  PPLLNoCheckBirthConditionTwoGeometry
  PPLLWriteSeqPersistenceRegression PPLLWriteSeqRelocation
open PPLLLinearCarrierPacking PPLLPpsiLabelGeometry

set_option autoImplicit false
set_option warningAsError true

/-- The one modular field used by the packed position grid. -/
def packedWidth (n : Nat) : Nat := width (leastNonDivisor n)

theorem packedWidth_pos (n : Nat) : 0 < packedWidth n := by
  exact width_pos _

theorem packedWidth_dvd {n : Nat} (hn : 0 < n)
    (hk : 8 <= leastNonDivisor n) : packedWidth n ∣ n := by
  exact width_leastNonDivisor_dvd hn hk

/-! ## Constant-factor separated geometry controls -/

/-- A composition-safe alternative to reusing transaction controls.  The
three Boolean fields store the P-prime geometry leader, probe, and phase while
the packed payload/transaction cell is framed.  There is still only one
`Fin h`, namely `PackedCell.pos`. -/
abbrev GeometryFramedPackedCell (h : Nat) :=
  ((PackedCell h × Bool) × Bool) × Bool

/-- Constructive exhaustive list for the composition-safe carrier. -/
def geometryFramedPackedCellStates (h : Nat) :
    ExhaustiveList (GeometryFramedPackedCell h) :=
  ExhaustiveList.prod
    (ExhaustiveList.prod
      (ExhaustiveList.prod (packedCellStates h) ExhaustiveList.bool)
      ExhaustiveList.bool)
    ExhaustiveList.bool

theorem geometryFramedPackedCellStates_nodup (h : Nat) :
    (geometryFramedPackedCellStates h).values.Nodup := by
  unfold geometryFramedPackedCellStates
  exact ExhaustiveList.values_nodup_prod _ _
    (ExhaustiveList.values_nodup_prod _ _
      (ExhaustiveList.values_nodup_prod _ _
        (packedCellStates_nodup h) ExhaustiveList.values_nodup_bool)
      ExhaustiveList.values_nodup_bool)
    ExhaustiveList.values_nodup_bool

/-- Separating all three geometry bits costs exactly a factor eight. -/
theorem geometryFramedPackedCellStates_length (h : Nat) :
    (geometryFramedPackedCellStates h).values.length = 2097152 * h := by
  simp [geometryFramedPackedCellStates,
    ExhaustiveList.values_length_prod,
    ExhaustiveList.values_length_bool,
    packedCellStates_length]
  omega

def geometryFramedLargeBranchStateCount (n : Nat) : Nat :=
  2097152 * width (leastNonDivisor n)

theorem geometryFramedLargeBranchStateCount_le_loglog
    {n : Nat} (hn : 0 < n) :
    geometryFramedLargeBranchStateCount n <=
      2097152 * (4 + (Nat.log2 (Nat.log2 n + 1) + 1)) := by
  exact Nat.mul_le_mul_left 2097152
    (width_leastNonDivisor_le_explicitHeightBound hn)

/-- Rooted stopped formation of the packed position grid.  The disjunction is
operational: an early P-prime barrier birth is already a leader-producing
outcome; otherwise the one `Fin packedWidth` field is aligned around the whole
cycle and the quotient block count retains the source nondivisor condition. -/
theorem exists_stopped_packed_grid_or_leader_from_root
    {n : Nat} (ring : DirectedRing n) (hn : 1 < n)
    (hk : 8 <= leastNonDivisor n) (root : Fin n)
    (C : Fin n -> AgentState (packedWidth n))
    (hleaderless : RawLeaderless C) :
    ∃ (word : DetSchedule n) (D : Fin n -> AgentState (packedWidth n)),
      word.length <= n - 1 ∧
      D = runLocalSchedule ring (pPsi (packedWidth_pos n)) C word ∧
      (RawHasLeader D ∨
        (AllSuccessorLabels (packedWidth_pos n) ring D ∧
          ¬ leastNonDivisor n ∣ blockCount n)) := by
  have hnpos : 0 < n := by omega
  obtain ⟨word, D, hlength, hD, hout⟩ :=
    exists_stopped_labelSweep_or_leader_from_root
      (packedWidth_pos n) ring hn (packedWidth_dvd hnpos hk)
      root C hleaderless
  refine ⟨word, D, hlength, hD, ?_⟩
  rcases hout with hleader | haligned
  · exact Or.inl hleader
  · exact Or.inr ⟨haligned,
      leastNonDivisor_not_dvd_blockCount hnpos hk⟩

/-- Unrooted presentation of the same dynamic position-grid bridge. -/
theorem exists_stopped_packed_grid_or_leader
    {n : Nat} (ring : DirectedRing n) (hn : 1 < n)
    (hk : 8 <= leastNonDivisor n)
    (C : Fin n -> AgentState (packedWidth n))
    (hleaderless : RawLeaderless C) :
    ∃ (word : DetSchedule n) (D : Fin n -> AgentState (packedWidth n)),
      D = runLocalSchedule ring (pPsi (packedWidth_pos n)) C word ∧
      (RawHasLeader D ∨
        (AllSuccessorLabels (packedWidth_pos n) ring D ∧
          ¬ leastNonDivisor n ∣ blockCount n)) := by
  let root : Fin n := ⟨0, by omega⟩
  obtain ⟨word, D, _hlength, hD, hout⟩ :=
    exists_stopped_packed_grid_or_leader_from_root
      ring hn hk root C hleaderless
  exact ⟨word, D, hD, hout⟩

end PPLLLinearCarrierGeometry

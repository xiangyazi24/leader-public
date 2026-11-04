import Leader.Wu.WriteSeq.PersistenceRepair
import Leader.Wu.Safety.NoCheckBirthConditionFiveRegression
import Leader.Wu.Safety.SignalCoherence
import Leader.Wu.Scheduler.TraversalMetric

/-!
# Regressions for the Algorithm-16 persistence repair

These finite computations pin the exact scope of the repaired line-8 semantics.
An aligned input `equal` survives at the initiator, advances through the
terminal responder, and creates a same-interaction `increment_group` that
Algorithm 19 consumes.  Clearing input increment actions blocks the exact local pair
behind the condition-5 regression without blocking that same-call generation.
The tests also expose the remaining limits: an arbitrary input
`write_state=increment_group` reopens the same bit flip, a freshly computed
label-zero equality departs before a later interaction can use it, path transfer
remains dead under the persistence-only transition, and the condition-4
`move_flip` witness remains live.  The guarded lifecycle variant then supplies
the missing positive control: both an inside-group departure and a
terminal-wrap departure move through Algorithm 20, while same-call increment
generation still executes.
-/

namespace PPLLWriteSeqPersistenceRegression

open PPLL PPLLWriteIncrementGate PPLLWriteSeqPersistenceRepair
  PPLLNoCheckBirthConditionFourRegression
  PPLLNoCheckBirthConditionFiveRegression
  PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoProtocol

/-- An arbitrarily supplied aligned equality at label zero and an idle terminal
component. Neither endpoint starts with a write command; no reachability claim
is made for the input equality. -/
def persistentEqualLeft : AgentState 2 :=
  { conditionFiveCoreConfig 2 with path3 := some ⟨0, 0, 0⟩, write_state := .equal, write := .none }

def persistentEqualRight : AgentState 2 :=
  { conditionFiveCoreConfig 3 with path3 := some ⟨1, 0, 0⟩, write_state := .none, write := .none }

/-- The formerly dead second comparison reaches terminal equality and lines
24--28 generate an increment from command-free inputs. -/
theorem persistent_prepare_reaches_terminal_increment :
    let q := writeSeqPreparePersistent hTwo
      persistentEqualLeft persistentEqualRight
    q.1.write_state = .equal ∧
      q.2.write_state = .equal ∧
      q.2.write = .increment_group ∧
      persistentEqualLeft.write = .none ∧
      persistentEqualRight.write = .none := by
  decide

/-- The newly generated terminal increment is accepted and consumed in the
same interaction, changing the terminal zero bit to one. -/
theorem persistent_gate_preserves_same_call_increment :
    (writeSeqPersistentIncrementGate hTwo
      persistentEqualLeft persistentEqualRight).2.bit = true ∧
    (writeSeqPersistentIncrementGate hTwo
      persistentEqualLeft persistentEqualRight).2.write = .none := by
  decide

/-- The old prepared gate executes the locally supported arbitrary increment
from the condition-5 pair, while entry sanitization in the persistent repair
blocks it. -/
theorem persistent_entry_sanitizer_blocks_conditionFive_pair :
    (writeSeqIncrementGate hTwo
      (conditionFiveCoreConfig 2) (conditionFiveCoreConfig 3)).2.bit = true ∧
    (writeSeqPersistentIncrementGate hTwo
      (conditionFiveCoreConfig 2) (conditionFiveCoreConfig 3)).2.bit = false := by
  decide

/-- A `write_state` forgery bypasses action-field sanitization. The literal
ready reset erased this state, but persistence lets it execute the same stable-ID
bit flip one field over from R36. -/
def persistentStateForgeryLeft : AgentState 2 :=
  conditionFiveCoreConfig 1

def persistentStateForgeryRight : AgentState 2 :=
  { conditionFiveCoreConfig 2 with path3 := some ⟨0, 0, 0⟩, write_state := .increment_group, write := .none }

theorem persistent_state_forgery_reopens_conditionFive_pair :
    (writeSeqIncrementGate hTwo
      persistentStateForgeryLeft persistentStateForgeryRight).2.bit = false ∧
    (writeSeqPersistentIncrementGate hTwo
      persistentStateForgeryLeft persistentStateForgeryRight).2.bit = true := by
  decide

/-- The repaired preparation can compute equality at a label-zero responder,
but the same full WRITE_SEQ call changes that state to `depart`. Thus the test
fixture above does not yet arise from the repaired lifecycle. -/
def persistentSeedLeft : AgentState 2 :=
  { conditionFiveCoreConfig 1 with path3 := some ⟨1, 0, 0⟩, write_state := .none, write := .none }

def persistentSeedRight : AgentState 2 :=
  { conditionFiveCoreConfig 2 with path3 := some ⟨0, 0, 0⟩, write_state := .none, write := .none }

theorem persistent_labelZero_equal_departs_same_call :
    (writeSeqPreparePersistent hTwo
      persistentSeedLeft persistentSeedRight).2.write_state = .equal ∧
    (writeSeqPersistentIncrementGate hTwo
      persistentSeedLeft persistentSeedRight).2.write_state = .depart := by
  decide

/-- Preserving an aligned input `depart` is insufficient to revive Algorithm
20 path transfer: Algorithm 19 overwrites it before MOVE_WSIG inspects it. -/
def persistentTransferLeft : AgentState 2 :=
  { conditionFiveCoreConfig 2 with path3 := some ⟨0, 0, 1⟩, write_state := .depart, write := .none }

def persistentTransferRight : AgentState 2 :=
  { conditionFiveCoreConfig 3 with path3 := none, write_state := .none, write := .none }

theorem persistent_depart_path_still_does_not_transfer :
    (writeSeqPersistentIncrementGate hTwo
      persistentTransferLeft persistentTransferRight).1.path3 =
        some ⟨0, 0, 1⟩ ∧
    (writeSeqPersistentIncrementGate hTwo
      persistentTransferLeft persistentTransferRight).2.path3 = none := by
  decide

/-! ## Positive Algorithm-19/20 handoff under the guarded lifecycle -/

/-- Guarding idle overwrites lets the existing Algorithm-20 transfer move an
inside-group path component into its empty successor. -/
theorem persistentLifecycle_inside_group_path_transfer :
    let q := writeSeqPersistentLifecycle hTwo
      persistentTransferLeft persistentTransferRight
    q.1.path3 = none ∧
      q.1.write_state = .none ∧
      q.2.path3 = some ⟨0, 0, 1⟩ ∧
      q.2.write_state = .depart := by
  decide

/-- A terminal departure with no pending command must cross the wrap instead
of being activated as the idle image of `.none`. -/
def persistentTerminalTransferLeft : AgentState 2 :=
  { persistentTransferLeft with
    label := ⟨1, by omega⟩
    path3 := some ⟨1, 0, 1⟩
    write_state := .depart
    write := .none }

def persistentWrapTransferRight : AgentState 2 :=
  { persistentTransferRight with label := ⟨0, by omega⟩ }

/-- The same guarded lifecycle restores terminal-to-zero path movement. -/
theorem persistentLifecycle_terminal_wrap_path_transfer :
    let q := writeSeqPersistentLifecycle hTwo
      persistentTerminalTransferLeft persistentWrapTransferRight
    q.1.path3 = none ∧
      q.1.write_state = .none ∧
      q.2.path3 = some ⟨1, 0, 1⟩ ∧
      q.2.write_state = .depart := by
  decide

/-! ## Complete stop-on-alignment transport -/

/-- The first stable edge moves an aligned label-zero component to the
label-one host.  Its transport rank falls from two to one. -/
def persistentTransportAfterOne : AgentState 2 × AgentState 2 :=
  writeSeqPersistentComparisonTransportLifecycle hTwo
    persistentTransferLeft persistentTransferRight

/-- The wrap edge reaches the next label-zero host and retires `depart`; the
component is now aligned in the next group and has transport rank zero. -/
def persistentTransportAfterTwo : AgentState 2 × AgentState 2 :=
  writeSeqPersistentComparisonTransportLifecycle hTwo
    persistentTransportAfterOne.2 persistentWrapTransferRight

/-- **Positive one-group transport.**  A physical writer component crosses
exactly `ψ=2` stable edges, preserves its payload label, payload bit, and flag,
and stops aligned in the next group.  The explicit rank values are `2,1,0`.
This is the finite regression counterpart of
`moveWsigTransferStopAligned_phase`. -/
theorem persistentTransport_two_edges_stops_aligned :
    writerTransportPhase persistentTransferLeft = 2 ∧
      persistentTransportAfterOne.1.path3 = none ∧
      persistentTransportAfterOne.2.label = ⟨1, by omega⟩ ∧
      persistentTransportAfterOne.2.path3 = some ⟨0, 0, 1⟩ ∧
      persistentTransportAfterOne.2.write_state = .depart ∧
      writerTransportPhase persistentTransportAfterOne.2 = 1 ∧
      persistentTransportAfterTwo.1.path3 = none ∧
      persistentTransportAfterTwo.2.label = ⟨0, by omega⟩ ∧
      persistentTransportAfterTwo.2.path3 = some ⟨0, 0, 1⟩ ∧
      persistentTransportAfterTwo.2.write_state = .none ∧
      writerTransportPhase persistentTransportAfterTwo.2 = 0 := by
  decide

/-! ## Complete two-component group crossing -/

/-- One right-to-left sweep over a width-`width` writer block.  At round
`round`, the leading edge has advanced by `round`; reversing the range visits
the occupied cells from right to left so each responder slot is empty. -/
def writerBlockSweepSchedule {n : Nat} (ring : DirectedRing n)
    (start : Fin n) (width round : Nat) : DetSchedule n :=
  (List.range width).reverse.map fun k =>
    ⟨(start.val + round + k) % n, Nat.mod_lt _ ring.hn⟩

/-- `width` right-to-left sweeps, the canonical schedule for translating a
width-`width` writer block by one whole group. -/
def writerBlockTransportSchedule {n : Nat} (ring : DirectedRing n)
    (start : Fin n) (width : Nat) : DetSchedule n :=
  (List.range width).flatMap fun round =>
    writerBlockSweepSchedule ring start width round

theorem writerBlockSweepSchedule_length {n : Nat} (ring : DirectedRing n)
    (start : Fin n) (width round : Nat) :
    (writerBlockSweepSchedule ring start width round).length = width := by
  simp [writerBlockSweepSchedule]

/-- The canonical full-block transport schedule has exactly `width²` local
interactions. -/
theorem writerBlockTransportSchedule_length {n : Nat}
    (ring : DirectedRing n) (start : Fin n) (width : Nat) :
    (writerBlockTransportSchedule ring start width).length = width * width := by
  simp only [writerBlockTransportSchedule, List.length_flatMap,
    writerBlockSweepSchedule, List.length_map, List.length_reverse,
    List.length_range]
  have hsum : ∀ xs : List Nat,
      (xs.map fun _ => width).sum = xs.length * width := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih => simp [ih, Nat.add_mul, Nat.add_comm]
  rw [hsum, List.length_range]

/-- Recursive descending-prefix form of one sweep, exposed for the eventual
configuration induction. -/
def writerDescendingPrefixSchedule {n : Nat} (ring : DirectedRing n)
    (start : Fin n) (round : Nat) : Nat → DetSchedule n
  | 0 => []
  | count + 1 =>
      ⟨(start.val + round + count) % n, Nat.mod_lt _ ring.hn⟩ ::
        writerDescendingPrefixSchedule ring start round count

theorem writerBlockSweepSchedule_eq_descending {n : Nat}
    (ring : DirectedRing n) (start : Fin n) (width round : Nat) :
    writerBlockSweepSchedule ring start width round =
      writerDescendingPrefixSchedule ring start round width := by
  induction width with
  | zero => rfl
  | succ width ih =>
      unfold writerBlockSweepSchedule at ih ⊢
      simp [writerDescendingPrefixSchedule, List.range_succ, ih]

/-- Recursive completed-round form of the arbitrary-width block schedule. -/
def writerBlockTransportRounds {n : Nat} (ring : DirectedRing n)
    (start : Fin n) (width : Nat) : Nat → DetSchedule n
  | 0 => []
  | rounds + 1 =>
      writerBlockTransportRounds ring start width rounds ++
        writerDescendingPrefixSchedule ring start rounds width

theorem writerBlockTransportRounds_eq_flatMap {n : Nat}
    (ring : DirectedRing n) (start : Fin n) (width rounds : Nat) :
    writerBlockTransportRounds ring start width rounds =
      (List.range rounds).flatMap fun round =>
        writerBlockSweepSchedule ring start width round := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      rw [writerBlockTransportRounds, ih, List.range_succ,
        List.flatMap_append]
      simp [writerBlockSweepSchedule_eq_descending]

/-- The public canonical schedule is exactly the recursive schedule after all
`width` rounds. -/
theorem writerBlockTransportSchedule_eq_rounds {n : Nat}
    (ring : DirectedRing n) (start : Fin n) (width : Nat) :
    writerBlockTransportSchedule ring start width =
      writerBlockTransportRounds ring start width width := by
  rw [writerBlockTransportRounds_eq_flatMap]
  rfl

/-- The clean one-edge lifecycle lifts from its two local endpoints to the
whole ring configuration.  This is the configuration-level induction step
used by the descending sweep: the vacated source and the arriving responder
both remain clean writer frames. -/
theorem stepConfig_writer_clean_sweep_edge {ψ n : Nat} (hψ : ψ > 0)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → AgentState ψ) (e : Fin n) (p3 : Path3Info)
    (hlpath : (C e).path3 = some p3)
    (hrpath : (C (ring.rightNeighbor e)).path3 = none)
    (hdepart : (C e).write_state = .depart)
    (hlclean : WriterTransportCleanFrame (C e))
    (hrclean : WriterTransportCleanFrame (C (ring.rightNeighbor e))) :
    let D := stepConfig ring
      (writeSeqPersistentComparisonTransportLifecycle hψ) C e
    (D e).path3 = none ∧ (D e).write_state = .none ∧
      (D e).label = (C e).label ∧ (D e).bit = (C e).bit ∧
      WriterTransportCleanFrame (D e) ∧
      (D (ring.rightNeighbor e)).path3 = some p3 ∧
      (D (ring.rightNeighbor e)).label =
        (C (ring.rightNeighbor e)).label ∧
      (D (ring.rightNeighbor e)).bit =
        (C (ring.rightNeighbor e)).bit ∧
      (D (ring.rightNeighbor e)).write_state =
        (if (C (ring.rightNeighbor e)).label.val = p3.label
          then .none else .depart) ∧
      WriterTransportCleanFrame (D (ring.rightNeighbor e)) := by
  have hlocal := writeSeqPersistentComparisonTransportLifecycle_clean_sweep_edge
    hψ (C e) (C (ring.rightNeighbor e)) p3 hlpath hrpath hdepart
    hlclean hrclean
  have hne : ring.rightNeighbor e ≠ e :=
    rightNeighbor_ne_self_of_one_lt ring hn e
  have hleft :
      stepConfig ring (writeSeqPersistentComparisonTransportLifecycle hψ) C e e =
        (writeSeqPersistentComparisonTransportLifecycle hψ
          (C e) (C (ring.rightNeighbor e))).1 := by
    simp [stepConfig]
  have hright :
      stepConfig ring (writeSeqPersistentComparisonTransportLifecycle hψ) C e
          (ring.rightNeighbor e) =
        (writeSeqPersistentComparisonTransportLifecycle hψ
          (C e) (C (ring.rightNeighbor e))).2 := by
    simp [stepConfig, hne]
  rcases hlocal with ⟨hsourcePath, hsourceState, hsourceLabel,
    hsourceBit, hsourceClean, htargetPath, htargetLabel, htargetBit,
    htargetState, htargetClean⟩
  dsimp only
  rw [hleft, hright]
  exact ⟨hsourcePath, hsourceState, hsourceLabel, hsourceBit,
    hsourceClean, htargetPath, htargetLabel, htargetBit,
    htargetState, htargetClean⟩

/-! ## Arbitrary-width writer transport -/

/-- A component arriving during round `round` is aligned exactly in the
final sweep. -/
theorem writer_arrival_aligned_iff {ψ round k : Nat}
    (_hψ : 0 < ψ) (hround : round < ψ) (hk : k < ψ) :
    (round + k + 1) % ψ = k ↔ round + 1 = ψ := by
  constructor
  · intro halign
    have hcases : round + 1 = ψ ∨ round + 1 < ψ := by omega
    rcases hcases with hfinal | hstep
    · exact hfinal
    · have hshape : round + k + 1 = (round + 1) + k := by omega
      rw [hshape] at halign
      by_cases hsum : round + 1 + k < ψ
      · rw [Nat.mod_eq_of_lt hsum] at halign
        omega
      · have hge : ψ ≤ round + 1 + k := by omega
        rw [Nat.mod_eq_sub_mod hge,
          Nat.mod_eq_of_lt (by omega : round + 1 + k - ψ < ψ)] at halign
        omega
  · intro hfinal
    have hshape : round + k + 1 = ψ + k := by omega
    simp [hshape, Nat.add_mod_left, Nat.mod_eq_of_lt hk]

theorem rightNeighbor_groupOffset {n : Nat} (ring : DirectedRing n)
    (start : Fin n) (k : Nat) :
    ring.rightNeighbor (groupOffset ring start k) =
      groupOffset ring start (k + 1) := by
  apply Fin.ext
  simp only [DirectedRing.rightNeighbor, groupOffset]
  rw [Nat.mod_add_mod]
  congr 1

theorem groupOffset_compose {n : Nat} (ring : DirectedRing n)
    (start : Fin n) (x k : Nat) :
    groupOffset ring (groupOffset ring start x) k =
      groupOffset ring start (x + k) := by
  apply Fin.ext
  simp only [groupOffset]
  rw [Nat.mod_add_mod]
  congr 1
  omega

theorem groupOffset_zero_ne_of_lt {n a b : Nat} (hn : 0 < n)
    (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    groupOffset (⟨hn⟩ : DirectedRing n) (⟨0, hn⟩ : Fin n) a ≠
      groupOffset (⟨hn⟩ : DirectedRing n) (⟨0, hn⟩ : Fin n) b := by
  intro h
  have hv := congrArg Fin.val h
  simp [groupOffset, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
  exact hab hv

theorem writerDescendingPrefixSchedule_head {n : Nat}
    (ring : DirectedRing n) (start : Fin n) (round count : Nat) :
    writerDescendingPrefixSchedule ring start round (count + 1) =
      groupOffset ring start (round + count) ::
        writerDescendingPrefixSchedule ring start round count := by
  simp only [writerDescendingPrefixSchedule]
  congr 2
  congr 1
  omega

set_option linter.defProp false in
  def genericWriterRing (hψ : 0 < ψ) : DirectedRing (2 * ψ) :=
    ⟨by omega⟩

def genericWriterStart (hψ : 0 < ψ) : Fin (2 * ψ) :=
  ⟨0, by omega⟩

def genericWriterPos (hψ : 0 < ψ) (x : Nat) : Fin (2 * ψ) :=
  groupOffset (genericWriterRing hψ) (genericWriterStart hψ) x

theorem genericWriterPos_ne_of_lt {ψ a b : Nat} (hψ : 0 < ψ)
    (ha : a < 2 * ψ) (hb : b < 2 * ψ) (hab : a ≠ b) :
    genericWriterPos hψ a ≠ genericWriterPos hψ b := by
  unfold genericWriterPos genericWriterRing genericWriterStart
  exact groupOffset_zero_ne_of_lt (by omega) ha hb hab

theorem rightNeighbor_genericWriterPos {ψ x : Nat} (hψ : 0 < ψ) :
    (genericWriterRing hψ).rightNeighbor (genericWriterPos hψ x) =
      genericWriterPos hψ (x + 1) := by
  exact rightNeighbor_groupOffset
    (genericWriterRing hψ) (genericWriterStart hψ) x

def WriterLabelFrame (hψ : 0 < ψ)
    (C : Fin (2 * ψ) → AgentState ψ) : Prop :=
  ∀ x, x < 2 * ψ → (C (genericWriterPos hψ x)).label.val = x % ψ

def WriterBitFrame (reference C : Fin n → AgentState ψ) : Prop :=
  ∀ i, (C i).bit = (reference i).bit

def WriterTokenAt (C : Fin n → AgentState ψ) (i : Fin n)
    (p3 : Path3Info) (state : WriteState) : Prop :=
  (C i).path3 = some p3 ∧ (C i).write_state = state

/-- After `round` complete sweeps, all `ψ` payloads occupy the translated
block; the prefix and unused tail are empty. -/
def WriterRoundState (hψ : 0 < ψ) (C : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (round : Nat) : Prop :=
  round ≤ ψ ∧
    (∀ k, k < ψ →
      WriterTokenAt C (genericWriterPos hψ (round + k)) (payload k)
        (if round = ψ then .none else .depart)) ∧
    (∀ x, x < round → (C (genericWriterPos hψ x)).path3 = none) ∧
    (∀ x, round + ψ ≤ x → x < 2 * ψ →
      (C (genericWriterPos hψ x)).path3 = none)

/-- Inner descending-sweep invariant. `count` components remain on their
old cells, the others have moved once, and `round + count` is the unique
hole inside the active block. -/
def WriterSweepState (hψ : 0 < ψ) (C : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (round count : Nat) : Prop :=
  round < ψ ∧ count ≤ ψ ∧
    (∀ k, k < count →
      WriterTokenAt C (genericWriterPos hψ (round + k))
        (payload k) .depart) ∧
    (∀ k, count ≤ k → k < ψ →
      WriterTokenAt C (genericWriterPos hψ (round + k + 1))
        (payload k) (if round + 1 = ψ then .none else .depart)) ∧
    (C (genericWriterPos hψ (round + count))).path3 = none ∧
    (∀ x, x < round → (C (genericWriterPos hψ x)).path3 = none) ∧
    (∀ x, round + ψ < x → x < 2 * ψ →
      (C (genericWriterPos hψ x)).path3 = none)

theorem WriterRoundState.toSweep {ψ : Nat} (hψ : 0 < ψ)
    (C : Fin (2 * ψ) → AgentState ψ) (payload : Nat → Path3Info)
    (round : Nat) (hround : round < ψ)
    (h : WriterRoundState hψ C payload round) :
    WriterSweepState hψ C payload round ψ := by
  rcases h with ⟨_, htokens, hprefix, htail⟩
  refine ⟨hround, Nat.le_refl _, ?_, ?_, ?_, hprefix, ?_⟩
  · intro k hk
    have hne : round ≠ ψ := by omega
    simpa [WriterTokenAt, hne] using htokens k hk
  · intro k hk hlt
    omega
  · exact htail (round + ψ) (Nat.le_refl _) (by omega)
  · intro x hx hlt
    exact htail x (by omega) hlt

theorem WriterSweepState.zero_toRound {ψ : Nat} (hψ : 0 < ψ)
    (C : Fin (2 * ψ) → AgentState ψ) (payload : Nat → Path3Info)
    (round : Nat) (h : WriterSweepState hψ C payload round 0) :
    WriterRoundState hψ C payload (round + 1) := by
  rcases h with ⟨hround, _, _, htokens, hhole, hprefix, htail⟩
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro k hk
    have hpos : round + k + 1 = round + 1 + k := by omega
    rw [← hpos]
    exact htokens k (by omega) hk
  · intro x hx
    by_cases hxr : x < round
    · exact hprefix x hxr
    · have hxround : x = round := by omega
      subst x
      simpa using hhole
  · intro x hx hlt
    exact htail x (by omega) hlt

theorem stepConfig_eq_of_ne {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (C : Fin n → AgentState ψ) (e i : Fin n)
    (hleft : i ≠ e) (hright : i ≠ ring.rightNeighbor e) :
    stepConfig ring T C e i = C i := by
  simp [stepConfig, hleft, hright]

/-- Any local writer contract that preserves clean frames, labels, and physical
bits at both endpoints lifts to the same three frames on the whole ring.  This
is independent of whether the interaction transports, compares, or executes a
backward action. -/
theorem stepConfig_global_writer_frames_of_endpoint_contract {ψ n : Nat}
    (ring : DirectedRing n) (hn : 1 < n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hleftClean : WriterTransportCleanFrame
      (T (C e) (C (ring.rightNeighbor e))).1)
    (hrightClean : WriterTransportCleanFrame
      (T (C e) (C (ring.rightNeighbor e))).2)
    (hleftLabel : (T (C e) (C (ring.rightNeighbor e))).1.label =
      (C e).label)
    (hrightLabel : (T (C e) (C (ring.rightNeighbor e))).2.label =
      (C (ring.rightNeighbor e)).label)
    (hleftBit : (T (C e) (C (ring.rightNeighbor e))).1.bit =
      (C e).bit)
    (hrightBit : (T (C e) (C (ring.rightNeighbor e))).2.bit =
      (C (ring.rightNeighbor e)).bit) :
    let D := stepConfig ring T C e
    (∀ i, WriterTransportCleanFrame (D i)) ∧
      ∀ i, (D i).label = (C i).label ∧ (D i).bit = (C i).bit := by
  have hne : ring.rightNeighbor e ≠ e :=
    rightNeighbor_ne_self_of_one_lt ring hn e
  dsimp only
  constructor
  · intro i
    by_cases hi : i = e
    · subst i
      simpa [stepConfig] using hleftClean
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        simpa [stepConfig, hne] using hrightClean
      · rw [stepConfig_eq_of_ne ring T C e i hi hj]
        exact hclean i
  · intro i
    by_cases hi : i = e
    · subst i
      simpa [stepConfig] using And.intro hleftLabel hleftBit
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        simpa [stepConfig, hne] using And.intro hrightLabel hrightBit
      · simp [stepConfig, hi, hj]

/-- A local action that may change a physical bit still lifts clean-frame and
label preservation to the whole ring.  This is the global frame interface used
by the binary-increment branch, whose responder bit is intentionally toggled. -/
theorem stepConfig_global_writer_clean_label_of_endpoint_contract {ψ n : Nat}
    (ring : DirectedRing n) (hn : 1 < n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hleftClean : WriterTransportCleanFrame
      (T (C e) (C (ring.rightNeighbor e))).1)
    (hrightClean : WriterTransportCleanFrame
      (T (C e) (C (ring.rightNeighbor e))).2)
    (hleftLabel : (T (C e) (C (ring.rightNeighbor e))).1.label =
      (C e).label)
    (hrightLabel : (T (C e) (C (ring.rightNeighbor e))).2.label =
      (C (ring.rightNeighbor e)).label) :
    let D := stepConfig ring T C e
    (∀ i, WriterTransportCleanFrame (D i)) ∧
      ∀ i, (D i).label = (C i).label := by
  have hne : ring.rightNeighbor e ≠ e :=
    rightNeighbor_ne_self_of_one_lt ring hn e
  dsimp only
  constructor
  · intro i
    by_cases hi : i = e
    · subst i
      simpa [stepConfig] using hleftClean
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        simpa [stepConfig, hne] using hrightClean
      · rw [stepConfig_eq_of_ne ring T C e i hi hj]
        exact hclean i
  · intro i
    by_cases hi : i = e
    · subst i
      simpa [stepConfig] using hleftLabel
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        simpa [stepConfig, hne] using hrightLabel
      · simp [stepConfig, hi, hj]

theorem stepConfig_writer_global_frames {ψ n : Nat} (hψ : ψ > 0)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → AgentState ψ) (e : Fin n) (p3 : Path3Info)
    (hlpath : (C e).path3 = some p3)
    (hrpath : (C (ring.rightNeighbor e)).path3 = none)
    (hdepart : (C e).write_state = .depart)
    (hclean : ∀ i, WriterTransportCleanFrame (C i)) :
    let D := stepConfig ring
      (writeSeqPersistentComparisonTransportLifecycle hψ) C e
    (∀ i, WriterTransportCleanFrame (D i)) ∧
      ∀ i, (D i).label = (C i).label ∧ (D i).bit = (C i).bit := by
  have hedge := stepConfig_writer_clean_sweep_edge hψ ring hn C e p3
    hlpath hrpath hdepart (hclean e) (hclean (ring.rightNeighbor e))
  rcases hedge with ⟨_, _, hsourceLabel, hsourceBit, hsourceClean,
    _, htargetLabel, htargetBit, _, htargetClean⟩
  dsimp only
  constructor
  · intro i
    by_cases hi : i = e
    · subst i
      exact hsourceClean
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        exact htargetClean
      · rw [stepConfig_eq_of_ne ring
          (writeSeqPersistentComparisonTransportLifecycle hψ) C e i hi hj]
        exact hclean i
  · intro i
    by_cases hi : i = e
    · subst i
      simpa [stepConfig] using And.intro hsourceLabel hsourceBit
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        have hne := rightNeighbor_ne_self_of_one_lt ring hn e
        simpa [stepConfig, hne] using And.intro htargetLabel htargetBit
      · simp [stepConfig, hi, hj]

/-- One actual repaired lifecycle interaction decreases the inner sweep
count while preserving global clean, label, and physical-bit frames. -/
theorem WriterSweepState.step {ψ : Nat} (hψ : 0 < ψ)
    (C : Fin (2 * ψ) → AgentState ψ) (payload : Nat → Path3Info)
    (reference : Fin (2 * ψ) → AgentState ψ) (round count : Nat)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hsweep : WriterSweepState hψ C payload round (count + 1))
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame hψ C)
    (hbit : WriterBitFrame reference C) :
    let D := stepConfig (genericWriterRing hψ)
      (writeSeqPersistentComparisonTransportLifecycle hψ) C
      (genericWriterPos hψ (round + count))
    WriterSweepState hψ D payload round count ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame hψ D ∧ WriterBitFrame reference D := by
  rcases hsweep with ⟨hround, hcount, hunprocessed, hprocessed,
    hhole, hprefix, htail⟩
  have hcountLt : count < ψ := by omega
  let ring := genericWriterRing hψ
  let e := genericWriterPos hψ (round + count)
  let j := genericWriterPos hψ (round + count + 1)
  let T := writeSeqPersistentComparisonTransportLifecycle hψ
  let D := stepConfig (genericWriterRing hψ)
    (writeSeqPersistentComparisonTransportLifecycle hψ) C
    (genericWriterPos hψ (round + count))
  have hj : ring.rightNeighbor e = j := by
    dsimp only [ring, e, j]
    rw [rightNeighbor_genericWriterPos]
  have hsource := hunprocessed count (by omega)
  have hsourcePath : (C e).path3 = some (payload count) := by
    simpa [e, WriterTokenAt] using hsource.1
  have hsourceState : (C e).write_state = .depart := by
    simpa [e, WriterTokenAt] using hsource.2
  have htargetPath : (C (ring.rightNeighbor e)).path3 = none := by
    rw [hj]
    have hpos : round + (count + 1) = round + count + 1 := by omega
    simpa [j, hpos] using hhole
  have hedge := stepConfig_writer_clean_sweep_edge hψ ring (by omega)
    C e (payload count) hsourcePath htargetPath hsourceState
    (hclean e) (hclean (ring.rightNeighbor e))
  rcases hedge with ⟨hsourcePathAfter, _, hsourceLabelAfter,
    hsourceBitAfter, hsourceCleanAfter, htargetPathAfter,
    htargetLabelAfter, htargetBitAfter, htargetStateAfter,
    htargetCleanAfter⟩
  change (D e).path3 = none at hsourcePathAfter
  change (D (ring.rightNeighbor e)).path3 = some (payload count)
    at htargetPathAfter
  change (D (ring.rightNeighbor e)).write_state =
    (if (C (ring.rightNeighbor e)).label.val = (payload count).label
      then WriteState.none else WriteState.depart) at htargetStateAfter
  have hframes := stepConfig_writer_global_frames hψ ring (by omega)
    C e (payload count) hsourcePath htargetPath hsourceState hclean
  rcases hframes with ⟨hcleanAfter, hlabelBitAfter⟩
  change (∀ i, WriterTransportCleanFrame (D i)) at hcleanAfter
  change (∀ i, (D i).label = (C i).label ∧
    (D i).bit = (C i).bit) at hlabelBitAfter
  have htargetLabelVal : (C (ring.rightNeighbor e)).label.val =
      (round + count + 1) % ψ := by
    rw [hj]
    exact hlabel (round + count + 1) (by omega)
  have harrivalState :
      (if (C (ring.rightNeighbor e)).label.val = (payload count).label
        then WriteState.none else WriteState.depart) =
      (if round + 1 = ψ then WriteState.none else WriteState.depart) := by
    rw [htargetLabelVal, hpayload count hcountLt]
    simp only [writer_arrival_aligned_iff hψ hround hcountLt]
  have hsame (x : Nat) (hx : x < 2 * ψ)
      (hxe : x ≠ round + count) (hxj : x ≠ round + count + 1) :
      D (genericWriterPos hψ x) = C (genericWriterPos hψ x) := by
    apply stepConfig_eq_of_ne ring T C e
    · exact genericWriterPos_ne_of_lt hψ hx (by omega) hxe
    · rw [hj]
      exact genericWriterPos_ne_of_lt hψ hx (by omega) hxj
  dsimp only
  refine ⟨?_, hcleanAfter, ?_, ?_⟩
  · refine ⟨hround, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      change WriterTokenAt D (genericWriterPos hψ (round + k))
        (payload k) .depart
      unfold WriterTokenAt
      rw [hsame (round + k) (by omega) (by omega) (by omega)]
      exact hunprocessed k (by omega)
    · intro k hck hk
      change WriterTokenAt D (genericWriterPos hψ (round + k + 1))
        (payload k) (if round + 1 = ψ then .none else .depart)
      unfold WriterTokenAt
      by_cases hkc : k = count
      · subst k
        have htargetStateExact := htargetStateAfter.trans harrivalState
        rw [hj] at htargetPathAfter htargetStateExact
        exact ⟨htargetPathAfter, htargetStateExact⟩
      · rw [hsame (round + k + 1) (by omega) (by omega) (by omega)]
        exact hprocessed k (by omega) hk
    · simpa [e] using hsourcePathAfter
    · intro x hx
      change (D (genericWriterPos hψ x)).path3 = none
      rw [hsame x (by omega) (by omega) (by omega)]
      exact hprefix x hx
    · intro x hx hlt
      change (D (genericWriterPos hψ x)).path3 = none
      rw [hsame x hlt (by omega) (by omega)]
      exact htail x hx hlt
  · unfold WriterLabelFrame
    intro x hx
    rw [(hlabelBitAfter (genericWriterPos hψ x)).1]
    exact hlabel x hx
  · unfold WriterBitFrame
    intro i
    rw [(hlabelBitAfter i).2]
    exact hbit i

/-- The recursive descending schedule completes one physical block sweep. -/
theorem writerDescendingPrefixSchedule_completes_sweep {ψ : Nat}
    (hψ : 0 < ψ) (C : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info)
    (reference : Fin (2 * ψ) → AgentState ψ) (round count : Nat)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hsweep : WriterSweepState hψ C payload round count)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame hψ C)
    (hbit : WriterBitFrame reference C) :
    let D := applySchedule (genericWriterRing hψ)
      (writeSeqPersistentComparisonTransportLifecycle hψ) C
      (writerDescendingPrefixSchedule (genericWriterRing hψ)
        (genericWriterStart hψ) round count)
    WriterSweepState hψ D payload round 0 ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame hψ D ∧ WriterBitFrame reference D := by
  induction count generalizing C with
  | zero =>
      simpa [writerDescendingPrefixSchedule, applySchedule] using
        And.intro hsweep (And.intro hclean (And.intro hlabel hbit))
  | succ count ih =>
      have hone := WriterSweepState.step hψ C payload reference
        round count hpayload hsweep hclean hlabel hbit
      let C₁ := stepConfig (genericWriterRing hψ)
        (writeSeqPersistentComparisonTransportLifecycle hψ) C
        (genericWriterPos hψ (round + count))
      change WriterSweepState hψ C₁ payload round count ∧
        (∀ i, WriterTransportCleanFrame (C₁ i)) ∧
        WriterLabelFrame hψ C₁ ∧ WriterBitFrame reference C₁ at hone
      rcases hone with ⟨hsweep₁, hclean₁, hlabel₁, hbit₁⟩
      have hrest := ih C₁ hsweep₁ hclean₁ hlabel₁ hbit₁
      simpa [writerDescendingPrefixSchedule_head, genericWriterPos,
        applySchedule, C₁] using hrest

/-- One canonical right-to-left sweep advances the block invariant by one
physical edge. -/
theorem writerBlockSweepSchedule_advances_round {ψ : Nat}
    (hψ : 0 < ψ) (C : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info)
    (reference : Fin (2 * ψ) → AgentState ψ)
    (round : Nat) (hround : round < ψ)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hstate : WriterRoundState hψ C payload round)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame hψ C)
    (hbit : WriterBitFrame reference C) :
    let D := applySchedule (genericWriterRing hψ)
      (writeSeqPersistentComparisonTransportLifecycle hψ) C
      (writerBlockSweepSchedule (genericWriterRing hψ)
        (genericWriterStart hψ) ψ round)
    WriterRoundState hψ D payload (round + 1) ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame hψ D ∧ WriterBitFrame reference D := by
  have hsweep := WriterRoundState.toSweep hψ C payload round hround hstate
  have hdone := writerDescendingPrefixSchedule_completes_sweep
    hψ C payload reference round ψ hpayload hsweep hclean hlabel hbit
  let D := applySchedule (genericWriterRing hψ)
    (writeSeqPersistentComparisonTransportLifecycle hψ) C
    (writerBlockSweepSchedule (genericWriterRing hψ)
      (genericWriterStart hψ) ψ round)
  have hdone' : WriterSweepState hψ D payload round 0 ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame hψ D ∧ WriterBitFrame reference D := by
    dsimp only [D]
    simpa only [writerBlockSweepSchedule_eq_descending] using hdone
  rcases hdone' with ⟨hsweepAfter, hcleanAfter, hlabelAfter, hbitAfter⟩
  exact ⟨WriterSweepState.zero_toRound hψ D payload round hsweepAfter,
    hcleanAfter, hlabelAfter, hbitAfter⟩

theorem applySchedule_append {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (C : Fin n → AgentState ψ) (first second : DetSchedule n) :
    applySchedule ring T C (first ++ second) =
      applySchedule ring T (applySchedule ring T C first) second := by
  induction first generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.cons_append, applySchedule]
      exact ih (stepConfig ring T C e)

/-- Any prefix of the canonical outer schedule advances the writer by the
same number of physical edges. -/
theorem writerBlockTransportRounds_from_zero {ψ : Nat}
    (hψ : 0 < ψ) (C : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info)
    (reference : Fin (2 * ψ) → AgentState ψ)
    (rounds : Nat) (hrounds : rounds ≤ ψ)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hstate : WriterRoundState hψ C payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame hψ C)
    (hbit : WriterBitFrame reference C) :
    let D := applySchedule (genericWriterRing hψ)
      (writeSeqPersistentComparisonTransportLifecycle hψ) C
      (writerBlockTransportRounds (genericWriterRing hψ)
        (genericWriterStart hψ) ψ rounds)
    WriterRoundState hψ D payload rounds ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame hψ D ∧ WriterBitFrame reference D := by
  induction rounds with
  | zero =>
      simpa [writerBlockTransportRounds, applySchedule] using
        And.intro hstate (And.intro hclean (And.intro hlabel hbit))
  | succ rounds ih =>
      have hroundLt : rounds < ψ := by omega
      have hprev := ih (by omega)
      let C₁ := applySchedule (genericWriterRing hψ)
        (writeSeqPersistentComparisonTransportLifecycle hψ) C
        (writerBlockTransportRounds (genericWriterRing hψ)
          (genericWriterStart hψ) ψ rounds)
      change WriterRoundState hψ C₁ payload rounds ∧
        (∀ i, WriterTransportCleanFrame (C₁ i)) ∧
        WriterLabelFrame hψ C₁ ∧ WriterBitFrame reference C₁ at hprev
      rcases hprev with ⟨hstate₁, hclean₁, hlabel₁, hbit₁⟩
      have hnext := writerBlockSweepSchedule_advances_round hψ C₁
        payload reference rounds hroundLt hpayload hstate₁ hclean₁
        hlabel₁ hbit₁
      dsimp only
      rw [writerBlockTransportRounds, applySchedule_append,
        ← writerBlockSweepSchedule_eq_descending]
      exact hnext

/-- **Arbitrary-width writer transport.** The actual repaired lifecycle and
the canonical `ψ²` schedule translate a clean complete writer by one group. -/
theorem writerBlockTransportSchedule_from_zero {ψ : Nat}
    (hψ : 0 < ψ) (C : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info)
    (reference : Fin (2 * ψ) → AgentState ψ)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hstate : WriterRoundState hψ C payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame hψ C)
    (hbit : WriterBitFrame reference C) :
    let D := applySchedule (genericWriterRing hψ)
      (writeSeqPersistentComparisonTransportLifecycle hψ) C
      (writerBlockTransportSchedule (genericWriterRing hψ)
        (genericWriterStart hψ) ψ)
    WriterRoundState hψ D payload ψ ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame hψ D ∧ WriterBitFrame reference D := by
  have hrounds := writerBlockTransportRounds_from_zero hψ C payload
    reference ψ (Nat.le_refl _) hpayload hstate hclean hlabel hbit
  simpa only [writerBlockTransportSchedule_eq_rounds] using hrounds

/-- The transported arbitrary-width block retains the source bits and common
flag, hence satisfies the existing source-tagged component interface. -/
theorem writerBlockTransportSchedule_sourceTagged {ψ : Nat}
    (hψ : 0 < ψ) (C : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (flag : Nat)
    (hflag : flag ≤ 1)
    (hpayloadLabel : ∀ k, k < ψ → (payload k).label = k)
    (hpayloadBit : ∀ k, k < ψ → (payload k).bit =
      (if (C (genericWriterPos hψ k)).bit then 1 else 0))
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = flag)
    (hstate : WriterRoundState hψ C payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame hψ C) :
    let D := applySchedule (genericWriterRing hψ)
      (writeSeqPersistentComparisonTransportLifecycle hψ) C
      (writerBlockTransportSchedule (genericWriterRing hψ)
        (genericWriterStart hψ) ψ)
    overwritingBitsMatchBetweenAt (genericWriterRing hψ) D D
      (genericWriterPos hψ ψ) (genericWriterStart hψ) flag := by
  have htransport := writerBlockTransportSchedule_from_zero hψ C
    payload C hpayloadLabel hstate hclean hlabel (fun _ => rfl)
  let D := applySchedule (genericWriterRing hψ)
    (writeSeqPersistentComparisonTransportLifecycle hψ) C
    (writerBlockTransportSchedule (genericWriterRing hψ)
      (genericWriterStart hψ) ψ)
  change WriterRoundState hψ D payload ψ ∧
    (∀ i, WriterTransportCleanFrame (D i)) ∧
    WriterLabelFrame hψ D ∧ WriterBitFrame C D at htransport
  rcases htransport with ⟨hfinal, _, _, hbit⟩
  rcases hfinal with ⟨_, htokens, _, _⟩
  dsimp only
  constructor
  · exact hflag
  · intro k hk
    have htoken := htokens k hk
    refine ⟨payload k, ?_, hpayloadLabel k hk, ?_, hpayloadFlag k hk⟩
    · have hpos : groupOffset (genericWriterRing hψ)
          (genericWriterPos hψ ψ) k = genericWriterPos hψ (ψ + k) := by
        unfold genericWriterPos
        exact groupOffset_compose (genericWriterRing hψ)
          (genericWriterStart hψ) ψ k
      rw [hpos]
      exact htoken.1
    · change (payload k).bit =
        (if (D (genericWriterPos hψ k)).bit then 1 else 0)
      rw [hbit (genericWriterPos hψ k)]
      exact hpayloadBit k hk

/-- The arbitrary-width physical trace constructs a complete carrier at
target group one, ready for the separate ruler-flag processing join. -/
theorem writerBlockTransportSchedule_existsCarrier {ψ : Nat}
    (hψ : 0 < ψ) (C : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (flag : Nat)
    (hflag : flag ≤ 1)
    (hpayloadLabel : ∀ k, k < ψ → (payload k).label = k)
    (hpayloadBit : ∀ k, k < ψ → (payload k).bit =
      (if (C (genericWriterPos hψ k)).bit then 1 else 0))
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = flag)
    (hstate : WriterRoundState hψ C payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame hψ C) :
    let D := applySchedule (genericWriterRing hψ)
      (writeSeqPersistentComparisonTransportLifecycle hψ) C
      (writerBlockTransportSchedule (genericWriterRing hψ)
        (genericWriterStart hψ) ψ)
    ∃ carrier : SourceTaggedCompleteOverwritingCarrier
        (genericWriterRing hψ) D D (genericWriterStart hψ),
      carrier.route.source = 0 ∧ carrier.route.target = 1 ∧
        carrier.flag = flag := by
  have htag := writerBlockTransportSchedule_sourceTagged hψ C payload
    flag hflag hpayloadLabel hpayloadBit hpayloadFlag hstate hclean hlabel
  let D := applySchedule (genericWriterRing hψ)
    (writeSeqPersistentComparisonTransportLifecycle hψ) C
    (writerBlockTransportSchedule (genericWriterRing hψ)
      (genericWriterStart hψ) ψ)
  change overwritingBitsMatchBetweenAt (genericWriterRing hψ) D D
    (genericWriterPos hψ ψ) (genericWriterStart hψ) flag at htag
  dsimp only
  let route : OverwritingCarrierRoute (genericWriterRing hψ) D
      (genericWriterStart hψ) :=
    { source := 0
      target := 1
      payload := groupID (genericWriterRing hψ).hn D
        (stableGroupStart (genericWriterRing hψ)
          (genericWriterStart hψ) ψ 0)
      source_in_range := by
        rw [Nat.mul_div_left 2 hψ]
        omega
      target_in_range := by
        rw [Nat.mul_div_left 2 hψ]
        omega
      payload_from_source := rfl }
  let carrier : SourceTaggedCompleteOverwritingCarrier
      (genericWriterRing hψ) D D (genericWriterStart hψ) :=
    { route := route
      flag := flag
      components := by
        simpa [route, stableGroupStart, genericWriterPos,
          genericWriterStart, genericWriterRing, groupOffset] using htag }
  exact ⟨carrier, rfl, rfl, rfl⟩

/-- A complete flag-one writer starts in the exact ruler state before target
group one.  Thus the arbitrary-width physical trace reaches not only the
source-tagged carrier interface but its static history certificate. -/
theorem writerBlockTransportSchedule_existsRulerHistory {ψ : Nat}
    (hψ : 0 < ψ) (C : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info)
    (hpayloadLabel : ∀ k, k < ψ → (payload k).label = k)
    (hpayloadBit : ∀ k, k < ψ → (payload k).bit =
      (if (C (genericWriterPos hψ k)).bit then 1 else 0))
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = 1)
    (hstate : WriterRoundState hψ C payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame hψ C) :
    let D := applySchedule (genericWriterRing hψ)
      (writeSeqPersistentComparisonTransportLifecycle hψ) C
      (writerBlockTransportSchedule (genericWriterRing hψ)
        (genericWriterStart hψ) ψ)
    ∃ carrier : SourceTaggedCompleteOverwritingCarrier
        (genericWriterRing hψ) D D (genericWriterStart hψ),
      RulerOverwritingHistory (genericWriterRing hψ) D
        (genericWriterStart hψ) carrier := by
  have hcarrier := writerBlockTransportSchedule_existsCarrier hψ C payload 1
    (by omega) hpayloadLabel hpayloadBit hpayloadFlag hstate hclean hlabel
  let D := applySchedule (genericWriterRing hψ)
    (writeSeqPersistentComparisonTransportLifecycle hψ) C
    (writerBlockTransportSchedule (genericWriterRing hψ)
      (genericWriterStart hψ) ψ)
  change ∃ carrier : SourceTaggedCompleteOverwritingCarrier
      (genericWriterRing hψ) D D (genericWriterStart hψ),
    carrier.route.source = 0 ∧ carrier.route.target = 1 ∧
      carrier.flag = 1 at hcarrier
  obtain ⟨carrier, _, htarget, hflag⟩ := hcarrier
  refine ⟨carrier, ?_⟩
  constructor
  · rw [htarget]
    omega
  · rw [hflag, htarget]
    simp [rulerWriterFlagBefore]

/-! ## Arbitrary-width equal-target processing

The transport induction ends with an idle complete writer in target group one.
The next induction follows the actual clockwise comparison schedule.  Its
state records an equal prefix, the untouched suffix, and the pathless cell
immediately preceding the target group; the latter is the physical boundary
that starts label-zero comparison and later terminates the backward action.
-/

/-- After `count` forward interactions, exactly the first `count` target
components carry the unresolved equality token.  The range stops before the
terminal component, whose interaction selects the ruler action rather than
leaving another equality token. -/
def WriterEqualPrefixState (hψ : 0 < ψ)
    (C : Fin (2 * ψ) → AgentState ψ) (payload : Nat → Path3Info)
    (count : Nat) : Prop :=
  count ≤ ψ - 1 ∧
    (C (genericWriterPos hψ (ψ - 1))).path3 = none ∧
    ∀ k, k < ψ →
      WriterTokenAt C (genericWriterPos hψ (ψ + k)) (payload k)
        (if k < count then .equal else .none)

/-- The arbitrary-width transport endpoint is exactly the base of the forward
equal-prefix induction: the source terminal cell is empty and every target
component is aligned and idle. -/
theorem WriterRoundState.toEqualPrefix {ψ : Nat} (hψ : 0 < ψ)
    (C : Fin (2 * ψ) → AgentState ψ) (payload : Nat → Path3Info)
    (hstate : WriterRoundState hψ C payload ψ) :
    WriterEqualPrefixState hψ C payload 0 := by
  rcases hstate with ⟨_, htokens, hprefix, _⟩
  refine ⟨by omega, hprefix (ψ - 1) (by omega), ?_⟩
  intro k hk
  simpa [WriterTokenAt] using htokens k hk

/-- The first physical comparison edge lifts the local label-zero contract to
the whole arbitrary-width configuration, establishing a one-component equal
prefix while preserving all global writer frames. -/
theorem WriterEqualPrefixState.seed_step {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hcompare :
      checkBitWS (reference (genericWriterPos (by omega) ψ)).bit
        (payload 0).bit = .equal)
    (hstate : WriterEqualPrefixState (by omega) C payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := stepConfig (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (genericWriterPos (by omega) (ψ - 1))
    WriterEqualPrefixState (by omega) D payload 1 ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧ WriterBitFrame reference D := by
  rcases hstate with ⟨_, hboundary, htokens⟩
  let hp : 0 < ψ := by omega
  let ring := genericWriterRing hp
  let e := genericWriterPos hp (ψ - 1)
  let j := genericWriterPos hp ψ
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let D := stepConfig ring T C e
  have hj : ring.rightNeighbor e = j := by
    dsimp only [ring, e, j]
    rw [rightNeighbor_genericWriterPos]
    congr 2
    omega
  have htoken := htokens 0 (by omega)
  have hsourcePath : (C e).path3 = none := by
    simpa [e] using hboundary
  have htargetPath : (C j).path3 = some (payload 0) := by
    simpa [j, WriterTokenAt] using htoken.1
  have htargetState : (C j).write_state = .none := by
    simpa [j, WriterTokenAt] using htoken.2
  have htargetLabelVal : (C j).label.val = 0 := by
    have h := hlabel ψ (by omega)
    simpa [j] using h
  have htargetZero : (C j).label = ⟨0, hp⟩ := by
    apply Fin.ext
    exact htargetLabelVal
  have htargetAlign : (C j).label.val = (payload 0).label := by
    rw [htargetLabelVal, hpayload 0 (by omega)]
  have htargetCompare :
      checkBitWS (C j).bit (payload 0).bit = .equal := by
    rw [hbit j]
    simpa [j] using hcompare
  have htargetNotTerminal :
      (C j).label ≠ ⟨ψ - 1, by omega⟩ := by
    intro hterminal
    have hv := congrArg Fin.val (htargetZero.symm.trans hterminal)
    simp only at hv
    omega
  have hlocal :=
    writeSeqPersistentComparisonTransportLifecycle_equal_seed hp
      (C e) (C j) (payload 0) hsourcePath htargetPath htargetState
      htargetZero htargetAlign htargetCompare htargetNotTerminal
      (hclean e) (hclean j)
  rcases hlocal with ⟨hleftPath, hleftState, hleftLabel, hleftBit,
    hleftClean, hrightPath, hrightState, hrightLabel, hrightBit,
    hrightClean⟩
  have hleftPathT : (T (C e) (C j)).1.path3 = none := by
    simpa only [T] using hleftPath
  have hrightPathT : (T (C e) (C j)).2.path3 = some (payload 0) := by
    simpa only [T] using hrightPath
  have hrightStateT : (T (C e) (C j)).2.write_state = .equal := by
    simpa only [T] using hrightState
  have hleftCleanT : WriterTransportCleanFrame (T (C e) (C j)).1 := by
    simpa only [T] using hleftClean
  have hrightCleanT : WriterTransportCleanFrame (T (C e) (C j)).2 := by
    simpa only [T] using hrightClean
  have hleftLabelT : (T (C e) (C j)).1.label = (C e).label := by
    simpa only [T] using hleftLabel
  have hrightLabelT : (T (C e) (C j)).2.label = (C j).label := by
    simpa only [T] using hrightLabel
  have hleftBitT : (T (C e) (C j)).1.bit = (C e).bit := by
    simpa only [T] using hleftBit
  have hrightBitT : (T (C e) (C j)).2.bit = (C j).bit := by
    simpa only [T] using hrightBit
  have hleftD : D e = (T (C e) (C j)).1 := by
    simp [D, stepConfig, hj]
  have hrightD : D j = (T (C e) (C j)).2 := by
    have hne : j ≠ e := by
      exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
    simp [D, stepConfig, hj, hne]
  have hframes := stepConfig_global_writer_frames_of_endpoint_contract
    ring (by omega) T C e hclean
    (by rw [hj]; exact hleftCleanT)
    (by rw [hj]; exact hrightCleanT)
    (by rw [hj]; exact hleftLabelT)
    (by rw [hj]; exact hrightLabelT)
    (by rw [hj]; exact hleftBitT)
    (by rw [hj]; exact hrightBitT)
  change (∀ i, WriterTransportCleanFrame (D i)) ∧
    ∀ i, (D i).label = (C i).label ∧ (D i).bit = (C i).bit at hframes
  rcases hframes with ⟨hcleanAfter, hlabelBitAfter⟩
  change WriterEqualPrefixState hp D payload 1 ∧
    (∀ i, WriterTransportCleanFrame (D i)) ∧
    WriterLabelFrame hp D ∧ WriterBitFrame reference D
  refine ⟨?_, hcleanAfter, ?_, ?_⟩
  · refine ⟨by omega, ?_, ?_⟩
    · change (D e).path3 = none
      rw [hleftD]
      exact hleftPathT
    · intro k hk
      by_cases hk0 : k = 0
      · subst k
        change WriterTokenAt D j (payload 0) .equal
        unfold WriterTokenAt
        rw [hrightD]
        exact ⟨hrightPathT, hrightStateT⟩
      · have hsame : D (genericWriterPos hp (ψ + k)) =
            C (genericWriterPos hp (ψ + k)) := by
          apply stepConfig_eq_of_ne ring T C e
          · exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
              (by omega)
          · rw [hj]
            exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
              (by omega)
        unfold WriterTokenAt
        rw [hsame]
        simpa [hk0, WriterTokenAt] using htokens k hk
  · intro x hx
    rw [(hlabelBitAfter (genericWriterPos hp x)).1]
    exact hlabel x hx
  · intro i
    rw [(hlabelBitAfter i).2]
    exact hbit i

/-- Every later nonterminal forward edge extends the equal prefix by one
component.  The proof uses the arbitrary-`ψ` local comparison contract and
shows that the actual ring update leaves the boundary, untouched suffix, and
all global frames unchanged. -/
theorem WriterEqualPrefixState.nonterminal_step {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (count : Nat)
    (hcountPos : 0 < count) (hcount : count < ψ - 1)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hcompare :
      checkBitWS
        (reference (genericWriterPos (by omega) (ψ + count))).bit
        (payload count).bit = .equal)
    (hstate : WriterEqualPrefixState (by omega) C payload count)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := stepConfig (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (genericWriterPos (by omega) (ψ + count - 1))
    WriterEqualPrefixState (by omega) D payload (count + 1) ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧ WriterBitFrame reference D := by
  rcases hstate with ⟨_, hboundary, htokens⟩
  let hp : 0 < ψ := by omega
  let ring := genericWriterRing hp
  let e := genericWriterPos hp (ψ + count - 1)
  let j := genericWriterPos hp (ψ + count)
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let D := stepConfig ring T C e
  have heIndex : ψ + count - 1 = ψ + (count - 1) := by omega
  have hj : ring.rightNeighbor e = j := by
    dsimp only [ring, e, j]
    rw [rightNeighbor_genericWriterPos]
    apply congrArg (genericWriterPos hp)
    omega
  have hleftToken := htokens (count - 1) (by omega)
  have hrightToken := htokens count (by omega)
  have hleftPath : (C e).path3 = some (payload (count - 1)) := by
    simpa [e, WriterTokenAt, heIndex] using hleftToken.1
  have hleftState : (C e).write_state = .equal := by
    have hlt : count - 1 < count := by omega
    simpa [e, WriterTokenAt, heIndex, hlt] using hleftToken.2
  have hrightPath : (C j).path3 = some (payload count) := by
    simpa [j, WriterTokenAt] using hrightToken.1
  have hrightState : (C j).write_state = .none := by
    simpa [j, WriterTokenAt] using hrightToken.2
  have hleftLabelVal : (C e).label.val = count - 1 := by
    calc
      (C e).label.val = (ψ + count - 1) % ψ := hlabel _ (by omega)
      _ = count - 1 := by
        rw [heIndex, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hrightLabelVal : (C j).label.val = count := by
    calc
      (C j).label.val = (ψ + count) % ψ := hlabel _ (by omega)
      _ = count := by
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hleftAlign : (C e).label.val = (payload (count - 1)).label := by
    rw [hleftLabelVal, hpayload (count - 1) (by omega)]
  have hrightAlign : (C j).label.val = (payload count).label := by
    rw [hrightLabelVal, hpayload count (by omega)]
  have hrightCompare :
      checkBitWS (C j).bit (payload count).bit = .equal := by
    rw [hbit j]
    simpa [j] using hcompare
  have hleftCompare : (C e).label.val < ψ - 1 := by
    rw [hleftLabelVal]
    omega
  have hrightZero : (C j).label ≠ ⟨0, hp⟩ := by
    intro hzero
    have hv := congrArg Fin.val hzero
    simp only at hv
    rw [hrightLabelVal] at hv
    omega
  have hrightNotTerminal :
      (C j).label ≠ ⟨ψ - 1, by omega⟩ := by
    intro hterminal
    have hv := congrArg Fin.val hterminal
    simp only at hv
    rw [hrightLabelVal] at hv
    omega
  have horder : (C e).label < (C j).label := by
    change (C e).label.val < (C j).label.val
    rw [hleftLabelVal, hrightLabelVal]
    omega
  have hlocal :=
    writeSeqPersistentComparisonTransportLifecycle_equal_nonterminal hp
      (C e) (C j) (payload (count - 1)) (payload count)
      hleftPath hrightPath hleftState hrightState hleftAlign hrightAlign
      hrightCompare hleftCompare hrightZero hrightNotTerminal
      (hclean e) (hclean j)
  rcases hlocal with ⟨hleftPathAfter, hleftStateAfter, hleftLabelAfter,
    hleftBitAfter, hleftCleanAfter, hrightPathAfter, hrightStateAfter,
    hrightLabelAfter, hrightBitAfter, hrightCleanAfter⟩
  have hleftPathT :
      (T (C e) (C j)).1.path3 = some (payload (count - 1)) := by
    simpa only [T] using hleftPathAfter
  have hleftStateT : (T (C e) (C j)).1.write_state = .equal := by
    simpa only [T] using hleftStateAfter
  have hrightPathT : (T (C e) (C j)).2.path3 = some (payload count) := by
    simpa only [T] using hrightPathAfter
  have hrightStateT : (T (C e) (C j)).2.write_state = .equal := by
    simpa only [T] using hrightStateAfter
  have hleftCleanT : WriterTransportCleanFrame (T (C e) (C j)).1 := by
    simpa only [T] using hleftCleanAfter
  have hrightCleanT : WriterTransportCleanFrame (T (C e) (C j)).2 := by
    simpa only [T] using hrightCleanAfter
  have hleftLabelT : (T (C e) (C j)).1.label = (C e).label := by
    simpa only [T] using hleftLabelAfter
  have hrightLabelT : (T (C e) (C j)).2.label = (C j).label := by
    simpa only [T] using hrightLabelAfter
  have hleftBitT : (T (C e) (C j)).1.bit = (C e).bit := by
    simpa only [T] using hleftBitAfter
  have hrightBitT : (T (C e) (C j)).2.bit = (C j).bit := by
    simpa only [T] using hrightBitAfter
  have hleftD : D e = (T (C e) (C j)).1 := by
    simp [D, stepConfig, hj]
  have hrightD : D j = (T (C e) (C j)).2 := by
    have hne : j ≠ e :=
      genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
    simp [D, stepConfig, hj, hne]
  have hframes := stepConfig_global_writer_frames_of_endpoint_contract
    ring (by omega) T C e hclean
    (by rw [hj]; exact hleftCleanT)
    (by rw [hj]; exact hrightCleanT)
    (by rw [hj]; exact hleftLabelT)
    (by rw [hj]; exact hrightLabelT)
    (by rw [hj]; exact hleftBitT)
    (by rw [hj]; exact hrightBitT)
  change (∀ i, WriterTransportCleanFrame (D i)) ∧
    ∀ i, (D i).label = (C i).label ∧ (D i).bit = (C i).bit at hframes
  rcases hframes with ⟨hcleanAfter, hlabelBitAfter⟩
  change WriterEqualPrefixState hp D payload (count + 1) ∧
    (∀ i, WriterTransportCleanFrame (D i)) ∧
    WriterLabelFrame hp D ∧ WriterBitFrame reference D
  refine ⟨?_, hcleanAfter, ?_, ?_⟩
  · refine ⟨by omega, ?_, ?_⟩
    · have hsame : D (genericWriterPos hp (ψ - 1)) =
          C (genericWriterPos hp (ψ - 1)) := by
        apply stepConfig_eq_of_ne ring T C e
        · exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
            (by omega)
        · rw [hj]
          exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
            (by omega)
      rw [hsame]
      simpa using hboundary
    · intro k hk
      by_cases hkc : k = count
      · subst k
        unfold WriterTokenAt
        rw [if_pos (by omega : count < count + 1)]
        change (D j).path3 = some (payload count) ∧
          (D j).write_state = .equal
        rw [hrightD]
        exact ⟨hrightPathT, hrightStateT⟩
      · by_cases hkp : k = count - 1
        · subst k
          unfold WriterTokenAt
          have hePos : genericWriterPos hp (ψ + (count - 1)) = e := by
            simp [e, heIndex]
          rw [hePos]
          rw [if_pos (by omega : count - 1 < count + 1)]
          rw [hleftD]
          exact ⟨hleftPathT, hleftStateT⟩
        · have hsame : D (genericWriterPos hp (ψ + k)) =
              C (genericWriterPos hp (ψ + k)) := by
            apply stepConfig_eq_of_ne ring T C e
            · exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
                (by omega)
            · rw [hj]
              exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
                (by omega)
          have hkiff : k < count + 1 ↔ k < count := by omega
          unfold WriterTokenAt
          rw [hsame]
          simpa [hkiff, WriterTokenAt] using htokens k hk
  · intro x hx
    rw [(hlabelBitAfter (genericWriterPos hp x)).1]
    exact hlabel x hx
  · intro i
    rw [(hlabelBitAfter i).2]
    exact hbit i

/-- The first `count` edges of the clockwise target-group comparison.  Edge
zero is the source-terminal to target-zero boundary; every later edge joins
two successive target components. -/
def writerEqualPrefixSchedule {ψ : Nat} (hψ : 0 < ψ) :
    Nat → DetSchedule (2 * ψ)
  | 0 => []
  | count + 1 =>
      writerEqualPrefixSchedule hψ count ++
        [genericWriterPos hψ (ψ + count - 1)]

/-- The actual recursive forward schedule establishes any requested proper
equal prefix.  In particular, `count = ψ-1` reaches the exact preterminal
configuration consumed by the terminal action contract. -/
theorem writerEqualPrefixSchedule_reaches {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (count : Nat) (hcount : count ≤ ψ - 1)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hcompare : ∀ k, k < count →
      checkBitWS (reference (genericWriterPos (by omega) (ψ + k))).bit
        (payload k).bit = .equal)
    (hstate : WriterEqualPrefixState (by omega) C payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := applySchedule (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (writerEqualPrefixSchedule (by omega) count)
    WriterEqualPrefixState (by omega) D payload count ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧ WriterBitFrame reference D := by
  induction count with
  | zero =>
      simpa [writerEqualPrefixSchedule, applySchedule] using
        And.intro hstate (And.intro hclean (And.intro hlabel hbit))
  | succ count ih =>
      have hprev := ih (by omega)
        (fun k hk => hcompare k (by omega)) hstate hlabel
      let hp : 0 < ψ := by omega
      let C₁ := applySchedule (genericWriterRing hp)
        (writeSeqPersistentComparisonTransportLifecycle hp) C
        (writerEqualPrefixSchedule hp count)
      change WriterEqualPrefixState hp C₁ payload count ∧
        (∀ i, WriterTransportCleanFrame (C₁ i)) ∧
        WriterLabelFrame hp C₁ ∧ WriterBitFrame reference C₁ at hprev
      rcases hprev with ⟨hstate₁, hclean₁, hlabel₁, hbit₁⟩
      have hnext :
          let D := stepConfig (genericWriterRing hp)
            (writeSeqPersistentComparisonTransportLifecycle hp) C₁
            (genericWriterPos hp (ψ + count - 1))
          WriterEqualPrefixState hp D payload (count + 1) ∧
            (∀ i, WriterTransportCleanFrame (D i)) ∧
            WriterLabelFrame hp D ∧ WriterBitFrame reference D := by
        cases count with
        | zero =>
            simpa using WriterEqualPrefixState.seed_step hψ C₁ reference
              payload hpayload (hcompare 0 (by omega)) hstate₁ hclean₁
              hlabel₁ hbit₁
        | succ count =>
            exact WriterEqualPrefixState.nonterminal_step hψ C₁ reference
              payload (count + 1) (by omega) (by omega) hpayload
              (hcompare (count + 1) (by omega)) hstate₁ hclean₁ hlabel₁
              hbit₁
      dsimp only
      rw [writerEqualPrefixSchedule, applySchedule_append]
      simpa [applySchedule, C₁, hp] using hnext

/-! ## Arbitrary-width flag-one backward action

Terminal equality with a flag-one writer selects `move_flip`.  The action then
travels from the terminal component back to label zero.  The invariant below
counts the already retired suffix: the unprocessed prefix remains in `equal`,
its rightmost component carries `move_flip`, and the processed suffix has
flipped payload flags and `depart` state.
-/

/-- After `processed` components of a flag-one action have retired, the
rightmost `processed` payloads have complemented flags.  Unless the whole
group is done, the component immediately to their left carries `move_flip`;
all still earlier components retain the forward-comparison state. -/
def WriterMoveFlipSweepState (hψ : 0 < ψ)
    (C : Fin (2 * ψ) → AgentState ψ) (payload : Nat → Path3Info)
    (processed : Nat) : Prop :=
  1 ≤ processed ∧ processed ≤ ψ ∧
    (C (genericWriterPos hψ (ψ - 1))).path3 = none ∧
    ∀ k, k < ψ →
      WriterTokenAt C (genericWriterPos hψ (ψ + k))
        (if k + processed < ψ then payload k
          else { payload k with flag := 1 - (payload k).flag })
        (if k + processed + 1 < ψ then .equal
          else if k + processed + 1 = ψ then .move_flip else .depart)

/-- The terminal comparison edge converts the full proper equal prefix into
the base case of the backward sweep.  It flips and retires the terminal
payload, hands `move_flip` to its predecessor, and preserves the clean, label,
and physical-bit frames globally. -/
theorem WriterEqualPrefixState.terminal_one_step {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hcompare : ∀ k, k < ψ →
      checkBitWS (reference (genericWriterPos (by omega) (ψ + k))).bit
        (payload k).bit = .equal)
    (hterminalFlag : (payload (ψ - 1)).flag = 1)
    (hstate : WriterEqualPrefixState (by omega) C payload (ψ - 1))
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := stepConfig (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (genericWriterPos (by omega) (ψ + (ψ - 1) - 1))
    WriterMoveFlipSweepState (by omega) D payload 1 ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧ WriterBitFrame reference D := by
  rcases hstate with ⟨_, hboundary, htokens⟩
  let hp : 0 < ψ := by omega
  let ring := genericWriterRing hp
  let e := genericWriterPos hp (ψ + (ψ - 1) - 1)
  let j := genericWriterPos hp (ψ + (ψ - 1))
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let D := stepConfig ring T C e
  have heIndex : ψ + (ψ - 1) - 1 = ψ + (ψ - 2) := by omega
  have hj : ring.rightNeighbor e = j := by
    dsimp only [ring, e, j]
    rw [rightNeighbor_genericWriterPos]
    apply congrArg (genericWriterPos hp)
    omega
  have hleftToken := htokens (ψ - 2) (by omega)
  have hrightToken := htokens (ψ - 1) (by omega)
  have hleftPath : (C e).path3 = some (payload (ψ - 2)) := by
    simpa [e, WriterTokenAt, heIndex] using hleftToken.1
  have hleftState : (C e).write_state = .equal := by
    have hprefix : ψ - 2 < ψ - 1 := by omega
    simpa [e, WriterTokenAt, heIndex, hprefix] using hleftToken.2
  have hrightPath : (C j).path3 = some (payload (ψ - 1)) := by
    simpa [j, WriterTokenAt] using hrightToken.1
  have hrightState : (C j).write_state = .none := by
    simpa [j, WriterTokenAt] using hrightToken.2
  have hleftLabelVal : (C e).label.val = ψ - 2 := by
    calc
      (C e).label.val = (ψ + (ψ - 1) - 1) % ψ := hlabel _ (by omega)
      _ = ψ - 2 := by
        rw [heIndex, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hrightLabelVal : (C j).label.val = ψ - 1 := by
    calc
      (C j).label.val = (ψ + (ψ - 1)) % ψ := hlabel _ (by omega)
      _ = ψ - 1 := by
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hleftAlign : (C e).label.val = (payload (ψ - 2)).label := by
    rw [hleftLabelVal, hpayload (ψ - 2) (by omega)]
  have hrightAlign : (C j).label.val = (payload (ψ - 1)).label := by
    rw [hrightLabelVal, hpayload (ψ - 1) (by omega)]
  have hrightCompare :
      checkBitWS (C j).bit (payload (ψ - 1)).bit = .equal := by
    rw [hbit j]
    simpa [j] using hcompare (ψ - 1) (by omega)
  have hleftCompare : (C e).label.val < ψ - 1 := by
    rw [hleftLabelVal]
    omega
  have hrightTerminal : (C j).label = ⟨ψ - 1, by omega⟩ := by
    apply Fin.ext
    exact hrightLabelVal
  have hrightZero : (C j).label ≠ ⟨0, hp⟩ := by
    intro hzero
    have hv := congrArg Fin.val hzero
    simp only at hv
    rw [hrightLabelVal] at hv
    omega
  have horder : (C e).label < (C j).label := by
    change (C e).label.val < (C j).label.val
    rw [hleftLabelVal, hrightLabelVal]
    omega
  have hlocal :=
    writeSeqPersistentComparisonTransportLifecycle_equal_terminal_one hp
      (C e) (C j) (payload (ψ - 2)) (payload (ψ - 1))
      hleftPath hrightPath hleftState hrightState hleftAlign hrightAlign
      hrightCompare hleftCompare hrightTerminal hrightZero horder
      hterminalFlag (hclean e) (hclean j)
  rcases hlocal with ⟨hleftPathAfter, hleftStateAfter, hleftLabelAfter,
    hleftBitAfter, hleftCleanAfter, hrightPathAfter, hrightStateAfter,
    hrightLabelAfter, hrightBitAfter, hrightCleanAfter⟩
  have hleftD : D e = (T (C e) (C j)).1 := by
    simp [D, stepConfig, hj]
  have hrightD : D j = (T (C e) (C j)).2 := by
    have hne : j ≠ e :=
      genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
    simp [D, stepConfig, hj, hne]
  have hframes := stepConfig_global_writer_frames_of_endpoint_contract
    ring (by omega) T C e hclean
    (by rw [hj]; simpa only [T] using hleftCleanAfter)
    (by rw [hj]; simpa only [T] using hrightCleanAfter)
    (by rw [hj]; simpa only [T] using hleftLabelAfter)
    (by rw [hj]; simpa only [T] using hrightLabelAfter)
    (by rw [hj]; simpa only [T] using hleftBitAfter)
    (by rw [hj]; simpa only [T] using hrightBitAfter)
  change (∀ i, WriterTransportCleanFrame (D i)) ∧
    ∀ i, (D i).label = (C i).label ∧ (D i).bit = (C i).bit at hframes
  rcases hframes with ⟨hcleanAfter, hlabelBitAfter⟩
  change WriterMoveFlipSweepState hp D payload 1 ∧
    (∀ i, WriterTransportCleanFrame (D i)) ∧
    WriterLabelFrame hp D ∧ WriterBitFrame reference D
  refine ⟨?_, hcleanAfter, ?_, ?_⟩
  · refine ⟨by omega, by omega, ?_, ?_⟩
    · have hsame : D (genericWriterPos hp (ψ - 1)) =
          C (genericWriterPos hp (ψ - 1)) := by
        apply stepConfig_eq_of_ne ring T C e
        · exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
            (by omega)
        · rw [hj]
          exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
            (by omega)
      rw [hsame]
      exact hboundary
    · intro k hk
      by_cases hkLeft : k = ψ - 2
      · subst k
        have hpayloadOriginal : ψ - 2 + 1 < ψ := by omega
        have hstateNotEarly : ¬ (ψ - 2 + 1 + 1 < ψ) := by omega
        have hstateFrontier : ψ - 2 + 1 + 1 = ψ := by omega
        unfold WriterTokenAt
        rw [show genericWriterPos hp (ψ + (ψ - 2)) = e by simp [e, heIndex]]
        rw [hleftD]
        simpa [T, hpayloadOriginal, hstateNotEarly, hstateFrontier] using
          And.intro hleftPathAfter hleftStateAfter
      · by_cases hkRight : k = ψ - 1
        · subst k
          have hpayloadFlipped : ¬ (ψ - 1 + 1 < ψ) := by omega
          have hstateNotEarly : ¬ (ψ - 1 + 1 + 1 < ψ) := by omega
          have hstateNotFrontier : ψ - 1 + 1 + 1 ≠ ψ := by omega
          unfold WriterTokenAt
          rw [show genericWriterPos hp (ψ + (ψ - 1)) = j by rfl]
          rw [hrightD]
          simpa [T, hpayloadFlipped, hstateNotEarly, hstateNotFrontier] using
            And.intro hrightPathAfter hrightStateAfter
        · have hkEarly : k < ψ - 2 := by omega
          have hkPayload : k + 1 < ψ := by omega
          have hkState : k + 1 + 1 < ψ := by omega
          have hkPrefix : k < ψ - 1 := by omega
          have hsame : D (genericWriterPos hp (ψ + k)) =
              C (genericWriterPos hp (ψ + k)) := by
            apply stepConfig_eq_of_ne ring T C e
            · exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
                (by omega)
            · rw [hj]
              exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
                (by omega)
          unfold WriterTokenAt
          rw [hsame]
          simpa [hkPayload, hkState, hkPrefix, WriterTokenAt] using
            htokens k hk
  · intro x hx
    rw [(hlabelBitAfter (genericWriterPos hp x)).1]
    exact hlabel x hx
  · intro i
    rw [(hlabelBitAfter i).2]
    exact hbit i

/-- While the `move_flip` frontier has positive label, the actual edge from
its equal predecessor advances the frontier one component to the left.  The
old frontier retires with complemented flag, and every cell outside the two
endpoints keeps the same branch of the sweep invariant. -/
theorem WriterMoveFlipSweepState.nonzero_step {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (processed : Nat)
    (hprocessed : processed < ψ - 1)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hstate : WriterMoveFlipSweepState (by omega) C payload processed)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let frontier := ψ - processed - 1
    let D := stepConfig (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (genericWriterPos (by omega) (ψ + frontier - 1))
    WriterMoveFlipSweepState (by omega) D payload (processed + 1) ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧ WriterBitFrame reference D := by
  rcases hstate with ⟨hprocessedPos, hprocessedLe, hboundary, htokens⟩
  let hp : 0 < ψ := by omega
  let frontier := ψ - processed - 1
  have hfrontierPos : 0 < frontier := by
    dsimp only [frontier]
    omega
  have hfrontierLt : frontier < ψ := by
    dsimp only [frontier]
    omega
  have hfrontierSum : frontier + processed + 1 = ψ := by
    dsimp only [frontier]
    omega
  let ring := genericWriterRing hp
  let e := genericWriterPos hp (ψ + frontier - 1)
  let j := genericWriterPos hp (ψ + frontier)
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let D := stepConfig ring T C e
  have heIndex : ψ + frontier - 1 = ψ + (frontier - 1) := by omega
  have hj : ring.rightNeighbor e = j := by
    dsimp only [ring, e, j]
    rw [rightNeighbor_genericWriterPos]
    apply congrArg (genericWriterPos hp)
    omega
  have hleftToken := htokens (frontier - 1) (by omega)
  have hrightToken := htokens frontier hfrontierLt
  have hleftPayloadOld : frontier - 1 + processed < ψ := by omega
  have hleftStateOld : frontier - 1 + processed + 1 < ψ := by omega
  have hrightPayloadOld : frontier + processed < ψ := by omega
  have hrightStateNotEarly : ¬ (frontier + processed + 1 < ψ) := by omega
  have hrightStateFrontier : frontier + processed + 1 = ψ :=
    hfrontierSum
  have hleftPath : (C e).path3 = some (payload (frontier - 1)) := by
    simpa [e, WriterTokenAt, heIndex, hleftPayloadOld] using hleftToken.1
  have hleftState : (C e).write_state = .equal := by
    simpa [e, WriterTokenAt, heIndex, hleftStateOld] using hleftToken.2
  have hrightPath : (C j).path3 = some (payload frontier) := by
    simpa [j, WriterTokenAt, hrightPayloadOld] using hrightToken.1
  have hrightState : (C j).write_state = .move_flip := by
    simpa [j, WriterTokenAt, hrightStateNotEarly,
      hrightStateFrontier] using hrightToken.2
  have hleftLabelVal : (C e).label.val = frontier - 1 := by
    calc
      (C e).label.val = (ψ + frontier - 1) % ψ := hlabel _ (by omega)
      _ = frontier - 1 := by
        rw [heIndex, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hrightLabelVal : (C j).label.val = frontier := by
    calc
      (C j).label.val = (ψ + frontier) % ψ := hlabel _ (by omega)
      _ = frontier := by
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt hfrontierLt]
  have hleftAlign : (C e).label.val = (payload (frontier - 1)).label := by
    rw [hleftLabelVal, hpayload (frontier - 1) (by omega)]
  have hrightAlign : (C j).label.val = (payload frontier).label := by
    rw [hrightLabelVal, hpayload frontier hfrontierLt]
  have hleftCompare : (C e).label.val < ψ - 1 := by
    rw [hleftLabelVal]
    omega
  have hrightZero : (C j).label ≠ ⟨0, hp⟩ := by
    intro hzero
    have hv := congrArg Fin.val hzero
    simp only at hv
    rw [hrightLabelVal] at hv
    omega
  have horder : (C e).label < (C j).label := by
    change (C e).label.val < (C j).label.val
    rw [hleftLabelVal, hrightLabelVal]
    omega
  have hlocal :=
    writeSeqPersistentComparisonTransportLifecycle_move_flip_nonzero hp
      (C e) (C j) (payload (frontier - 1)) (payload frontier)
      hleftPath hrightPath hleftState hrightState hleftAlign hrightAlign
      hleftCompare hrightZero horder (hclean e) (hclean j)
  rcases hlocal with ⟨hleftPathAfter, hleftStateAfter, hleftLabelAfter,
    hleftBitAfter, hleftCleanAfter, hrightPathAfter, hrightStateAfter,
    hrightLabelAfter, hrightBitAfter, hrightCleanAfter⟩
  have hleftD : D e = (T (C e) (C j)).1 := by
    simp [D, stepConfig, hj]
  have hrightD : D j = (T (C e) (C j)).2 := by
    have hne : j ≠ e :=
      genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
    simp [D, stepConfig, hj, hne]
  have hframes := stepConfig_global_writer_frames_of_endpoint_contract
    ring (by omega) T C e hclean
    (by rw [hj]; simpa only [T] using hleftCleanAfter)
    (by rw [hj]; simpa only [T] using hrightCleanAfter)
    (by rw [hj]; simpa only [T] using hleftLabelAfter)
    (by rw [hj]; simpa only [T] using hrightLabelAfter)
    (by rw [hj]; simpa only [T] using hleftBitAfter)
    (by rw [hj]; simpa only [T] using hrightBitAfter)
  change (∀ i, WriterTransportCleanFrame (D i)) ∧
    ∀ i, (D i).label = (C i).label ∧ (D i).bit = (C i).bit at hframes
  rcases hframes with ⟨hcleanAfter, hlabelBitAfter⟩
  dsimp only
  change WriterMoveFlipSweepState hp D payload (processed + 1) ∧
    (∀ i, WriterTransportCleanFrame (D i)) ∧
    WriterLabelFrame hp D ∧ WriterBitFrame reference D
  refine ⟨?_, hcleanAfter, ?_, ?_⟩
  · refine ⟨by omega, by omega, ?_, ?_⟩
    · have hsame : D (genericWriterPos hp (ψ - 1)) =
          C (genericWriterPos hp (ψ - 1)) := by
        apply stepConfig_eq_of_ne ring T C e
        · exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
            (by omega)
        · rw [hj]
          exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
            (by omega)
      rw [hsame]
      exact hboundary
    · intro k hk
      by_cases hkLeft : k = frontier - 1
      · subst k
        have hpayloadOriginal : frontier - 1 + (processed + 1) < ψ := by
          omega
        have hstateNotEarly :
            ¬ (frontier - 1 + (processed + 1) + 1 < ψ) := by omega
        have hstateFrontier :
            frontier - 1 + (processed + 1) + 1 = ψ := by omega
        unfold WriterTokenAt
        rw [show genericWriterPos hp (ψ + (frontier - 1)) = e by
          simp [e, heIndex]]
        rw [hleftD]
        simpa [T, hpayloadOriginal, hstateNotEarly, hstateFrontier] using
          And.intro hleftPathAfter hleftStateAfter
      · by_cases hkRight : k = frontier
        · subst k
          have hpayloadFlipped :
              ¬ (frontier + (processed + 1) < ψ) := by omega
          have hstateNotEarly :
              ¬ (frontier + (processed + 1) + 1 < ψ) := by omega
          have hstateNotFrontier :
              frontier + (processed + 1) + 1 ≠ ψ := by omega
          unfold WriterTokenAt
          rw [show genericWriterPos hp (ψ + frontier) = j by rfl]
          rw [hrightD]
          simpa [T, hpayloadFlipped, hstateNotEarly,
            hstateNotFrontier] using
              And.intro hrightPathAfter hrightStateAfter
        · have hsame : D (genericWriterPos hp (ψ + k)) =
              C (genericWriterPos hp (ψ + k)) := by
            apply stepConfig_eq_of_ne ring T C e
            · exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
                (by omega)
            · rw [hj]
              exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
                (by omega)
          unfold WriterTokenAt
          rw [hsame]
          by_cases hkEarly : k < frontier
          · have hkBefore : k < frontier - 1 := by omega
            have hpayloadOld : k + processed < ψ := by omega
            have hpayloadNew : k + (processed + 1) < ψ := by omega
            have hstateOld : k + processed + 1 < ψ := by omega
            have hstateNew : k + (processed + 1) + 1 < ψ := by omega
            simpa [WriterTokenAt, hpayloadOld, hpayloadNew, hstateOld,
              hstateNew] using
              htokens k hk
          · have hkAfter : frontier < k := by omega
            have hpayloadOld : ¬ (k + processed < ψ) := by omega
            have hpayloadNew : ¬ (k + (processed + 1) < ψ) := by omega
            have hstateOldEarly : ¬ (k + processed + 1 < ψ) := by omega
            have hstateOldFrontier : k + processed + 1 ≠ ψ := by omega
            have hstateNewEarly :
                ¬ (k + (processed + 1) + 1 < ψ) := by omega
            have hstateNewFrontier :
                k + (processed + 1) + 1 ≠ ψ := by omega
            simpa [WriterTokenAt, hpayloadOld, hpayloadNew, hstateOldEarly,
              hstateOldFrontier, hstateNewEarly, hstateNewFrontier] using
                htokens k hk
  · intro x hx
    rw [(hlabelBitAfter (genericWriterPos hp x)).1]
    exact hlabel x hx
  · intro i
    rw [(hlabelBitAfter i).2]
    exact hbit i

/-- When the backward frontier reaches label zero, the source-terminal to
target-zero edge executes the final `move_flip` without propagating a command
across the group boundary.  The whole target writer is then uniformly
retired with complemented flags. -/
theorem WriterMoveFlipSweepState.zero_step {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hstate : WriterMoveFlipSweepState (by omega) C payload (ψ - 1))
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := stepConfig (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (genericWriterPos (by omega) (ψ - 1))
    WriterMoveFlipSweepState (by omega) D payload ψ ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧ WriterBitFrame reference D := by
  rcases hstate with ⟨_, _, hboundary, htokens⟩
  let hp : 0 < ψ := by omega
  let ring := genericWriterRing hp
  let e := genericWriterPos hp (ψ - 1)
  let j := genericWriterPos hp ψ
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let D := stepConfig ring T C e
  have hj : ring.rightNeighbor e = j := by
    dsimp only [ring, e, j]
    rw [rightNeighbor_genericWriterPos]
    congr 2
    omega
  have hrightToken := htokens 0 (by omega)
  have hpayloadOld : ψ - 1 < ψ := by omega
  have hstateNotEarly : ¬ (ψ - 1 + 1 < ψ) := by omega
  have hstateFrontier : ψ - 1 + 1 = ψ := by omega
  have hleftPath : (C e).path3 = none := by
    simpa [e] using hboundary
  have hrightPath : (C j).path3 = some (payload 0) := by
    simpa [j, WriterTokenAt, hpayloadOld] using hrightToken.1
  have hrightState : (C j).write_state = .move_flip := by
    simpa [j, WriterTokenAt, hstateNotEarly, hstateFrontier] using
      hrightToken.2
  have hrightLabelVal : (C j).label.val = 0 := by
    calc
      (C j).label.val = ψ % ψ := hlabel ψ (by omega)
      _ = 0 := Nat.mod_self ψ
  have hrightZero : (C j).label = ⟨0, hp⟩ := by
    apply Fin.ext
    exact hrightLabelVal
  have hrightAlign : (C j).label.val = (payload 0).label := by
    rw [hrightLabelVal, hpayload 0 (by omega)]
  have hlocal :=
    writeSeqPersistentComparisonTransportLifecycle_move_flip_zero hp
      (C e) (C j) (payload 0) hleftPath hrightPath hrightState
      hrightZero hrightAlign (hclean e) (hclean j)
  rcases hlocal with ⟨hleftPathAfter, hleftStateAfter, hleftLabelAfter,
    hleftBitAfter, hleftCleanAfter, hrightPathAfter, hrightStateAfter,
    hrightLabelAfter, hrightBitAfter, hrightCleanAfter⟩
  have hleftD : D e = (T (C e) (C j)).1 := by
    simp [D, stepConfig, hj]
  have hrightD : D j = (T (C e) (C j)).2 := by
    have hne : j ≠ e :=
      genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
    simp [D, stepConfig, hj, hne]
  have hframes := stepConfig_global_writer_frames_of_endpoint_contract
    ring (by omega) T C e hclean
    (by rw [hj]; simpa only [T] using hleftCleanAfter)
    (by rw [hj]; simpa only [T] using hrightCleanAfter)
    (by rw [hj]; simpa only [T] using hleftLabelAfter)
    (by rw [hj]; simpa only [T] using hrightLabelAfter)
    (by rw [hj]; simpa only [T] using hleftBitAfter)
    (by rw [hj]; simpa only [T] using hrightBitAfter)
  change (∀ i, WriterTransportCleanFrame (D i)) ∧
    ∀ i, (D i).label = (C i).label ∧ (D i).bit = (C i).bit at hframes
  rcases hframes with ⟨hcleanAfter, hlabelBitAfter⟩
  change WriterMoveFlipSweepState hp D payload ψ ∧
    (∀ i, WriterTransportCleanFrame (D i)) ∧
    WriterLabelFrame hp D ∧ WriterBitFrame reference D
  refine ⟨?_, hcleanAfter, ?_, ?_⟩
  · refine ⟨by omega, by omega, ?_, ?_⟩
    · change (D e).path3 = none
      rw [hleftD]
      simpa only [T] using hleftPathAfter
    · intro k hk
      by_cases hkZero : k = 0
      · subst k
        have hpayloadFlipped : ¬ (ψ < ψ) := by omega
        have hstateNotEarlyNew : ¬ (ψ + 1 < ψ) := by omega
        have hstateNotFrontierNew : ψ + 1 ≠ ψ := by omega
        unfold WriterTokenAt
        rw [show genericWriterPos hp (ψ + 0) = j by simp [j]]
        rw [hrightD]
        simpa [T, hpayloadFlipped, hstateNotEarlyNew,
          hstateNotFrontierNew] using
            And.intro hrightPathAfter hrightStateAfter
      · have hkPos : 0 < k := by omega
        have hsame : D (genericWriterPos hp (ψ + k)) =
            C (genericWriterPos hp (ψ + k)) := by
          apply stepConfig_eq_of_ne ring T C e
          · exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
              (by omega)
          · rw [hj]
            exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
              (by omega)
        have hpayloadOldFlipped : ¬ (k + (ψ - 1) < ψ) := by omega
        have hpayloadNewFlipped : ¬ (k + ψ < ψ) := by omega
        have hstateOldNotEarly : ¬ (k + (ψ - 1) + 1 < ψ) := by omega
        have hstateOldNotFrontier : k + (ψ - 1) + 1 ≠ ψ := by omega
        have hstateNewNotEarly : ¬ (k + ψ + 1 < ψ) := by omega
        have hstateNewNotFrontier : k + ψ + 1 ≠ ψ := by omega
        unfold WriterTokenAt
        rw [hsame]
        simpa [WriterTokenAt, hpayloadOldFlipped, hpayloadNewFlipped,
          hstateOldNotEarly, hstateOldNotFrontier, hstateNewNotEarly,
          hstateNewNotFrontier] using htokens k hk
  · intro x hx
    rw [(hlabelBitAfter (genericWriterPos hp x)).1]
    exact hlabel x hx
  · intro i
    rw [(hlabelBitAfter i).2]
    exact hbit i

/-- The first `steps` edges of the counterclockwise flag-one action.  The
source of each interaction is immediately left of the current frontier; the
last edge is the source-terminal to target-zero boundary. -/
def writerMoveFlipSchedule {ψ : Nat} (hψ : 0 < ψ) :
    Nat → DetSchedule (2 * ψ)
  | 0 => []
  | steps + 1 =>
      writerMoveFlipSchedule hψ steps ++
        [genericWriterPos hψ
          (ψ + (ψ - (steps + 1) - 1) - 1)]

/-- Starting from the terminal-action base case, the recursive physical
schedule executes any requested prefix of the backward sweep.  At
`steps = ψ-1`, all `ψ` payload components have complemented flags and are in
`depart`, with no action propagated across the group boundary. -/
theorem writerMoveFlipSchedule_reaches {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (steps : Nat) (hsteps : steps ≤ ψ - 1)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hstate : WriterMoveFlipSweepState (by omega) C payload 1)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := applySchedule (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (writerMoveFlipSchedule (by omega) steps)
    WriterMoveFlipSweepState (by omega) D payload (steps + 1) ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧ WriterBitFrame reference D := by
  induction steps generalizing C with
  | zero =>
      simpa [writerMoveFlipSchedule, applySchedule] using
        And.intro hstate (And.intro hclean (And.intro hlabel hbit))
  | succ steps ih =>
      have hprev := ih (C := C) (by omega) hstate hclean hlabel hbit
      let hp : 0 < ψ := by omega
      let C₁ := applySchedule (genericWriterRing hp)
        (writeSeqPersistentComparisonTransportLifecycle hp) C
        (writerMoveFlipSchedule hp steps)
      change WriterMoveFlipSweepState hp C₁ payload (steps + 1) ∧
        (∀ i, WriterTransportCleanFrame (C₁ i)) ∧
        WriterLabelFrame hp C₁ ∧ WriterBitFrame reference C₁ at hprev
      rcases hprev with ⟨hstate₁, hclean₁, hlabel₁, hbit₁⟩
      have hnext :
          let frontier := ψ - (steps + 1) - 1
          let D := stepConfig (genericWriterRing hp)
            (writeSeqPersistentComparisonTransportLifecycle hp) C₁
            (genericWriterPos hp (ψ + frontier - 1))
          WriterMoveFlipSweepState hp D payload (steps + 1 + 1) ∧
            (∀ i, WriterTransportCleanFrame (D i)) ∧
            WriterLabelFrame hp D ∧ WriterBitFrame reference D := by
        by_cases hnonzero : steps + 1 < ψ - 1
        · simpa using WriterMoveFlipSweepState.nonzero_step hψ C₁ reference
            payload (steps + 1) hnonzero hpayload hstate₁ hclean₁
            hlabel₁ hbit₁
        · have hterminal : steps + 1 = ψ - 1 := by omega
          have hstateTerminal :
              WriterMoveFlipSweepState hp C₁ payload (ψ - 1) := by
            simpa [hterminal] using hstate₁
          have hfrontierZero : ψ - (ψ - 1) - 1 = 0 := by omega
          have hprocessedDone : ψ - 1 + 1 = ψ := by omega
          rw [hterminal, hfrontierZero, Nat.add_zero, hprocessedDone]
          exact WriterMoveFlipSweepState.zero_step hψ C₁ reference payload
            hpayload hstateTerminal hclean₁ hlabel₁ hbit₁
      dsimp only
      rw [writerMoveFlipSchedule, applySchedule_append]
      simpa [applySchedule, C₁, hp] using hnext

/-- The complete physical schedule for the equal, common-flag-one ruler
action: compare through the proper prefix, select `move_flip` at the terminal
component, then execute the counterclockwise sweep through label zero. -/
def writerEqualFlagOneActionSchedule {ψ : Nat} (hψ : 0 < ψ) :
    DetSchedule (2 * ψ) :=
  writerEqualPrefixSchedule hψ (ψ - 1) ++
    [genericWriterPos hψ (ψ + (ψ - 1) - 1)] ++
    writerMoveFlipSchedule hψ (ψ - 1)

/-- **Arbitrary-width equal flag-one action.**  From an aligned idle target
writer whose bits all compare equal, the concrete schedule executes the
paper's flag-one branch: every payload flag is complemented, every component
retires in `depart`, and the clean, label, and physical-bit frames survive.
This is the first complete arbitrary-`ψ` comparison/action lifecycle. -/
theorem writerEqualFlagOneActionSchedule_reaches {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hcompare : ∀ k, k < ψ →
      checkBitWS (reference (genericWriterPos (by omega) (ψ + k))).bit
        (payload k).bit = .equal)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = 1)
    (hstate : WriterEqualPrefixState (by omega) C payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := applySchedule (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (writerEqualFlagOneActionSchedule (by omega))
    WriterMoveFlipSweepState (by omega) D payload ψ ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧ WriterBitFrame reference D := by
  let hp : 0 < ψ := by omega
  let ring := genericWriterRing hp
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let forward := writerEqualPrefixSchedule hp (ψ - 1)
  let terminal := genericWriterPos hp (ψ + (ψ - 1) - 1)
  let backward := writerMoveFlipSchedule hp (ψ - 1)
  let C₁ := applySchedule ring T C forward
  have hforward := writerEqualPrefixSchedule_reaches hψ C reference payload
    (ψ - 1) (by omega) hpayload (fun k hk => hcompare k (by omega))
    hstate hclean hlabel hbit
  change WriterEqualPrefixState hp C₁ payload (ψ - 1) ∧
    (∀ i, WriterTransportCleanFrame (C₁ i)) ∧
    WriterLabelFrame hp C₁ ∧ WriterBitFrame reference C₁ at hforward
  rcases hforward with ⟨hstate₁, hclean₁, hlabel₁, hbit₁⟩
  let C₂ := stepConfig ring T C₁ terminal
  have hterminal := WriterEqualPrefixState.terminal_one_step hψ C₁ reference
    payload hpayload hcompare (hpayloadFlag (ψ - 1) (by omega)) hstate₁
    hclean₁ hlabel₁ hbit₁
  change WriterMoveFlipSweepState hp C₂ payload 1 ∧
    (∀ i, WriterTransportCleanFrame (C₂ i)) ∧
    WriterLabelFrame hp C₂ ∧ WriterBitFrame reference C₂ at hterminal
  rcases hterminal with ⟨hstate₂, hclean₂, hlabel₂, hbit₂⟩
  have hbackward := writerMoveFlipSchedule_reaches hψ C₂ reference payload
    (ψ - 1) (by omega) hpayload hstate₂ hclean₂ hlabel₂ hbit₂
  let D := applySchedule ring T C₂ backward
  change WriterMoveFlipSweepState hp D payload (ψ - 1 + 1) ∧
    (∀ i, WriterTransportCleanFrame (D i)) ∧
    WriterLabelFrame hp D ∧ WriterBitFrame reference D at hbackward
  have hdone : ψ - 1 + 1 = ψ := by omega
  rw [hdone] at hbackward
  change WriterMoveFlipSweepState hp
      (applySchedule ring T C (writerEqualFlagOneActionSchedule hp))
      payload ψ ∧
    (∀ i, WriterTransportCleanFrame
      (applySchedule ring T C (writerEqualFlagOneActionSchedule hp) i)) ∧
    WriterLabelFrame hp
      (applySchedule ring T C (writerEqualFlagOneActionSchedule hp)) ∧
    WriterBitFrame reference
      (applySchedule ring T C (writerEqualFlagOneActionSchedule hp))
  rw [writerEqualFlagOneActionSchedule, applySchedule_append,
    applySchedule_append]
  simpa [applySchedule, forward, terminal, backward, C₁, C₂, D, ring, T]
    using hbackward

/-- The first complete ruler-processing schedule combines one canonical
writer block crossing with the equal, flag-one action at target group one. -/
def writerFirstEqualFlagOneSchedule {ψ : Nat} (hψ : 0 < ψ) :
    DetSchedule (2 * ψ) :=
  writerBlockTransportSchedule (genericWriterRing hψ)
      (genericWriterStart hψ) ψ ++
    writerEqualFlagOneActionSchedule hψ

/-- A clean complete writer at source group zero can physically cross into
target group one and execute the entire equal, flag-one ruler action under one
repaired lifecycle.  The output has all payload flags complemented and all
components in `depart`; extending the history to target two now requires only
the separate larger-ring relocation layer. -/
theorem writerFirstEqualFlagOneSchedule_reaches {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hcompare : ∀ k, k < ψ →
      checkBitWS (reference (genericWriterPos (by omega) (ψ + k))).bit
        (payload k).bit = .equal)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = 1)
    (hstate : WriterRoundState (by omega) C payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := applySchedule (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (writerFirstEqualFlagOneSchedule (by omega))
    WriterMoveFlipSweepState (by omega) D payload ψ ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧ WriterBitFrame reference D := by
  let hp : 0 < ψ := by omega
  let ring := genericWriterRing hp
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let transport := writerBlockTransportSchedule ring
    (genericWriterStart hp) ψ
  let C₁ := applySchedule ring T C transport
  have htransport := writerBlockTransportSchedule_from_zero hp C payload
    reference hpayload hstate hclean hlabel hbit
  change WriterRoundState hp C₁ payload ψ ∧
    (∀ i, WriterTransportCleanFrame (C₁ i)) ∧
    WriterLabelFrame hp C₁ ∧ WriterBitFrame reference C₁ at htransport
  rcases htransport with ⟨hround, hclean₁, hlabel₁, hbit₁⟩
  have hequal : WriterEqualPrefixState hp C₁ payload 0 :=
    WriterRoundState.toEqualPrefix hp C₁ payload hround
  have haction := writerEqualFlagOneActionSchedule_reaches hψ C₁ reference
    payload hpayload hcompare hpayloadFlag hequal hclean₁ hlabel₁ hbit₁
  change WriterMoveFlipSweepState hp
      (applySchedule ring T C (writerFirstEqualFlagOneSchedule hp))
      payload ψ ∧
    (∀ i, WriterTransportCleanFrame
      (applySchedule ring T C (writerFirstEqualFlagOneSchedule hp) i)) ∧
    WriterLabelFrame hp
      (applySchedule ring T C (writerFirstEqualFlagOneSchedule hp)) ∧
    WriterBitFrame reference
      (applySchedule ring T C (writerFirstEqualFlagOneSchedule hp))
  rw [writerFirstEqualFlagOneSchedule, applySchedule_append]
  simpa [transport, C₁, ring, T] using haction

/-! ## Arbitrary-width flag-zero binary increment

The other equal branch starts with common writer flag zero and performs a
right-to-left binary increment.  A carry reaches component `k` exactly when
every less-significant component to its right was one in the reference target
group.  This semantic predicate simultaneously determines the frontier
command and the final physical-bit toggle, avoiding an unverified abstraction
over the incremented group ID.
-/

/-- The binary carry reaches label `k` precisely when all labels strictly to
its right contain one in the target group before the action begins. -/
def WriterCarryReaches {ψ : Nat} (hψ : 0 < ψ)
    (reference : Fin (2 * ψ) → AgentState ψ) (k : Nat) : Prop :=
  ∀ t, k < t → t < ψ →
    (reference (genericWriterPos hψ (ψ + t))).bit = true

/-- No component lies to the right of the terminal label, so the incoming
carry always reaches it. -/
theorem writerCarryReaches_terminal {ψ : Nat} (hψ : 0 < ψ)
    (reference : Fin (2 * ψ) → AgentState ψ) :
    WriterCarryReaches hψ reference (ψ - 1) := by
  intro t hkt ht
  omega

/-- Moving one label left extends the carry condition by exactly the bit at
the old frontier.  This is the structural recurrence behind the executable
increment sweep. -/
theorem writerCarryReaches_pred_iff {ψ : Nat} (hψ : 0 < ψ)
    (reference : Fin (2 * ψ) → AgentState ψ) (k : Nat)
    (hkPos : 0 < k) (hk : k < ψ) :
    WriterCarryReaches hψ reference (k - 1) ↔
      (reference (genericWriterPos hψ (ψ + k))).bit = true ∧
        WriterCarryReaches hψ reference k := by
  constructor
  · intro h
    constructor
    · exact h k (by omega) hk
    · intro t hkt ht
      exact h t (by omega) ht
  · rintro ⟨hkbit, htail⟩ t hpred ht
    by_cases htk : t = k
    · subst t
      exact hkbit
    · exact htail t (by omega) ht

/-- The command handed left from label `k`: continue the carry exactly while
all less-significant reference bits are one. -/
noncomputable def writerIncrementCommand {ψ : Nat} (hψ : 0 < ψ)
    (reference : Fin (2 * ψ) → AgentState ψ) (k : Nat) : WriteState := by
  classical
  exact if WriterCarryReaches hψ reference k then .increment_group
    else .move_flip

/-- The final target bit at label `k`: toggle it iff the incoming binary carry
reaches that label. -/
noncomputable def writerIncrementedBit {ψ : Nat} (hψ : 0 < ψ)
    (reference : Fin (2 * ψ) → AgentState ψ) (k : Nat) : Bool := by
  classical
  exact if WriterCarryReaches hψ reference k then
    !(reference (genericWriterPos hψ (ψ + k))).bit
  else (reference (genericWriterPos hψ (ψ + k))).bit

/-- The source group's physical bits remain immutable while the target group
executes its binary increment. -/
def WriterSourceBitFrame {ψ : Nat} (hψ : 0 < ψ)
    (reference C : Fin (2 * ψ) → AgentState ψ) : Prop :=
  ∀ k, k < ψ →
    (C (genericWriterPos hψ k)).bit =
      (reference (genericWriterPos hψ k)).bit

/-- After `processed` rightmost components have retired, their payload flags
are complemented.  An unprocessed prefix remains in `equal`; its frontier
carries `increment_group` exactly while the reference suffix is all one, and
otherwise carries `move_flip`.  Processed physical bits equal the exact binary
increment result, while unprocessed bits retain the reference value. -/
def WriterIncrementSweepState {ψ : Nat} (hψ : 0 < ψ)
    (reference C : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (processed : Nat) : Prop :=
  1 ≤ processed ∧ processed ≤ ψ ∧
    (C (genericWriterPos hψ (ψ - 1))).path3 = none ∧
    ∀ k, k < ψ →
      WriterTokenAt C (genericWriterPos hψ (ψ + k))
        (if k + processed < ψ then payload k
          else { payload k with flag := 1 - (payload k).flag })
        (if k + processed + 1 < ψ then .equal
          else if k + processed + 1 = ψ then
            writerIncrementCommand hψ reference k
          else .depart) ∧
      (C (genericWriterPos hψ (ψ + k))).bit =
        if k + processed < ψ then
          (reference (genericWriterPos hψ (ψ + k))).bit
        else writerIncrementedBit hψ reference k

/-- Terminal equality with common flag zero establishes the exact base of the
binary-increment sweep.  The terminal bit toggles, the predecessor receives
`increment_group` iff that terminal reference bit was one, and source bits,
clean frames, and labels remain intact. -/
theorem WriterEqualPrefixState.terminal_zero_step {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hcompare : ∀ k, k < ψ →
      checkBitWS (reference (genericWriterPos (by omega) (ψ + k))).bit
        (payload k).bit = .equal)
    (hterminalFlag : (payload (ψ - 1)).flag = 0)
    (hstate : WriterEqualPrefixState (by omega) C payload (ψ - 1))
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := stepConfig (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (genericWriterPos (by omega) (ψ + (ψ - 1) - 1))
    WriterIncrementSweepState (by omega) reference D payload 1 ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧
      WriterSourceBitFrame (by omega) reference D := by
  classical
  rcases hstate with ⟨_, hboundary, htokens⟩
  let hp : 0 < ψ := by omega
  let ring := genericWriterRing hp
  let e := genericWriterPos hp (ψ + (ψ - 1) - 1)
  let j := genericWriterPos hp (ψ + (ψ - 1))
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let D := stepConfig ring T C e
  have heIndex : ψ + (ψ - 1) - 1 = ψ + (ψ - 2) := by omega
  have hj : ring.rightNeighbor e = j := by
    dsimp only [ring, e, j]
    rw [rightNeighbor_genericWriterPos]
    apply congrArg (genericWriterPos hp)
    omega
  have hleftToken := htokens (ψ - 2) (by omega)
  have hrightToken := htokens (ψ - 1) (by omega)
  have hleftPath : (C e).path3 = some (payload (ψ - 2)) := by
    simpa [e, WriterTokenAt, heIndex] using hleftToken.1
  have hleftState : (C e).write_state = .equal := by
    have hprefix : ψ - 2 < ψ - 1 := by omega
    simpa [e, WriterTokenAt, heIndex, hprefix] using hleftToken.2
  have hrightPath : (C j).path3 = some (payload (ψ - 1)) := by
    simpa [j, WriterTokenAt] using hrightToken.1
  have hrightState : (C j).write_state = .none := by
    simpa [j, WriterTokenAt] using hrightToken.2
  have hleftLabelVal : (C e).label.val = ψ - 2 := by
    calc
      (C e).label.val = (ψ + (ψ - 1) - 1) % ψ := hlabel _ (by omega)
      _ = ψ - 2 := by
        rw [heIndex, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hrightLabelVal : (C j).label.val = ψ - 1 := by
    calc
      (C j).label.val = (ψ + (ψ - 1)) % ψ := hlabel _ (by omega)
      _ = ψ - 1 := by
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hleftAlign : (C e).label.val = (payload (ψ - 2)).label := by
    rw [hleftLabelVal, hpayload (ψ - 2) (by omega)]
  have hrightAlign : (C j).label.val = (payload (ψ - 1)).label := by
    rw [hrightLabelVal, hpayload (ψ - 1) (by omega)]
  have hrightCompare :
      checkBitWS (C j).bit (payload (ψ - 1)).bit = .equal := by
    rw [hbit j]
    simpa [j] using hcompare (ψ - 1) (by omega)
  have hleftCompare : (C e).label.val < ψ - 1 := by
    rw [hleftLabelVal]
    omega
  have hrightTerminal : (C j).label = ⟨ψ - 1, by omega⟩ := by
    apply Fin.ext
    exact hrightLabelVal
  have hrightZero : (C j).label ≠ ⟨0, hp⟩ := by
    intro hzero
    have hv := congrArg Fin.val hzero
    simp only at hv
    rw [hrightLabelVal] at hv
    omega
  have horder : (C e).label < (C j).label := by
    change (C e).label.val < (C j).label.val
    rw [hleftLabelVal, hrightLabelVal]
    omega
  have hlocal :=
    writeSeqPersistentComparisonTransportLifecycle_equal_terminal_zero hp
      (C e) (C j) (payload (ψ - 2)) (payload (ψ - 1))
      hleftPath hrightPath hleftState hrightState hleftAlign hrightAlign
      hrightCompare hleftCompare hrightTerminal hrightZero horder
      hterminalFlag (hclean e) (hclean j)
  rcases hlocal with ⟨hleftPathAfter, hleftStateAfter, hleftLabelAfter,
    hleftBitAfter, hleftCleanAfter, hrightPathAfter, hrightStateAfter,
    hrightLabelAfter, hrightBitAfter, hrightCleanAfter⟩
  have hleftD : D e = (T (C e) (C j)).1 := by
    simp [D, stepConfig, hj]
  have hrightD : D j = (T (C e) (C j)).2 := by
    have hne : j ≠ e :=
      genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
    simp [D, stepConfig, hj, hne]
  have hframes := stepConfig_global_writer_clean_label_of_endpoint_contract
    ring (by omega) T C e hclean
    (by rw [hj]; simpa only [T] using hleftCleanAfter)
    (by rw [hj]; simpa only [T] using hrightCleanAfter)
    (by rw [hj]; simpa only [T] using hleftLabelAfter)
    (by rw [hj]; simpa only [T] using hrightLabelAfter)
  change (∀ i, WriterTransportCleanFrame (D i)) ∧
    ∀ i, (D i).label = (C i).label at hframes
  rcases hframes with ⟨hcleanAfter, hlabelAfter⟩
  have hcarryBeforeTerminal :
      WriterCarryReaches hp reference (ψ - 2) ↔
        (reference j).bit = true := by
    have hpred := writerCarryReaches_pred_iff hp reference (ψ - 1)
      (by omega) (by omega)
    rw [show ψ - 2 = ψ - 1 - 1 by omega]
    simpa [j, writerCarryReaches_terminal hp reference] using hpred
  change WriterIncrementSweepState hp reference D payload 1 ∧
    (∀ i, WriterTransportCleanFrame (D i)) ∧
    WriterLabelFrame hp D ∧ WriterSourceBitFrame hp reference D
  refine ⟨?_, hcleanAfter, ?_, ?_⟩
  · refine ⟨by omega, by omega, ?_, ?_⟩
    · have hsame : D (genericWriterPos hp (ψ - 1)) =
          C (genericWriterPos hp (ψ - 1)) := by
        apply stepConfig_eq_of_ne ring T C e
        · exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
            (by omega)
        · rw [hj]
          exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
            (by omega)
      rw [hsame]
      exact hboundary
    · intro k hk
      by_cases hkLeft : k = ψ - 2
      · subst k
        have hpayloadOriginal : ψ - 2 + 1 < ψ := by omega
        have hstateNotEarly : ¬ (ψ - 2 + 1 + 1 < ψ) := by omega
        have hstateFrontier : ψ - 2 + 1 + 1 = ψ := by omega
        unfold WriterTokenAt
        rw [show genericWriterPos hp (ψ + (ψ - 2)) = e by simp [e, heIndex]]
        rw [hleftD]
        constructor
        · constructor
          · simpa [T, hpayloadOriginal] using hleftPathAfter
          · rw [show (T (C e) (C j)).1.write_state =
                (if (C j).bit = true then .increment_group else .move_flip) by
              simpa only [T] using hleftStateAfter]
            rw [hbit j]
            simp only [hstateFrontier, if_true]
            simp [writerIncrementCommand, hcarryBeforeTerminal]
        · rw [show (T (C e) (C j)).1.bit = (C e).bit by
              simpa only [T] using hleftBitAfter]
          rw [hbit e]
          simp [hpayloadOriginal, e, heIndex]
      · by_cases hkRight : k = ψ - 1
        · subst k
          have hpayloadFlipped : ¬ (ψ - 1 + 1 < ψ) := by omega
          have hstateNotEarly : ¬ (ψ - 1 + 1 + 1 < ψ) := by omega
          have hstateNotFrontier : ψ - 1 + 1 + 1 ≠ ψ := by omega
          have hcarryTerminal := writerCarryReaches_terminal hp reference
          unfold WriterTokenAt
          rw [show genericWriterPos hp (ψ + (ψ - 1)) = j by rfl]
          rw [hrightD]
          constructor
          · simpa [T, hpayloadFlipped, hstateNotEarly,
              hstateNotFrontier] using
                And.intro hrightPathAfter hrightStateAfter
          · rw [show (T (C e) (C j)).2.bit = !(C j).bit by
                simpa only [T] using hrightBitAfter]
            rw [hbit j]
            simp [j, hpayloadFlipped, writerIncrementedBit, hcarryTerminal]
        · have hkEarly : k < ψ - 2 := by omega
          have hkPayload : k + 1 < ψ := by omega
          have hkState : k + 1 + 1 < ψ := by omega
          have hkPrefix : k < ψ - 1 := by omega
          have hsame : D (genericWriterPos hp (ψ + k)) =
              C (genericWriterPos hp (ψ + k)) := by
            apply stepConfig_eq_of_ne ring T C e
            · exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
                (by omega)
            · rw [hj]
              exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
                (by omega)
          unfold WriterTokenAt
          rw [hsame]
          constructor
          · simpa [WriterTokenAt, hkPayload, hkState, hkPrefix] using
              htokens k hk
          · rw [hbit]
            simp [hkPayload]
  · intro x hx
    rw [hlabelAfter (genericWriterPos hp x)]
    exact hlabel x hx
  · intro k hk
    have hsame : D (genericWriterPos hp k) = C (genericWriterPos hp k) := by
      apply stepConfig_eq_of_ne ring T C e
      · exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
      · rw [hj]
        exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
    rw [hsame, hbit]

/-- At a positive-label frontier, one physical edge advances the exact binary
increment sweep.  If the carry is still live the old frontier toggles its bit;
otherwise the same edge executes `move_flip`.  In both cases the predecessor
receives precisely the command determined by the reference suffix. -/
theorem WriterIncrementSweepState.nonzero_step {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (processed : Nat)
    (hprocessed : processed < ψ - 1)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hstate : WriterIncrementSweepState (by omega) reference C payload processed)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hsourceBit : WriterSourceBitFrame (by omega) reference C) :
    let frontier := ψ - processed - 1
    let D := stepConfig (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (genericWriterPos (by omega) (ψ + frontier - 1))
    WriterIncrementSweepState (by omega) reference D payload (processed + 1) ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧
      WriterSourceBitFrame (by omega) reference D := by
  classical
  rcases hstate with ⟨hprocessedPos, hprocessedLe, hboundary, htokens⟩
  let hp : 0 < ψ := by omega
  let frontier := ψ - processed - 1
  have hfrontierPos : 0 < frontier := by
    dsimp only [frontier]
    omega
  have hfrontierLt : frontier < ψ := by
    dsimp only [frontier]
    omega
  have hfrontierSum : frontier + processed + 1 = ψ := by
    dsimp only [frontier]
    omega
  let ring := genericWriterRing hp
  let e := genericWriterPos hp (ψ + frontier - 1)
  let j := genericWriterPos hp (ψ + frontier)
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let D := stepConfig ring T C e
  have heIndex : ψ + frontier - 1 = ψ + (frontier - 1) := by omega
  have hj : ring.rightNeighbor e = j := by
    dsimp only [ring, e, j]
    rw [rightNeighbor_genericWriterPos]
    apply congrArg (genericWriterPos hp)
    omega
  have hleftData := htokens (frontier - 1) (by omega)
  have hrightData := htokens frontier hfrontierLt
  have hleftPayloadOld : frontier - 1 + processed < ψ := by omega
  have hleftStateOld : frontier - 1 + processed + 1 < ψ := by omega
  have hrightPayloadOld : frontier + processed < ψ := by omega
  have hrightStateNotEarly : ¬ (frontier + processed + 1 < ψ) := by omega
  have hrightStateFrontier : frontier + processed + 1 = ψ :=
    hfrontierSum
  have hleftPath : (C e).path3 = some (payload (frontier - 1)) := by
    simpa [e, WriterTokenAt, heIndex, hleftPayloadOld] using hleftData.1.1
  have hleftState : (C e).write_state = .equal := by
    simpa [e, WriterTokenAt, heIndex, hleftStateOld] using hleftData.1.2
  have hleftBit : (C e).bit =
      (reference (genericWriterPos hp (ψ + (frontier - 1)))).bit := by
    simpa [e, heIndex, hleftPayloadOld] using hleftData.2
  have hrightPath : (C j).path3 = some (payload frontier) := by
    simpa [j, WriterTokenAt, hrightPayloadOld] using hrightData.1.1
  have hrightState : (C j).write_state =
      writerIncrementCommand hp reference frontier := by
    simpa [j, WriterTokenAt, hrightStateNotEarly,
      hrightStateFrontier] using hrightData.1.2
  have hrightBit : (C j).bit =
      (reference (genericWriterPos hp (ψ + frontier))).bit := by
    simpa [j, hrightPayloadOld] using hrightData.2
  have hleftLabelVal : (C e).label.val = frontier - 1 := by
    calc
      (C e).label.val = (ψ + frontier - 1) % ψ := hlabel _ (by omega)
      _ = frontier - 1 := by
        rw [heIndex, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hrightLabelVal : (C j).label.val = frontier := by
    calc
      (C j).label.val = (ψ + frontier) % ψ := hlabel _ (by omega)
      _ = frontier := by
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt hfrontierLt]
  have hleftAlign : (C e).label.val = (payload (frontier - 1)).label := by
    rw [hleftLabelVal, hpayload (frontier - 1) (by omega)]
  have hrightAlign : (C j).label.val = (payload frontier).label := by
    rw [hrightLabelVal, hpayload frontier hfrontierLt]
  have hleftCompare : (C e).label.val < ψ - 1 := by
    rw [hleftLabelVal]
    omega
  have hrightZero : (C j).label ≠ ⟨0, hp⟩ := by
    intro hzero
    have hv := congrArg Fin.val hzero
    simp only at hv
    rw [hrightLabelVal] at hv
    omega
  have horder : (C e).label < (C j).label := by
    change (C e).label.val < (C j).label.val
    rw [hleftLabelVal, hrightLabelVal]
    omega
  have hcarryPred := writerCarryReaches_pred_iff hp reference frontier
    hfrontierPos hfrontierLt
  have hlocal :
      let q := T (C e) (C j)
      q.1.path3 = some (payload (frontier - 1)) ∧
        q.1.write_state = writerIncrementCommand hp reference (frontier - 1) ∧
        q.1.label = (C e).label ∧ q.1.bit = (C e).bit ∧
        WriterTransportCleanFrame q.1 ∧
        q.2.path3 = some { payload frontier with
          flag := 1 - (payload frontier).flag } ∧
        q.2.write_state = .depart ∧ q.2.label = (C j).label ∧
        q.2.bit = writerIncrementedBit hp reference frontier ∧
        WriterTransportCleanFrame q.2 := by
    by_cases hcarry : WriterCarryReaches hp reference frontier
    · have hrightCommand : (C j).write_state = .increment_group := by
        simpa [writerIncrementCommand, hcarry] using hrightState
      have hraw :=
        writeSeqPersistentComparisonTransportLifecycle_increment_nonzero hp
          (C e) (C j) (payload (frontier - 1)) (payload frontier)
          hleftPath hrightPath hleftState hrightCommand hleftAlign hrightAlign
          hleftCompare hrightZero horder (hclean e) (hclean j)
      have hleftCommandEq :
          (if (C j).bit = true then .increment_group else .move_flip) =
            writerIncrementCommand hp reference (frontier - 1) := by
        rw [hrightBit]
        simp [writerIncrementCommand, hcarryPred, hcarry]
      have hrightBitEq : (!(C j).bit) =
          writerIncrementedBit hp reference frontier := by
        rw [hrightBit]
        simp [writerIncrementedBit, hcarry]
      rw [hleftCommandEq, hrightBitEq] at hraw
      simpa only [T] using hraw
    · have hrightCommand : (C j).write_state = .move_flip := by
        simpa [writerIncrementCommand, hcarry] using hrightState
      have hnotPred :
          ¬ WriterCarryReaches hp reference (frontier - 1) := by
        intro hpred
        exact hcarry (hcarryPred.mp hpred).2
      have hraw :=
        writeSeqPersistentComparisonTransportLifecycle_move_flip_nonzero hp
          (C e) (C j) (payload (frontier - 1)) (payload frontier)
          hleftPath hrightPath hleftState hrightCommand hleftAlign hrightAlign
          hleftCompare hrightZero horder (hclean e) (hclean j)
      have hleftCommandEq : .move_flip =
          writerIncrementCommand hp reference (frontier - 1) := by
        simp [writerIncrementCommand, hnotPred]
      have hrightBitEq : (C j).bit =
          writerIncrementedBit hp reference frontier := by
        rw [hrightBit]
        simp [writerIncrementedBit, hcarry]
      rw [hleftCommandEq, hrightBitEq] at hraw
      simpa only [T] using hraw
  rcases hlocal with ⟨hleftPathAfter, hleftStateAfter, hleftLabelAfter,
    hleftBitAfter, hleftCleanAfter, hrightPathAfter, hrightStateAfter,
    hrightLabelAfter, hrightBitAfter, hrightCleanAfter⟩
  have hleftD : D e = (T (C e) (C j)).1 := by
    simp [D, stepConfig, hj]
  have hrightD : D j = (T (C e) (C j)).2 := by
    have hne : j ≠ e :=
      genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
    simp [D, stepConfig, hj, hne]
  have hframes := stepConfig_global_writer_clean_label_of_endpoint_contract
    ring (by omega) T C e hclean
    (by rw [hj]; exact hleftCleanAfter)
    (by rw [hj]; exact hrightCleanAfter)
    (by rw [hj]; exact hleftLabelAfter)
    (by rw [hj]; exact hrightLabelAfter)
  change (∀ i, WriterTransportCleanFrame (D i)) ∧
    ∀ i, (D i).label = (C i).label at hframes
  rcases hframes with ⟨hcleanAfter, hlabelAfter⟩
  dsimp only
  change WriterIncrementSweepState hp reference D payload (processed + 1) ∧
    (∀ i, WriterTransportCleanFrame (D i)) ∧
    WriterLabelFrame hp D ∧ WriterSourceBitFrame hp reference D
  refine ⟨?_, hcleanAfter, ?_, ?_⟩
  · refine ⟨by omega, by omega, ?_, ?_⟩
    · have hsame : D (genericWriterPos hp (ψ - 1)) =
          C (genericWriterPos hp (ψ - 1)) := by
        apply stepConfig_eq_of_ne ring T C e
        · exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
            (by omega)
        · rw [hj]
          exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
            (by omega)
      rw [hsame]
      exact hboundary
    · intro k hk
      by_cases hkLeft : k = frontier - 1
      · subst k
        have hpayloadOriginal : frontier - 1 + (processed + 1) < ψ := by
          omega
        have hstateNotEarly :
            ¬ (frontier - 1 + (processed + 1) + 1 < ψ) := by omega
        have hstateFrontier :
            frontier - 1 + (processed + 1) + 1 = ψ := by omega
        unfold WriterTokenAt
        rw [show genericWriterPos hp (ψ + (frontier - 1)) = e by
          simp [e, heIndex]]
        rw [hleftD]
        constructor
        · simpa [hpayloadOriginal, hstateNotEarly, hstateFrontier] using
            And.intro hleftPathAfter hleftStateAfter
        · rw [hleftBitAfter, hleftBit]
          simp [hpayloadOriginal, e, heIndex]
      · by_cases hkRight : k = frontier
        · subst k
          have hpayloadFlipped :
              ¬ (frontier + (processed + 1) < ψ) := by omega
          have hstateNotEarly :
              ¬ (frontier + (processed + 1) + 1 < ψ) := by omega
          have hstateNotFrontier :
              frontier + (processed + 1) + 1 ≠ ψ := by omega
          unfold WriterTokenAt
          rw [show genericWriterPos hp (ψ + frontier) = j by rfl]
          rw [hrightD]
          constructor
          · simpa [hpayloadFlipped, hstateNotEarly,
              hstateNotFrontier] using
                And.intro hrightPathAfter hrightStateAfter
          · simpa [hpayloadFlipped] using hrightBitAfter
        · have hsame : D (genericWriterPos hp (ψ + k)) =
              C (genericWriterPos hp (ψ + k)) := by
            apply stepConfig_eq_of_ne ring T C e
            · exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
                (by omega)
            · rw [hj]
              exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
                (by omega)
          unfold WriterTokenAt
          rw [hsame]
          by_cases hkEarly : k < frontier
          · have hkBefore : k < frontier - 1 := by omega
            have hpayloadOld : k + processed < ψ := by omega
            have hpayloadNew : k + (processed + 1) < ψ := by omega
            have hstateOld : k + processed + 1 < ψ := by omega
            have hstateNew : k + (processed + 1) + 1 < ψ := by omega
            constructor
            · simpa [WriterTokenAt, hpayloadOld, hpayloadNew,
                hstateOld, hstateNew] using htokens k hk |>.1
            · simpa [hpayloadOld, hpayloadNew] using htokens k hk |>.2
          · have hkAfter : frontier < k := by omega
            have hpayloadOld : ¬ (k + processed < ψ) := by omega
            have hpayloadNew : ¬ (k + (processed + 1) < ψ) := by omega
            have hstateOldEarly : ¬ (k + processed + 1 < ψ) := by omega
            have hstateOldFrontier : k + processed + 1 ≠ ψ := by omega
            have hstateNewEarly :
                ¬ (k + (processed + 1) + 1 < ψ) := by omega
            have hstateNewFrontier :
                k + (processed + 1) + 1 ≠ ψ := by omega
            constructor
            · simpa [WriterTokenAt, hpayloadOld, hpayloadNew,
                hstateOldEarly, hstateOldFrontier, hstateNewEarly,
                hstateNewFrontier] using htokens k hk |>.1
            · simpa [hpayloadOld, hpayloadNew] using htokens k hk |>.2
  · intro x hx
    rw [hlabelAfter (genericWriterPos hp x)]
    exact hlabel x hx
  · intro k hk
    have hsame : D (genericWriterPos hp k) = C (genericWriterPos hp k) := by
      apply stepConfig_eq_of_ne ring T C e
      · exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
      · rw [hj]
        exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
    rw [hsame]
    exact hsourceBit k hk

/-- At label zero the final action edge retires the frontier without sending a
command across the group boundary.  It toggles the zero-label bit exactly when
the reference suffix is all one, completing the exact binary increment and
the all-component flag complement. -/
theorem WriterIncrementSweepState.zero_step {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hstate : WriterIncrementSweepState (by omega) reference C payload (ψ - 1))
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hsourceBit : WriterSourceBitFrame (by omega) reference C) :
    let D := stepConfig (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (genericWriterPos (by omega) (ψ - 1))
    WriterIncrementSweepState (by omega) reference D payload ψ ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧
      WriterSourceBitFrame (by omega) reference D := by
  classical
  rcases hstate with ⟨_, _, hboundary, htokens⟩
  let hp : 0 < ψ := by omega
  let ring := genericWriterRing hp
  let e := genericWriterPos hp (ψ - 1)
  let j := genericWriterPos hp ψ
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let D := stepConfig ring T C e
  have hj : ring.rightNeighbor e = j := by
    dsimp only [ring, e, j]
    rw [rightNeighbor_genericWriterPos]
    congr 2
    omega
  have hrightData := htokens 0 (by omega)
  have hpayloadOld : ψ - 1 < ψ := by omega
  have hstateNotEarly : ¬ (ψ - 1 + 1 < ψ) := by omega
  have hstateFrontier : ψ - 1 + 1 = ψ := by omega
  have hleftPath : (C e).path3 = none := by
    simpa [e] using hboundary
  have hrightPath : (C j).path3 = some (payload 0) := by
    simpa [j, WriterTokenAt, hpayloadOld] using hrightData.1.1
  have hrightState : (C j).write_state =
      writerIncrementCommand hp reference 0 := by
    simpa [j, WriterTokenAt, hstateNotEarly, hstateFrontier] using
      hrightData.1.2
  have hrightBit : (C j).bit =
      (reference (genericWriterPos hp ψ)).bit := by
    simpa [j, hpayloadOld] using hrightData.2
  have hrightLabelVal : (C j).label.val = 0 := by
    calc
      (C j).label.val = ψ % ψ := hlabel ψ (by omega)
      _ = 0 := Nat.mod_self ψ
  have hrightZero : (C j).label = ⟨0, hp⟩ := by
    apply Fin.ext
    exact hrightLabelVal
  have hrightAlign : (C j).label.val = (payload 0).label := by
    rw [hrightLabelVal, hpayload 0 (by omega)]
  have hlocal :
      let q := T (C e) (C j)
      q.1.path3 = none ∧ q.1.write_state = .none ∧
        q.1.label = (C e).label ∧ q.1.bit = (C e).bit ∧
        WriterTransportCleanFrame q.1 ∧
        q.2.path3 = some { payload 0 with flag := 1 - (payload 0).flag } ∧
        q.2.write_state = .depart ∧ q.2.label = (C j).label ∧
        q.2.bit = writerIncrementedBit hp reference 0 ∧
        WriterTransportCleanFrame q.2 := by
    by_cases hcarry : WriterCarryReaches hp reference 0
    · have hrightCommand : (C j).write_state = .increment_group := by
        simpa [writerIncrementCommand, hcarry] using hrightState
      have hraw :=
        writeSeqPersistentComparisonTransportLifecycle_increment_zero hp
          (C e) (C j) (payload 0) hleftPath hrightPath hrightCommand
          hrightZero hrightAlign (hclean e) (hclean j)
      have hrightBitEq : (!(C j).bit) =
          writerIncrementedBit hp reference 0 := by
        rw [hrightBit]
        simp [writerIncrementedBit, hcarry]
      rw [hrightBitEq] at hraw
      simpa only [T] using hraw
    · have hrightCommand : (C j).write_state = .move_flip := by
        simpa [writerIncrementCommand, hcarry] using hrightState
      have hraw :=
        writeSeqPersistentComparisonTransportLifecycle_move_flip_zero hp
          (C e) (C j) (payload 0) hleftPath hrightPath hrightCommand
          hrightZero hrightAlign (hclean e) (hclean j)
      have hrightBitEq : (C j).bit =
          writerIncrementedBit hp reference 0 := by
        rw [hrightBit]
        simp [writerIncrementedBit, hcarry]
      rw [hrightBitEq] at hraw
      simpa only [T] using hraw
  rcases hlocal with ⟨hleftPathAfter, hleftStateAfter, hleftLabelAfter,
    hleftBitAfter, hleftCleanAfter, hrightPathAfter, hrightStateAfter,
    hrightLabelAfter, hrightBitAfter, hrightCleanAfter⟩
  have hleftD : D e = (T (C e) (C j)).1 := by
    simp [D, stepConfig, hj]
  have hrightD : D j = (T (C e) (C j)).2 := by
    have hne : j ≠ e :=
      genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
    simp [D, stepConfig, hj, hne]
  have hframes := stepConfig_global_writer_clean_label_of_endpoint_contract
    ring (by omega) T C e hclean
    (by rw [hj]; exact hleftCleanAfter)
    (by rw [hj]; exact hrightCleanAfter)
    (by rw [hj]; exact hleftLabelAfter)
    (by rw [hj]; exact hrightLabelAfter)
  change (∀ i, WriterTransportCleanFrame (D i)) ∧
    ∀ i, (D i).label = (C i).label at hframes
  rcases hframes with ⟨hcleanAfter, hlabelAfter⟩
  change WriterIncrementSweepState hp reference D payload ψ ∧
    (∀ i, WriterTransportCleanFrame (D i)) ∧
    WriterLabelFrame hp D ∧ WriterSourceBitFrame hp reference D
  refine ⟨?_, hcleanAfter, ?_, ?_⟩
  · refine ⟨by omega, by omega, ?_, ?_⟩
    · change (D e).path3 = none
      rw [hleftD]
      exact hleftPathAfter
    · intro k hk
      by_cases hkZero : k = 0
      · subst k
        have hpayloadFlipped : ¬ (ψ < ψ) := by omega
        have hstateNotEarlyNew : ¬ (ψ + 1 < ψ) := by omega
        have hstateNotFrontierNew : ψ + 1 ≠ ψ := by omega
        unfold WriterTokenAt
        rw [show genericWriterPos hp (ψ + 0) = j by simp [j]]
        rw [hrightD]
        constructor
        · simpa [hpayloadFlipped, hstateNotEarlyNew,
            hstateNotFrontierNew] using
              And.intro hrightPathAfter hrightStateAfter
        · simpa [hpayloadFlipped, j] using hrightBitAfter
      · have hkPos : 0 < k := by omega
        have hsame : D (genericWriterPos hp (ψ + k)) =
            C (genericWriterPos hp (ψ + k)) := by
          apply stepConfig_eq_of_ne ring T C e
          · exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
              (by omega)
          · rw [hj]
            exact genericWriterPos_ne_of_lt hp (by omega) (by omega)
              (by omega)
        have hpayloadOldFlipped : ¬ (k + (ψ - 1) < ψ) := by omega
        have hpayloadNewFlipped : ¬ (k + ψ < ψ) := by omega
        have hstateOldNotEarly : ¬ (k + (ψ - 1) + 1 < ψ) := by omega
        have hstateOldNotFrontier : k + (ψ - 1) + 1 ≠ ψ := by omega
        have hstateNewNotEarly : ¬ (k + ψ + 1 < ψ) := by omega
        have hstateNewNotFrontier : k + ψ + 1 ≠ ψ := by omega
        unfold WriterTokenAt
        rw [hsame]
        constructor
        · simpa [WriterTokenAt, hpayloadOldFlipped, hpayloadNewFlipped,
            hstateOldNotEarly, hstateOldNotFrontier, hstateNewNotEarly,
            hstateNewNotFrontier] using htokens k hk |>.1
        · simpa [hpayloadOldFlipped, hpayloadNewFlipped] using
            htokens k hk |>.2
  · intro x hx
    rw [hlabelAfter (genericWriterPos hp x)]
    exact hlabel x hx
  · intro k hk
    by_cases hkTerminal : k = ψ - 1
    · subst k
      change (D e).bit = (reference e).bit
      rw [hleftD, hleftBitAfter]
      simpa [e] using hsourceBit (ψ - 1) (by omega)
    · have hsame : D (genericWriterPos hp k) = C (genericWriterPos hp k) := by
        apply stepConfig_eq_of_ne ring T C e
        · exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
        · rw [hj]
          exact genericWriterPos_ne_of_lt hp (by omega) (by omega) (by omega)
      rw [hsame]
      exact hsourceBit k hk

/-- The flag-zero action uses the same counterclockwise edge list as
`move_flip`; only the command and physical-bit effect differ.  The induction
therefore reuses `writerMoveFlipSchedule` and carries the exact binary result. -/
theorem writerIncrementSchedule_reaches {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info) (steps : Nat) (hsteps : steps ≤ ψ - 1)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hstate : WriterIncrementSweepState (by omega) reference C payload 1)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hsourceBit : WriterSourceBitFrame (by omega) reference C) :
    let D := applySchedule (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (writerMoveFlipSchedule (by omega) steps)
    WriterIncrementSweepState (by omega) reference D payload (steps + 1) ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧
      WriterSourceBitFrame (by omega) reference D := by
  induction steps generalizing C with
  | zero =>
      simpa [writerMoveFlipSchedule, applySchedule] using
        And.intro hstate
          (And.intro hclean (And.intro hlabel hsourceBit))
  | succ steps ih =>
      have hprev := ih (C := C) (by omega) hstate hclean hlabel hsourceBit
      let hp : 0 < ψ := by omega
      let C₁ := applySchedule (genericWriterRing hp)
        (writeSeqPersistentComparisonTransportLifecycle hp) C
        (writerMoveFlipSchedule hp steps)
      change WriterIncrementSweepState hp reference C₁ payload (steps + 1) ∧
        (∀ i, WriterTransportCleanFrame (C₁ i)) ∧
        WriterLabelFrame hp C₁ ∧ WriterSourceBitFrame hp reference C₁ at hprev
      rcases hprev with ⟨hstate₁, hclean₁, hlabel₁, hsourceBit₁⟩
      have hnext :
          let frontier := ψ - (steps + 1) - 1
          let D := stepConfig (genericWriterRing hp)
            (writeSeqPersistentComparisonTransportLifecycle hp) C₁
            (genericWriterPos hp (ψ + frontier - 1))
          WriterIncrementSweepState hp reference D payload (steps + 1 + 1) ∧
            (∀ i, WriterTransportCleanFrame (D i)) ∧
            WriterLabelFrame hp D ∧ WriterSourceBitFrame hp reference D := by
        by_cases hnonzero : steps + 1 < ψ - 1
        · simpa using WriterIncrementSweepState.nonzero_step hψ C₁ reference
            payload (steps + 1) hnonzero hpayload hstate₁ hclean₁
            hlabel₁ hsourceBit₁
        · have hterminal : steps + 1 = ψ - 1 := by omega
          have hstateTerminal :
              WriterIncrementSweepState hp reference C₁ payload (ψ - 1) := by
            simpa [hterminal] using hstate₁
          have hfrontierZero : ψ - (ψ - 1) - 1 = 0 := by omega
          have hprocessedDone : ψ - 1 + 1 = ψ := by omega
          rw [hterminal, hfrontierZero, Nat.add_zero, hprocessedDone]
          exact WriterIncrementSweepState.zero_step hψ C₁ reference payload
            hpayload hstateTerminal hclean₁ hlabel₁ hsourceBit₁
      dsimp only
      rw [writerMoveFlipSchedule, applySchedule_append]
      simpa [applySchedule, C₁, hp] using hnext

/-- The complete physical schedule for the equal, common-flag-zero branch.
Its edge list matches the flag-one action, but the terminal and backward
contracts execute a binary carry and expose the incremented target bits. -/
def writerEqualFlagZeroActionSchedule {ψ : Nat} (hψ : 0 < ψ) :
    DetSchedule (2 * ψ) :=
  writerEqualPrefixSchedule hψ (ψ - 1) ++
    [genericWriterPos hψ (ψ + (ψ - 1) - 1)] ++
    writerMoveFlipSchedule hψ (ψ - 1)

/-- **Arbitrary-width equal flag-zero action.**  The actual ring schedule
compares every component, selects the terminal increment, and executes its
entire backward carry.  Every payload flag is complemented, every writer
component retires, and target physical bits equal the exact binary successor
defined by `writerIncrementedBit`; source bits, labels, and clean frames remain
unchanged. -/
theorem writerEqualFlagZeroActionSchedule_reaches {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hcompare : ∀ k, k < ψ →
      checkBitWS (reference (genericWriterPos (by omega) (ψ + k))).bit
        (payload k).bit = .equal)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = 0)
    (hstate : WriterEqualPrefixState (by omega) C payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := applySchedule (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (writerEqualFlagZeroActionSchedule (by omega))
    WriterIncrementSweepState (by omega) reference D payload ψ ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧
      WriterSourceBitFrame (by omega) reference D := by
  let hp : 0 < ψ := by omega
  let ring := genericWriterRing hp
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let forward := writerEqualPrefixSchedule hp (ψ - 1)
  let terminal := genericWriterPos hp (ψ + (ψ - 1) - 1)
  let backward := writerMoveFlipSchedule hp (ψ - 1)
  let C₁ := applySchedule ring T C forward
  have hforward := writerEqualPrefixSchedule_reaches hψ C reference payload
    (ψ - 1) (by omega) hpayload (fun k hk => hcompare k (by omega))
    hstate hclean hlabel hbit
  change WriterEqualPrefixState hp C₁ payload (ψ - 1) ∧
    (∀ i, WriterTransportCleanFrame (C₁ i)) ∧
    WriterLabelFrame hp C₁ ∧ WriterBitFrame reference C₁ at hforward
  rcases hforward with ⟨hstate₁, hclean₁, hlabel₁, hbit₁⟩
  let C₂ := stepConfig ring T C₁ terminal
  have hterminal := WriterEqualPrefixState.terminal_zero_step hψ C₁ reference
    payload hpayload hcompare (hpayloadFlag (ψ - 1) (by omega)) hstate₁
    hclean₁ hlabel₁ hbit₁
  change WriterIncrementSweepState hp reference C₂ payload 1 ∧
    (∀ i, WriterTransportCleanFrame (C₂ i)) ∧
    WriterLabelFrame hp C₂ ∧ WriterSourceBitFrame hp reference C₂ at hterminal
  rcases hterminal with ⟨hstate₂, hclean₂, hlabel₂, hsourceBit₂⟩
  have hbackward := writerIncrementSchedule_reaches hψ C₂ reference payload
    (ψ - 1) (by omega) hpayload hstate₂ hclean₂ hlabel₂ hsourceBit₂
  let D := applySchedule ring T C₂ backward
  change WriterIncrementSweepState hp reference D payload (ψ - 1 + 1) ∧
    (∀ i, WriterTransportCleanFrame (D i)) ∧
    WriterLabelFrame hp D ∧ WriterSourceBitFrame hp reference D at hbackward
  have hdone : ψ - 1 + 1 = ψ := by omega
  rw [hdone] at hbackward
  change WriterIncrementSweepState hp reference
      (applySchedule ring T C (writerEqualFlagZeroActionSchedule hp))
      payload ψ ∧
    (∀ i, WriterTransportCleanFrame
      (applySchedule ring T C (writerEqualFlagZeroActionSchedule hp) i)) ∧
    WriterLabelFrame hp
      (applySchedule ring T C (writerEqualFlagZeroActionSchedule hp)) ∧
    WriterSourceBitFrame hp reference
      (applySchedule ring T C (writerEqualFlagZeroActionSchedule hp))
  rw [writerEqualFlagZeroActionSchedule, applySchedule_append,
    applySchedule_append]
  simpa [applySchedule, forward, terminal, backward, C₁, C₂, D, ring, T]
    using hbackward

/-- The first target-one flag-zero schedule combines canonical transport with
the exact equal/increment action. -/
def writerFirstEqualFlagZeroSchedule {ψ : Nat} (hψ : 0 < ψ) :
    DetSchedule (2 * ψ) :=
  writerBlockTransportSchedule (genericWriterRing hψ)
      (genericWriterStart hψ) ψ ++
    writerEqualFlagZeroActionSchedule hψ

/-- A common-flag-zero writer can cross from source group zero into target
group one and execute the complete equal binary increment under one lifecycle.
This is the arbitrary-width physical companion of the flag-one theorem. -/
theorem writerFirstEqualFlagZeroSchedule_reaches {ψ : Nat} (hψ : 1 < ψ)
    (C reference : Fin (2 * ψ) → AgentState ψ)
    (payload : Nat → Path3Info)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hcompare : ∀ k, k < ψ →
      checkBitWS (reference (genericWriterPos (by omega) (ψ + k))).bit
        (payload k).bit = .equal)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = 0)
    (hstate : WriterRoundState (by omega) C payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame (C i))
    (hlabel : WriterLabelFrame (by omega) C)
    (hbit : WriterBitFrame reference C) :
    let D := applySchedule (genericWriterRing (by omega))
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (writerFirstEqualFlagZeroSchedule (by omega))
    WriterIncrementSweepState (by omega) reference D payload ψ ∧
      (∀ i, WriterTransportCleanFrame (D i)) ∧
      WriterLabelFrame (by omega) D ∧
      WriterSourceBitFrame (by omega) reference D := by
  let hp : 0 < ψ := by omega
  let ring := genericWriterRing hp
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let transport := writerBlockTransportSchedule ring
    (genericWriterStart hp) ψ
  let C₁ := applySchedule ring T C transport
  have htransport := writerBlockTransportSchedule_from_zero hp C payload
    reference hpayload hstate hclean hlabel hbit
  change WriterRoundState hp C₁ payload ψ ∧
    (∀ i, WriterTransportCleanFrame (C₁ i)) ∧
    WriterLabelFrame hp C₁ ∧ WriterBitFrame reference C₁ at htransport
  rcases htransport with ⟨hround, hclean₁, hlabel₁, hbit₁⟩
  have hequal : WriterEqualPrefixState hp C₁ payload 0 :=
    WriterRoundState.toEqualPrefix hp C₁ payload hround
  have haction := writerEqualFlagZeroActionSchedule_reaches hψ C₁ reference
    payload hpayload hcompare hpayloadFlag hequal hclean₁ hlabel₁ hbit₁
  change WriterIncrementSweepState hp reference
      (applySchedule ring T C (writerFirstEqualFlagZeroSchedule hp))
      payload ψ ∧
    (∀ i, WriterTransportCleanFrame
      (applySchedule ring T C (writerFirstEqualFlagZeroSchedule hp) i)) ∧
    WriterLabelFrame hp
      (applySchedule ring T C (writerFirstEqualFlagZeroSchedule hp)) ∧
    WriterSourceBitFrame hp reference
      (applySchedule ring T C (writerFirstEqualFlagZeroSchedule hp))
  rw [writerFirstEqualFlagZeroSchedule, applySchedule_append]
  simpa [transport, C₁, ring, T] using haction

/-! ## First physical ruler-history advance

The arbitrary-width theorem above reaches target group one but deliberately
stops before comparison.  The following independent width-two trace checks the
next architectural join under one unified repaired lifecycle.  The writer with
payload zero first moves into ruler group one, whose ID is zero.  Two forward
comparison interactions establish equality; one backward action interaction
flips the remaining component; and the canonical block schedule transports the
uniform flag-zero writer into group two.
-/

/-- Three width-two groups provide separate source, current-target, and
next-target blocks for the first history-advance trace. -/
theorem rulerAdvanceRingSix : DirectedRing 6 := ⟨by omega⟩

private def rulerAdvanceView (i : Fin 6) : PeaceView 2 :=
  { leader := false
    label := ⟨i.val % 2, by omega⟩
    shield := false
    bullet := ⟨0, by omega⟩
    signal_B := ⟨0, by omega⟩ }

/-- The source and first target both encode zero; group two encodes one.  The
initial complete payload-zero writer has common flag one and is ready to leave
the source group. -/
def rulerAdvanceInitial (i : Fin 6) : AgentState 2 :=
  let u := PeaceView.toState (rulerAdvanceView i)
  let u := if i = 5 then { u with bit := true } else u
  if i.val < 2 then
    { u with path3 := some ⟨i.val, 0, 1⟩, write_state := .depart }
  else u

/-- Endpoint after the first canonical block crossing, immediately before
processing ruler group one. -/
def rulerAdvanceAtTargetOne : Fin 6 → AgentState 2 :=
  applySchedule rulerAdvanceRingSix
    (writeSeqPersistentComparisonTransportLifecycle hTwo)
    rulerAdvanceInitial
    (writerBlockTransportSchedule rulerAdvanceRingSix (0 : Fin 6) 2)

/-- Forward comparison through labels zero and one, followed by the sole
backward action edge needed to flip the label-zero component. -/
def rulerTargetOneProcessSchedule : DetSchedule 6 :=
  [⟨1, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩]

/-- Configuration after the equal target group has been processed but before
the writer starts its next block crossing. -/
def rulerAdvanceAfterTargetOne : Fin 6 → AgentState 2 :=
  applySchedule rulerAdvanceRingSix
    (writeSeqPersistentComparisonTransportLifecycle hTwo)
    rulerAdvanceAtTargetOne rulerTargetOneProcessSchedule

/-- Endpoint after processing group one and transporting the writer into group
two under the same repaired lifecycle. -/
def rulerAdvanceAtTargetTwo : Fin 6 → AgentState 2 :=
  applySchedule rulerAdvanceRingSix
    (writeSeqPersistentComparisonTransportLifecycle hTwo)
    rulerAdvanceAfterTargetOne
    (writerBlockTransportSchedule rulerAdvanceRingSix (2 : Fin 6) 2)

/-- The repaired line-19 handoff makes the complete equal-group action live:
comparison reaches the terminal component, both flags flip from one to zero,
and the next canonical transport retires both arrivals in group two. -/
theorem rulerTargetOne_equal_advance_trace :
    (rulerAdvanceAtTargetOne 2).path3 = some ⟨0, 0, 1⟩ ∧
      (rulerAdvanceAtTargetOne 3).path3 = some ⟨1, 0, 1⟩ ∧
      (rulerAdvanceAfterTargetOne 2).path3 = some ⟨0, 0, 0⟩ ∧
      (rulerAdvanceAfterTargetOne 2).write_state = .depart ∧
      (rulerAdvanceAfterTargetOne 3).path3 = some ⟨1, 0, 0⟩ ∧
      (rulerAdvanceAfterTargetOne 3).write_state = .depart ∧
      (rulerAdvanceAtTargetTwo 2).path3 = none ∧
      (rulerAdvanceAtTargetTwo 3).path3 = none ∧
      (rulerAdvanceAtTargetTwo 4).path3 = some ⟨0, 0, 0⟩ ∧
      (rulerAdvanceAtTargetTwo 4).write_state = .none ∧
      (rulerAdvanceAtTargetTwo 5).path3 = some ⟨1, 0, 0⟩ ∧
      (rulerAdvanceAtTargetTwo 5).write_state = .none := by
  set_option maxRecDepth 200000 in
  decide

/-- Source-tagged carrier at group one for the physical advance trace. -/
def rulerAdvanceCarrierOne : SourceTaggedCompleteOverwritingCarrier
    rulerAdvanceRingSix rulerAdvanceAtTargetOne rulerAdvanceAtTargetOne
    (0 : Fin 6) where
  route :=
    { source := 0
      target := 1
      payload := groupID rulerAdvanceRingSix.hn rulerAdvanceAtTargetOne
        (stableGroupStart rulerAdvanceRingSix (0 : Fin 6) 2 0)
      source_in_range := by omega
      target_in_range := by omega
      payload_from_source := rfl }
  flag := 1
  components := by
    constructor
    · omega
    · intro k hk
      have hkCases : k = 0 ∨ k = 1 := by omega
      rcases hkCases with rfl | rfl <;>
        set_option maxRecDepth 200000 in decide

/-- Source-tagged carrier after the same writer reaches group two. -/
def rulerAdvanceCarrierTwo : SourceTaggedCompleteOverwritingCarrier
    rulerAdvanceRingSix rulerAdvanceAtTargetTwo rulerAdvanceAtTargetTwo
    (0 : Fin 6) where
  route :=
    { source := 0
      target := 2
      payload := groupID rulerAdvanceRingSix.hn rulerAdvanceAtTargetTwo
        (stableGroupStart rulerAdvanceRingSix (0 : Fin 6) 2 0)
      source_in_range := by omega
      target_in_range := by omega
      payload_from_source := rfl }
  flag := 0
  components := by
    constructor
    · omega
    · intro k hk
      have hkCases : k = 0 ∨ k = 1 := by omega
      rcases hkCases with rfl | rfl <;>
        set_option maxRecDepth 200000 in decide

/-- The first transported carrier has the expected ruler state before group
one. -/
theorem rulerAdvanceCarrierOne_history :
    RulerOverwritingHistory rulerAdvanceRingSix rulerAdvanceAtTargetOne
      (0 : Fin 6) rulerAdvanceCarrierOne := by
  refine ⟨by change 0 < 1; omega, ?_⟩
  set_option maxRecDepth 200000 in
  decide

/-- **First executable `RulerOverwritingHistory.advance`.**  The payload and
route target are preserved by the two physical block crossings, while the
equal-group action realizes the ruler recurrence from flag one to flag zero. -/
theorem rulerTargetOne_physical_history_advance :
    RulerOverwritingHistory rulerAdvanceRingSix rulerAdvanceAtTargetTwo
      (0 : Fin 6) rulerAdvanceCarrierTwo := by
  apply RulerOverwritingHistory.advance rulerAdvanceRingSix
    rulerAdvanceAtTargetOne rulerAdvanceAtTargetTwo (0 : Fin 6)
    rulerAdvanceCarrierOne rulerAdvanceCarrierTwo
    rulerAdvanceCarrierOne_history
  · set_option maxRecDepth 200000 in decide
  · decide
  · set_option maxRecDepth 200000 in decide


/-- One complete two-component writer followed by one empty group. -/
def persistentCompleteTransportConfig (i : Fin 4) : AgentState 2 :=
  if i = 0 then persistentTransferLeft
  else if i = 1 then persistentTerminalTransferLeft
  else if i = 2 then persistentWrapTransferRight
  else persistentTransferRight

/-- Right-to-left sweeps keep every destination empty.  Each component moves
two physical edges, so the whole writer advances from positions `0,1` to
positions `2,3`. -/
def persistentCompleteTransportSchedule : DetSchedule 4 :=
  writerBlockTransportSchedule conditionFiveRing (0 : Fin 4) 2

theorem persistentCompleteTransportSchedule_eq :
    persistentCompleteTransportSchedule =
      [⟨1, by omega⟩, ⟨0, by omega⟩,
        ⟨2, by omega⟩, ⟨1, by omega⟩] := by
  rfl

def persistentCompleteTransportAfter : Fin 4 → AgentState 2 :=
  applySchedule conditionFiveRing
    (writeSeqPersistentComparisonTransportLifecycle hTwo)
    persistentCompleteTransportConfig persistentCompleteTransportSchedule

/-- **Positive complete-writer transport.**  Four actual repaired WRITE_SEQ
interactions move both components through one whole group.  Both source slots
are empty, both target slots retain the exact payloads and common flag, and
each arrival is retired rather than beginning another lap. -/
theorem persistentCompleteTransport_crosses_group :
    (persistentCompleteTransportAfter 0).path3 = none ∧
      (persistentCompleteTransportAfter 1).path3 = none ∧
      (persistentCompleteTransportAfter 2).path3 = some ⟨0, 0, 1⟩ ∧
      (persistentCompleteTransportAfter 2).write_state = .none ∧
      (persistentCompleteTransportAfter 3).path3 = some ⟨1, 0, 1⟩ ∧
      (persistentCompleteTransportAfter 3).write_state = .none := by
  set_option maxRecDepth 100000 in
  decide

/-- The transported physical block is a complete source-tagged overwriting
carrier at the next group, using the unchanged source-group bits in the final
configuration itself. -/
theorem persistentCompleteTransport_sourceTagged :
    overwritingBitsMatchBetweenAt conditionFiveRing
      persistentCompleteTransportAfter persistentCompleteTransportAfter
      (2 : Fin 4) (0 : Fin 4) 1 := by
  set_option maxRecDepth 100000 in
    constructor
    · omega
    · intro k hk
      have hkCases : k = 0 ∨ k = 1 := by omega
      rcases hkCases with rfl | rfl <;> decide

/-- Concrete bridge from the physical four-edge schedule to the existing
complete-carrier history interface. -/
def persistentCompleteTransportCarrier :
    SourceTaggedCompleteOverwritingCarrier conditionFiveRing
      persistentCompleteTransportAfter persistentCompleteTransportAfter
      (0 : Fin 4) where
  route :=
    { source := 0
      target := 1
      payload := groupID conditionFiveRing.hn
        persistentCompleteTransportAfter
        (stableGroupStart conditionFiveRing (0 : Fin 4) 2 0)
      source_in_range := by omega
      target_in_range := by omega
      payload_from_source := rfl }
  flag := 1
  components := by
    simpa [stableGroupStart] using persistentCompleteTransport_sourceTagged

/-- In this exact trace the transported carrier already satisfies the static
ruler-flag certificate at positive target group one. -/
theorem persistentCompleteTransport_rulerHistory :
    RulerOverwritingHistory conditionFiveRing
      persistentCompleteTransportAfter (0 : Fin 4)
      persistentCompleteTransportCarrier := by
  refine ⟨by change 0 < 1; omega, ?_⟩
  set_option maxRecDepth 100000 in
  decide

/-! ## Independent width-three acceptance trace -/

theorem writerTransportRingSix : DirectedRing 6 := ⟨by omega⟩

private def writerTransportThreeView (i : Fin 6) : PeaceView 3 :=
  { leader := false
    label := ⟨i.val % 3, by omega⟩
    shield := false
    bullet := ⟨0, by omega⟩
    signal_B := ⟨0, by omega⟩ }

/-- Three aligned writer components followed by one empty three-agent group. -/
def writerTransportThreeConfig (i : Fin 6) : AgentState 3 :=
  let u := PeaceView.toState (writerTransportThreeView i)
  if i.val < 3 then
    { u with path3 := some ⟨i.val, 0, 1⟩, write_state := .depart }
  else u

theorem writerBlockTransportSchedule_three :
    writerBlockTransportSchedule writerTransportRingSix (0 : Fin 6) 3 =
      [⟨2, by omega⟩, ⟨1, by omega⟩, ⟨0, by omega⟩,
        ⟨3, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩,
        ⟨4, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩] := by
  rfl

def writerTransportThreeAfter : Fin 6 → AgentState 3 :=
  applySchedule writerTransportRingSix
    (writeSeqPersistentComparisonTransportLifecycle hThree)
    writerTransportThreeConfig
    (writerBlockTransportSchedule writerTransportRingSix (0 : Fin 6) 3)

/-- The same canonical schedule works independently at width three: all three
source cells empty and all three exact payloads stop in the next group. -/
theorem writerTransportThree_crosses_group :
    (writerTransportThreeAfter 0).path3 = none ∧
      (writerTransportThreeAfter 1).path3 = none ∧
      (writerTransportThreeAfter 2).path3 = none ∧
      (writerTransportThreeAfter 3).path3 = some ⟨0, 0, 1⟩ ∧
      (writerTransportThreeAfter 3).write_state = .none ∧
      (writerTransportThreeAfter 4).path3 = some ⟨1, 0, 1⟩ ∧
      (writerTransportThreeAfter 4).write_state = .none ∧
      (writerTransportThreeAfter 5).path3 = some ⟨2, 0, 1⟩ ∧
      (writerTransportThreeAfter 5).write_state = .none := by
  set_option maxRecDepth 200000 in
  decide

theorem writerTransportThree_sourceTagged :
    overwritingBitsMatchBetweenAt writerTransportRingSix
      writerTransportThreeAfter writerTransportThreeAfter
      (3 : Fin 6) (0 : Fin 6) 1 := by
  constructor
  · omega
  · intro k hk
    have hkCases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hkCases with rfl | rfl | rfl <;>
      set_option maxRecDepth 200000 in decide

def writerTransportThreeCarrier :
    SourceTaggedCompleteOverwritingCarrier writerTransportRingSix
      writerTransportThreeAfter writerTransportThreeAfter (0 : Fin 6) where
  route :=
    { source := 0
      target := 1
      payload := groupID writerTransportRingSix.hn
        writerTransportThreeAfter
        (stableGroupStart writerTransportRingSix (0 : Fin 6) 3 0)
      source_in_range := by omega
      target_in_range := by omega
      payload_from_source := rfl }
  flag := 1
  components := by
    simpa [stableGroupStart] using writerTransportThree_sourceTagged

/-- Width three reaches the same static condition-4 history interface as the
width-two trace. -/
theorem writerTransportThree_rulerHistory :
    RulerOverwritingHistory writerTransportRingSix
      writerTransportThreeAfter (0 : Fin 6) writerTransportThreeCarrier := by
  refine ⟨by change 0 < 1; omega, ?_⟩
  set_option maxRecDepth 200000 in
  decide

/-- Restoring movement does not sacrifice the newly live same-call terminal
increment. -/
theorem persistentLifecycle_preserves_same_call_increment :
    (writeSeqPersistentLifecycle hTwo
      persistentEqualLeft persistentEqualRight).2.bit = true := by
  decide

/-- The repaired increment flips the processed terminal component and sends a
`move_flip` state toward the remaining more-significant components. -/
def persistentIncrementAfterFirst : AgentState 2 × AgentState 2 :=
  writeSeqPersistentLifecycle hTwo persistentEqualLeft persistentEqualRight

/-- A predecessor used only to schedule the propagated `move_flip` through the
label-zero component on the next local edge. -/
def persistentIncrementFlipPredecessor : AgentState 2 :=
  { conditionFiveCoreConfig 1 with
    label := ⟨1, by omega⟩
    path3 := none
    write_state := .none
    write := .none }

def persistentIncrementAfterSecond : AgentState 2 × AgentState 2 :=
  writeActionPreservingDepart hTwo
    persistentIncrementFlipPredecessor persistentIncrementAfterFirst.1

/-- **Positive writer-bit lifecycle.**  A generated flag-zero terminal
increment changes the group bit, flips its own flag, propagates `move_flip`,
and the next predecessor interaction flips the remaining label-zero flag.  The
two-component writer is then uniformly flag one, exactly as the ruler
automaton requires after an equal group. -/
theorem persistentLifecycle_increment_completes_flag_flip :
    persistentIncrementAfterFirst.1.path3 = some ⟨0, 0, 0⟩ ∧
      persistentIncrementAfterFirst.1.write_state = .move_flip ∧
      persistentIncrementAfterFirst.2.path3 = some ⟨1, 0, 1⟩ ∧
      persistentIncrementAfterFirst.2.bit = true ∧
      persistentIncrementAfterSecond.2.path3 = some ⟨0, 0, 1⟩ ∧
      persistentIncrementAfterSecond.2.write_state = .depart := by
  decide

/-- Line-8 persistence plus action sanitization does not solve condition 4: the
forged terminal `move_flip` still changes the sole zero flag to one. -/
theorem persistent_repair_retains_conditionFour_moveFlip :
    (writeSeqPersistentIncrementGate hThree
      (conditionFourCoreConfig 7)
      (conditionFourCoreConfig 8)).2.path3 = some ⟨2, 0, 1⟩ := by
  decide

end PPLLWriteSeqPersistenceRegression

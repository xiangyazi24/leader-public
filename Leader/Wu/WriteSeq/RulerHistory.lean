import Leader.Wu.WriteSeq.RulerBridge

/-!
# Phase-correct ruler-history transport

The action and transport interfaces now expose the exact configurations needed
by `RulerOverwritingHistory.advance`.  This module begins the global join by
proving that an older stable source group is geometrically outside every later
two-group window, including windows that wrap through physical index zero.
These are repair-lane facts used to preserve the authenticated source snapshot.
-/

namespace PPLLWriteSeqRulerHistory

open PPLL PPLLWriteSeqPersistenceRepair
  PPLLWriteSeqPersistenceRegression PPLLWriteSeqRelocation
  PPLLWriteSeqRulerBridge

/-! ## Reusable stable-suffix state -/

/-- An unvisited stable group has no writer payload, has the clean control and
cyclic label frames required by the next transport, and carries its ruler ID. -/
def WriterFreshStableGroup {ψ n : Nat} (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (leaderPos : Fin n) (group : Nat) : Prop :=
  (∀ k, k < ψ →
    let u := C (groupOffset ring
      (stableGroupStart ring leaderPos ψ group) k)
    u.path3 = none ∧ WriterTransportCleanFrame u ∧ u.label.val = k) ∧
  groupID ring.hn C (stableGroupStart ring leaderPos ψ group) =
    trailingZeros group

/-- Every indexed stable group strictly after `target` is fresh. -/
def WriterFreshStableSuffix {ψ n : Nat} (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (leaderPos : Fin n) (target : Nat) : Prop :=
  ∀ group, target < group → group < n / ψ →
    WriterFreshStableGroup ring C leaderPos group

/-- Induction state for one complete source-tagged writer immediately before
processing positive stable group `target`. -/
structure RulerWriterAtTarget {ψ n : Nat} (hψ : 0 < ψ)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (leaderPos : Fin n) (target : Nat) where
  carrier : SourceTaggedCompleteOverwritingCarrier ring C C leaderPos
  carrier_target : carrier.route.target = target
  source_lt_target : carrier.route.source < target
  history : RulerOverwritingHistory ring C leaderPos carrier
  payload : Nat → Path3Info
  payload_label : ∀ k, k < ψ → (payload k).label = k
  payload_bit : ∀ k, k < ψ →
    (payload k).bit = boolBitValue
      (C (groupOffset ring
        (stableGroupStart ring leaderPos ψ carrier.route.source) k)).bit
  payload_flag : ∀ k, k < ψ → (payload k).flag = carrier.flag
  round : WriterRoundState hψ
    (writerWindowPullback ring
      (stableGroupStart ring leaderPos ψ (target - 1)) C) payload ψ
  clean : ∀ i, WriterTransportCleanFrame
    ((writerWindowPullback ring
      (stableGroupStart ring leaderPos ψ (target - 1)) C) i)
  labels : WriterLabelFrame hψ
    (writerWindowPullback ring
      (stableGroupStart ring leaderPos ψ (target - 1)) C)
  target_id : groupID ring.hn C
    (stableGroupStart ring leaderPos ψ target) = trailingZeros target
  fresh_suffix : WriterFreshStableSuffix ring C leaderPos target

/-! ## Stable-group coordinates and window separation -/

/-- A stable group start is the ordinary group offset by `group * ψ` from the
leader anchor. -/
theorem stableGroupStart_eq_groupOffset {ψ n : Nat} (ring : DirectedRing n)
    (leaderPos : Fin n) (group : Nat) :
    stableGroupStart ring leaderPos ψ group =
      groupOffset ring leaderPos (group * ψ) := by
  rfl

/-- Two stable-group successors equal a physical offset of `2ψ`. -/
theorem stableGroupStart_add_two_eq_groupOffset {ψ n : Nat}
    (ring : DirectedRing n) (leaderPos : Fin n) (group : Nat) :
    stableGroupStart ring leaderPos ψ (group + 2) =
      groupOffset ring (stableGroupStart ring leaderPos ψ group) (2 * ψ) := by
  rw [show group + 2 = (group + 1) + 1 by omega,
    stableGroupStart_succ_eq_groupOffset (ψ := ψ) ring leaderPos (group + 1),
    stableGroupStart_succ_eq_groupOffset (ψ := ψ) ring leaderPos group,
    groupOffset_compose]
  congr 1
  omega

/-- Every component of a strictly earlier stable group is outside a later
two-group writer window.  Offsets are compared before one full revolution, so
the result remains valid when the physical window crosses index zero. -/
theorem stableSource_component_ne_later_window
    {ψ n source window k : Nat} (_hψ : 0 < ψ)
    (ring : DirectedRing n) (leaderPos : Fin n)
    (hsource : source < window) (hk : k < ψ)
    (hbound : (window + 2) * ψ ≤ n)
    (j : Fin (2 * ψ)) :
    groupOffset ring (stableGroupStart ring leaderPos ψ source) k ≠
      writerWindowEmbed ring (stableGroupStart ring leaderPos ψ window) j := by
  have hsourceStep : (source + 1) * ψ ≤ window * ψ :=
    Nat.mul_le_mul_right ψ (by omega)
  have hsourceOffset : source * ψ + k < window * ψ := by
    have hk' : source * ψ + k < source * ψ + ψ := by omega
    have hshape : source * ψ + ψ = (source + 1) * ψ := by
      rw [Nat.add_mul]
      simp
    omega
  have hwindowOffset : window * ψ + j.val < (window + 2) * ψ := by
    rw [Nat.add_mul]
    omega
  rw [stableGroupStart_eq_groupOffset, groupOffset_compose]
  unfold writerWindowEmbed
  rw [stableGroupStart_eq_groupOffset, groupOffset_compose]
  apply groupOffset_ne_of_lt ring leaderPos
  · omega
  · omega
  · omega

/-- A non-wrapping relocated schedule on a later two-group window preserves
every bit of a strictly earlier stable source group. -/
theorem relocateWriterSchedule_preserves_earlier_stable_source_bits
    {ψ n source window : Nat} (hψ : 1 < ψ)
    (ring : DirectedRing n) (leaderPos : Fin n)
    (hsource : source < window) (hbound : (window + 2) * ψ ≤ n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (C : Fin n → AgentState ψ) (schedule : DetSchedule (2 * ψ))
    (hnonwrap : WriterScheduleNonwrapping schedule) :
    let D := _root_.applySchedule ring T C
      (relocateWriterSchedule ring
        (stableGroupStart ring leaderPos ψ window) schedule)
    ∀ k, k < ψ →
      (D (groupOffset ring
        (stableGroupStart ring leaderPos ψ source) k)).bit =
      (C (groupOffset ring
        (stableGroupStart ring leaderPos ψ source) k)).bit := by
  dsimp only
  intro k hk
  let i := groupOffset ring (stableGroupStart ring leaderPos ψ source) k
  have hiOutside : ∀ j : Fin (2 * ψ),
      i ≠ writerWindowEmbed ring
        (stableGroupStart ring leaderPos ψ window) j := by
    intro j
    exact stableSource_component_ne_later_window (by omega) ring leaderPos
      hsource hk hbound j
  have hwindow : 2 * ψ ≤ n := by
    have hcoeff : 2 ≤ window + 2 := by omega
    exact Nat.le_trans (Nat.mul_le_mul_right ψ hcoeff) hbound
  have houtside := relocateWriterSchedule_eq_of_outside hψ ring
    (stableGroupStart ring leaderPos ψ window) hwindow T C schedule
    hnonwrap i hiOutside
  exact congrArg AgentState.bit houtside

/-- A component in a stable group at least two groups after a window start is
outside that two-group writer window. -/
theorem stableFuture_component_ne_earlier_window
    {ψ n future window k : Nat} (_hψ : 0 < ψ)
    (ring : DirectedRing n) (leaderPos : Fin n)
    (hfuture : window + 2 ≤ future) (hk : k < ψ)
    (hfutureRange : future < n / ψ) (j : Fin (2 * ψ)) :
    groupOffset ring (stableGroupStart ring leaderPos ψ future) k ≠
      writerWindowEmbed ring (stableGroupStart ring leaderPos ψ window) j := by
  have hfutureCoeff : future + 1 ≤ n / ψ := by omega
  have hfutureBound : (future + 1) * ψ ≤ n :=
    Nat.le_trans (Nat.mul_le_mul_right ψ hfutureCoeff)
      (Nat.div_mul_le_self n ψ)
  have hwindowOffset : window * ψ + j.val < future * ψ := by
    have hjBound : window * ψ + j.val < (window + 2) * ψ := by
      rw [Nat.add_mul]
      omega
    have hgroups := Nat.mul_le_mul_right ψ hfuture
    omega
  have hfutureOffset : future * ψ + k < (future + 1) * ψ := by
    rw [Nat.add_mul]
    omega
  rw [stableGroupStart_eq_groupOffset, groupOffset_compose]
  unfold writerWindowEmbed
  rw [stableGroupStart_eq_groupOffset, groupOffset_compose]
  apply groupOffset_ne_of_lt ring leaderPos
  · omega
  · omega
  · omega

/-- Any non-wrapping relocated schedule preserves every full stable group at
least two groups after its window start. -/
theorem relocateWriterSchedule_preserves_later_stable_group
    {ψ n future window : Nat} (hψ : 1 < ψ)
    (ring : DirectedRing n) (leaderPos : Fin n)
    (hfuture : window + 2 ≤ future) (hfutureRange : future < n / ψ)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (C : Fin n → AgentState ψ) (schedule : DetSchedule (2 * ψ))
    (hnonwrap : WriterScheduleNonwrapping schedule) :
    let D := _root_.applySchedule ring T C
      (relocateWriterSchedule ring
        (stableGroupStart ring leaderPos ψ window) schedule)
    ∀ k, k < ψ →
      D (groupOffset ring (stableGroupStart ring leaderPos ψ future) k) =
        C (groupOffset ring
          (stableGroupStart ring leaderPos ψ future) k) := by
  dsimp only
  intro k hk
  let i := groupOffset ring (stableGroupStart ring leaderPos ψ future) k
  have hiOutside : ∀ j : Fin (2 * ψ),
      i ≠ writerWindowEmbed ring
        (stableGroupStart ring leaderPos ψ window) j := by
    intro j
    exact stableFuture_component_ne_earlier_window (by omega) ring leaderPos
      hfuture hk hfutureRange j
  have hwindow : 2 * ψ ≤ n := by
    have hfuturePos : 0 < future := by omega
    have hcoeff : 2 ≤ future + 1 := by omega
    exact Nat.le_trans (Nat.mul_le_mul_right ψ hcoeff)
      (Nat.le_trans
        (Nat.mul_le_mul_right ψ (by omega : future + 1 ≤ n / ψ))
        (Nat.div_mul_le_self n ψ))
  exact relocateWriterSchedule_eq_of_outside hψ ring
    (stableGroupStart ring leaderPos ψ window) hwindow T C schedule
    hnonwrap i hiOutside

/-! ## Source snapshot preservation through the two phases -/

/-- Every schedule selected by the phase-correct action classifier is
non-wrapping in its canonical two-group window. -/
theorem WriterSelectedActionOutcome.nonwrapping {ψ : Nat} (hψ : 0 < ψ)
    (target : Nat → Bool) (payload : Nat → Path3Info) (flag : Nat)
    (schedule : DetSchedule (2 * ψ)) (nextPayload : Nat → Path3Info)
    (houtcome : WriterSelectedActionOutcome hψ target payload flag schedule
      nextPayload) :
    WriterScheduleNonwrapping schedule := by
  rcases houtcome with ⟨_, _, rfl, _⟩ | ⟨_, _, rfl, _⟩ |
      ⟨mismatch, _, _, hmismatch, _, _, _, rfl, _⟩
  · exact writerEqualFlagOneActionSchedule_nonwrapping hψ
  · exact writerEqualFlagZeroActionSchedule_nonwrapping hψ
  · exact writerUnequalActionSchedule_nonwrapping hψ hmismatch

/-- A selected action at stable target `target` preserves its older source
group.  The adjacent source is the action window's proved first half; a
strictly older source is outside the whole relocated schedule. -/
theorem selectedAction_preserves_stable_source_bits
    {ψ n source target : Nat} (hψ : 1 < ψ)
    (ring : DirectedRing n) (leaderPos : Fin n)
    (hsource : source < target) (htarget : 0 < target)
    (hbound : (target + 1) * ψ ≤ n)
    (C : Fin n → AgentState ψ) (targetBits : Nat → Bool)
    (payload nextPayload : Nat → Path3Info) (flag : Nat)
    (schedule : DetSchedule (2 * ψ))
    (houtcome : WriterSelectedActionOutcome (by omega) targetBits payload flag
      schedule nextPayload)
    (hfirstHalf :
      let A := _root_.applySchedule ring
        (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
        (relocateWriterSchedule ring
          (stableGroupStart ring leaderPos ψ (target - 1)) schedule)
      ∀ k, k < ψ →
        (A (groupOffset ring
          (stableGroupStart ring leaderPos ψ (target - 1)) k)).bit =
        (C (groupOffset ring
          (stableGroupStart ring leaderPos ψ (target - 1)) k)).bit) :
    let A := _root_.applySchedule ring
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (relocateWriterSchedule ring
        (stableGroupStart ring leaderPos ψ (target - 1)) schedule)
    ∀ k, k < ψ →
      (A (groupOffset ring
        (stableGroupStart ring leaderPos ψ source) k)).bit =
      (C (groupOffset ring
        (stableGroupStart ring leaderPos ψ source) k)).bit := by
  let T := writeSeqPersistentComparisonTransportLifecycle (by omega : 0 < ψ)
  let start := stableGroupStart ring leaderPos ψ (target - 1)
  let A := _root_.applySchedule ring T C
    (relocateWriterSchedule ring start schedule)
  by_cases hadjacent : source = target - 1
  · subst source
    simpa [A, T, start] using hfirstHalf
  · have hstrict : source < target - 1 := by omega
    have hwindowBound : (target - 1 + 2) * ψ ≤ n := by
      have hindex : target - 1 + 2 = target + 1 := by omega
      rw [hindex]
      exact hbound
    exact relocateWriterSchedule_preserves_earlier_stable_source_bits hψ ring
      leaderPos hstrict hwindowBound T C schedule
      (WriterSelectedActionOutcome.nonwrapping (by omega) targetBits payload
        flag schedule nextPayload houtcome)

/-- The standalone transport from stable target `target` to `target+1`
preserves every older source group. -/
theorem writerBlockTransport_preserves_earlier_stable_source_bits
    {ψ n source target : Nat} (hψ : 1 < ψ)
    (ring : DirectedRing n) (leaderPos : Fin n)
    (hsource : source < target) (hbound : (target + 2) * ψ ≤ n)
    (C : Fin n → AgentState ψ) :
    let schedule := writerBlockTransportSchedule
      (genericWriterRing (ψ := ψ) (by omega))
      (genericWriterStart (ψ := ψ) (by omega)) ψ
    let D := _root_.applySchedule ring
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (relocateWriterSchedule ring
        (stableGroupStart ring leaderPos ψ target) schedule)
    ∀ k, k < ψ →
      (D (groupOffset ring
        (stableGroupStart ring leaderPos ψ source) k)).bit =
      (C (groupOffset ring
        (stableGroupStart ring leaderPos ψ source) k)).bit := by
  exact relocateWriterSchedule_preserves_earlier_stable_source_bits hψ ring
    leaderPos hsource hbound
    (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
    (writerBlockTransportSchedule (genericWriterRing (ψ := ψ) (by omega))
      (genericWriterStart (ψ := ψ) (by omega)) ψ)
    (writerBlockTransportSchedule_nonwrapping (by omega))

/-! ## One phase-correct ruler-history advance -/

/-- **Arbitrary-width physical ruler-history step.** A certified writer already
resident at its current stable target selects and executes the current action,
crosses to the following target, preserves its older authenticated source, and
instantiates the repository's exact `RulerOverwritingHistory.advance` theorem.
The returned schedule is the real relocated action followed by the real
relocated block transport. -/
theorem RulerOverwritingHistory.exists_next_physical
    {ψ n : Nat} (hψ : 1 < ψ) (ring : DirectedRing n)
    (leaderPos : Fin n) (C : Fin n → AgentState ψ)
    (carrier : SourceTaggedCompleteOverwritingCarrier ring C C leaderPos)
    (history : RulerOverwritingHistory ring C leaderPos carrier)
    (hsourceLt : carrier.route.source < carrier.route.target)
    (hnextRange : carrier.route.target + 1 < n / ψ)
    (hbound : (carrier.route.target + 2) * ψ ≤ n)
    (payload : Nat → Path3Info)
    (hpayloadLabel : ∀ k, k < ψ → (payload k).label = k)
    (hpayloadBit : ∀ k, k < ψ →
      (payload k).bit = boolBitValue
        (C (groupOffset ring
          (stableGroupStart ring leaderPos ψ carrier.route.source) k)).bit)
    (hpayloadFlag : ∀ k, k < ψ →
      (payload k).flag = carrier.flag)
    (hstate : WriterRoundState (by omega)
      (writerWindowPullback ring
        (stableGroupStart ring leaderPos ψ (carrier.route.target - 1)) C)
      payload ψ)
    (hclean : ∀ i, WriterTransportCleanFrame
      ((writerWindowPullback ring
        (stableGroupStart ring leaderPos ψ (carrier.route.target - 1)) C) i))
    (hlabel : WriterLabelFrame (by omega)
      (writerWindowPullback ring
        (stableGroupStart ring leaderPos ψ (carrier.route.target - 1)) C))
    (hnextFresh : ∀ k, k < ψ →
      let u := C (groupOffset ring
        (stableGroupStart ring leaderPos ψ (carrier.route.target - 1))
        (2 * ψ + k))
      u.path3 = none ∧ WriterTransportCleanFrame u ∧ u.label.val = k)
    (htargetID : groupID ring.hn C
      (stableGroupStart ring leaderPos ψ carrier.route.target) =
        trailingZeros carrier.route.target) :
    ∃ (schedule : DetSchedule n) (nextPayload : Nat → Path3Info),
      let D := _root_.applySchedule ring
        (writeSeqPersistentComparisonTransportLifecycle (by omega)) C schedule
      ∃ next : SourceTaggedCompleteOverwritingCarrier ring D D leaderPos,
        next.route.source = carrier.route.source ∧
          next.route.target = carrier.route.target + 1 ∧
          next.route.payload = carrier.route.payload ∧
          RulerOverwritingHistory ring D leaderPos next ∧
          WriterRoundState (by omega)
            (writerWindowPullback ring
              (stableGroupStart ring leaderPos ψ carrier.route.target) D)
            nextPayload ψ ∧
          (∀ i, WriterTransportCleanFrame
            ((writerWindowPullback ring
              (stableGroupStart ring leaderPos ψ carrier.route.target) D) i)) ∧
          WriterLabelFrame (by omega)
            (writerWindowPullback ring
              (stableGroupStart ring leaderPos ψ carrier.route.target) D) ∧
          (∀ k, k < ψ → (nextPayload k).label = k) ∧
          (∀ k, k < ψ →
            (nextPayload k).bit = boolBitValue
              (D (groupOffset ring
                (stableGroupStart ring leaderPos ψ next.route.source) k)).bit) ∧
          (∀ k, k < ψ → (nextPayload k).flag = next.flag) ∧
          groupID ring.hn D
              (stableGroupStart ring leaderPos ψ (carrier.route.target + 1)) =
            groupID ring.hn C
              (stableGroupStart ring leaderPos ψ (carrier.route.target + 1)) ∧
          (∀ future, carrier.route.target + 1 < future →
            future < n / ψ → ∀ k, k < ψ →
              D (groupOffset ring
                (stableGroupStart ring leaderPos ψ future) k) =
              C (groupOffset ring
                (stableGroupStart ring leaderPos ψ future) k)) := by
  let hp : 0 < ψ := by omega
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let source := carrier.route.source
  let target := carrier.route.target
  let actionStart := stableGroupStart ring leaderPos ψ (target - 1)
  let targetStart := groupOffset ring actionStart ψ
  have htargetPos : 0 < target := history.target_pos
  have hstableTarget : targetStart =
      stableGroupStart ring leaderPos ψ target := by
    have hsucc := stableGroupStart_succ_eq_groupOffset (ψ := ψ) ring leaderPos
      (target - 1)
    have hindex : target - 1 + 1 = target := by omega
    rw [hindex] at hsucc
    exact hsucc.symm
  have hthree : 3 * ψ ≤ n := by
    have hcoeff : 3 ≤ target + 2 := by omega
    exact Nat.le_trans (Nat.mul_le_mul_right ψ hcoeff) hbound
  obtain ⟨actionSchedule, nextPayload, nextFlag, houtcome, hactionEndpoint,
      hfields, hflagUpdate⟩ :=
    writerActionOnlySchedule_relocated_toNextRoundState_with_groupID_update
      hψ ring actionStart (stableGroupStart ring leaderPos ψ source) hthree
      C C C payload carrier.flag carrier.components.1 hpayloadLabel hpayloadBit
      hpayloadFlag hstate hclean hlabel (fun _ => rfl) hnextFresh
  let actionLarge := relocateWriterSchedule ring actionStart actionSchedule
  let A := _root_.applySchedule ring T C actionLarge
  change WriterRoundState hp (writerWindowPullback ring targetStart A)
        nextPayload 0 ∧
      (∀ i, WriterTransportCleanFrame
        ((writerWindowPullback ring targetStart A) i)) ∧
      WriterLabelFrame hp (writerWindowPullback ring targetStart A) ∧
      (∀ k, k < ψ →
        (A (groupOffset ring actionStart k)).bit =
          (C (groupOffset ring actionStart k)).bit) at hactionEndpoint
  change WriterSelectedActionOutcome hp
      (fun k => (C (groupOffset ring targetStart k)).bit)
      payload carrier.flag actionSchedule nextPayload at houtcome
  have hactionSource := selectedAction_preserves_stable_source_bits hψ ring
    leaderPos hsourceLt htargetPos
    (by
      have hcoeff : target + 1 ≤ target + 2 := by omega
      exact Nat.le_trans (Nat.mul_le_mul_right ψ hcoeff) hbound)
    C (fun k => (C (groupOffset ring targetStart k)).bit) payload nextPayload
    carrier.flag actionSchedule houtcome hactionEndpoint.2.2.2
  change ∀ k, k < ψ →
      (A (groupOffset ring
        (stableGroupStart ring leaderPos ψ source) k)).bit =
      (C (groupOffset ring
        (stableGroupStart ring leaderPos ψ source) k)).bit at hactionSource
  have hnextPayloadLabel : ∀ k, k < ψ → (nextPayload k).label = k := by
    intro k hk
    rw [(hfields k hk).1, hpayloadLabel k hk]
  let transportSchedule := writerBlockTransportSchedule
    (genericWriterRing hp) (genericWriterStart hp) ψ
  let transportLarge := relocateWriterSchedule ring targetStart
    transportSchedule
  let D := _root_.applySchedule ring T A transportLarge
  have htransport := writerBlockTransportSchedule_relocated_from_zero hψ ring
    targetStart (by omega) A nextPayload hnextPayloadLabel
    hactionEndpoint.1 hactionEndpoint.2.1 hactionEndpoint.2.2.1
  change WriterRoundState hp (writerWindowPullback ring targetStart D)
        nextPayload ψ ∧
      (∀ i, WriterTransportCleanFrame
        ((writerWindowPullback ring targetStart D) i)) ∧
      WriterLabelFrame hp (writerWindowPullback ring targetStart D) ∧
      WriterBitFrame (writerWindowPullback ring targetStart A)
        (writerWindowPullback ring targetStart D) at htransport
  have htransportSourceRaw :=
    writerBlockTransport_preserves_earlier_stable_source_bits hψ ring
      leaderPos hsourceLt hbound A
  have htransportSource : ∀ k, k < ψ →
      (D (groupOffset ring
        (stableGroupStart ring leaderPos ψ source) k)).bit =
      (A (groupOffset ring
        (stableGroupStart ring leaderPos ψ source) k)).bit := by
    simpa [source, target, D, transportSchedule, transportLarge, T,
      hstableTarget] using htransportSourceRaw
  have hsourcePreserved : ∀ k, k < ψ →
      (D (groupOffset ring
        (stableGroupStart ring leaderPos ψ source) k)).bit =
      (C (groupOffset ring
        (stableGroupStart ring leaderPos ψ source) k)).bit := by
    intro k hk
    rw [htransportSource k hk, hactionSource k hk]
  have hsourceGroupID : groupID ring.hn D
      (stableGroupStart ring leaderPos ψ source) =
        groupID ring.hn C
          (stableGroupStart ring leaderPos ψ source) := by
    apply groupID_eq_of_bits ring D C _ _
    intro k hk
    exact hsourcePreserved k hk
  have hnextPayloadBit : ∀ k, k < ψ →
      (nextPayload k).bit = boolBitValue
        (D (groupOffset ring
          (stableGroupStart ring leaderPos ψ source) k)).bit := by
    intro k hk
    rw [(hfields k hk).2.1, hpayloadBit k hk, hsourcePreserved k hk]
  have hnextPayloadFlag : ∀ k, k < ψ →
      (nextPayload k).flag = nextFlag := by
    intro k hk
    exact (hfields k hk).2.2
  have hnextFlagBound : nextFlag ≤ 1 := by
    have holdFlag : carrier.flag ≤ 1 := carrier.components.1
    change nextFlag =
        (if groupID ring.hn C (stableGroupStart ring leaderPos ψ source) ≤
            groupID ring.hn C targetStart
          then 1 - carrier.flag else carrier.flag) at hflagUpdate
    rw [hflagUpdate]
    split <;> omega
  have hnextTargetStart : stableGroupStart ring leaderPos ψ (target + 1) =
      groupOffset ring targetStart ψ := by
    rw [stableGroupStart_succ_eq_groupOffset (ψ := ψ) ring leaderPos target]
    exact congrArg (fun s => groupOffset ring s ψ) hstableTarget.symm
  have hnextPayloadID : carrier.route.payload = groupID ring.hn D
      (stableGroupStart ring leaderPos ψ source) := by
    calc
      carrier.route.payload = groupID ring.hn C
          (stableGroupStart ring leaderPos ψ source) :=
        carrier.route.payload_from_source
      _ = groupID ring.hn D
          (stableGroupStart ring leaderPos ψ source) := hsourceGroupID.symm
  obtain ⟨next, hnextSource, hnextTarget, hnextPayload, hnextFlag⟩ :=
    WriterRoundState.existsSourceTaggedCarrier hp ring leaderPos targetStart D
      nextPayload source (target + 1) carrier.route.payload nextFlag
      carrier.route.source_in_range hnextRange hnextTargetStart hnextPayloadID
      htransport.1 hnextPayloadLabel hnextPayloadBit hnextPayloadFlag
      hnextFlagBound
  have hadvanceFlag : next.flag =
      if carrier.route.payload ≤ trailingZeros carrier.route.target then
        1 - carrier.flag else carrier.flag := by
    calc
      next.flag = nextFlag := hnextFlag
      _ = if groupID ring.hn C
              (stableGroupStart ring leaderPos ψ source) ≤
            groupID ring.hn C targetStart
          then 1 - carrier.flag else carrier.flag := by
        exact hflagUpdate
      _ = if carrier.route.payload ≤ trailingZeros carrier.route.target then
            1 - carrier.flag else carrier.flag := by
        rw [hstableTarget, htargetID,
          ← carrier.route.payload_from_source]
  have hnextHistory : RulerOverwritingHistory ring D leaderPos next :=
    RulerOverwritingHistory.advance ring C D leaderPos carrier next history
      (by rw [hnextPayload])
      (by rw [hnextTarget])
      hadvanceFlag
  have hactionNextRaw :=
    relocateWriterSchedule_preserves_later_stable_group hψ ring leaderPos
      (future := target + 1) (window := target - 1) (by omega) hnextRange T C
      actionSchedule
      (WriterSelectedActionOutcome.nonwrapping hp
        (fun k => (C (groupOffset ring targetStart k)).bit)
        payload carrier.flag actionSchedule nextPayload houtcome)
  have hactionNext : ∀ k, k < ψ →
      A (groupOffset ring
        (stableGroupStart ring leaderPos ψ (target + 1)) k) =
      C (groupOffset ring
        (stableGroupStart ring leaderPos ψ (target + 1)) k) := by
    intro k hk
    exact hactionNextRaw k hk
  have htransportNextBits : ∀ k, k < ψ →
      (D (groupOffset ring
        (stableGroupStart ring leaderPos ψ (target + 1)) k)).bit =
      (A (groupOffset ring
        (stableGroupStart ring leaderPos ψ (target + 1)) k)).bit := by
    intro k hk
    have hbitK := htransport.2.2.2 (genericWriterPos hp (ψ + k))
    unfold writerWindowPullback at hbitK
    rw [writerWindowEmbed_target hp ring targetStart hk,
      ← hnextTargetStart] at hbitK
    exact hbitK
  have hnextGroupID : groupID ring.hn D
      (stableGroupStart ring leaderPos ψ (target + 1)) =
      groupID ring.hn C
        (stableGroupStart ring leaderPos ψ (target + 1)) := by
    apply groupID_eq_of_bits ring D C _ _
    intro k hk
    rw [htransportNextBits k hk]
    exact congrArg AgentState.bit (hactionNext k hk)
  have hfuturePreserved : ∀ future, target + 1 < future →
      future < n / ψ → ∀ k, k < ψ →
        D (groupOffset ring
          (stableGroupStart ring leaderPos ψ future) k) =
        C (groupOffset ring
          (stableGroupStart ring leaderPos ψ future) k) := by
    intro future hfuture hfutureRange k hk
    have hactionFutureRaw :=
      relocateWriterSchedule_preserves_later_stable_group hψ ring leaderPos
        (future := future) (window := target - 1) (by omega) hfutureRange T C
        actionSchedule
        (WriterSelectedActionOutcome.nonwrapping hp
          (fun k => (C (groupOffset ring targetStart k)).bit)
          payload carrier.flag actionSchedule nextPayload houtcome)
    have hactionFuture :
        A (groupOffset ring
          (stableGroupStart ring leaderPos ψ future) k) =
        C (groupOffset ring
          (stableGroupStart ring leaderPos ψ future) k) := by
      exact hactionFutureRaw k hk
    have htransportFutureRaw :=
      relocateWriterSchedule_preserves_later_stable_group hψ ring leaderPos
        (future := future) (window := target) (by omega) hfutureRange T A
        transportSchedule (writerBlockTransportSchedule_nonwrapping hp)
    have htransportFuture :
        D (groupOffset ring
          (stableGroupStart ring leaderPos ψ future) k) =
        A (groupOffset ring
          (stableGroupStart ring leaderPos ψ future) k) := by
      simpa [D, transportLarge, hstableTarget] using
        htransportFutureRaw k hk
    exact htransportFuture.trans hactionFuture
  let schedule := actionLarge ++ transportLarge
  have hcombined : _root_.applySchedule ring T C schedule = D := by
    rw [show schedule = actionLarge ++ transportLarge by rfl,
      applySchedule_append]
  refine ⟨schedule, nextPayload, ?_⟩
  change ∃ next' : SourceTaggedCompleteOverwritingCarrier
      ring (_root_.applySchedule ring T C schedule)
        (_root_.applySchedule ring T C schedule) leaderPos,
    next'.route.source = carrier.route.source ∧
      next'.route.target = carrier.route.target + 1 ∧
      next'.route.payload = carrier.route.payload ∧
      RulerOverwritingHistory ring (_root_.applySchedule ring T C schedule)
        leaderPos next' ∧
      WriterRoundState hp
        (writerWindowPullback ring
          (stableGroupStart ring leaderPos ψ carrier.route.target)
          (_root_.applySchedule ring T C schedule)) nextPayload ψ ∧
      (∀ i, WriterTransportCleanFrame
        ((writerWindowPullback ring
          (stableGroupStart ring leaderPos ψ carrier.route.target)
          (_root_.applySchedule ring T C schedule)) i)) ∧
      WriterLabelFrame hp
        (writerWindowPullback ring
          (stableGroupStart ring leaderPos ψ carrier.route.target)
          (_root_.applySchedule ring T C schedule)) ∧
      (∀ k, k < ψ → (nextPayload k).label = k) ∧
      (∀ k, k < ψ →
        (nextPayload k).bit = boolBitValue
          ((_root_.applySchedule ring T C schedule)
            (groupOffset ring
              (stableGroupStart ring leaderPos ψ next'.route.source) k)).bit) ∧
      (∀ k, k < ψ → (nextPayload k).flag = next'.flag) ∧
      groupID ring.hn (_root_.applySchedule ring T C schedule)
          (stableGroupStart ring leaderPos ψ (carrier.route.target + 1)) =
        groupID ring.hn C
          (stableGroupStart ring leaderPos ψ (carrier.route.target + 1)) ∧
      (∀ future, carrier.route.target + 1 < future →
        future < n / ψ → ∀ k, k < ψ →
          (_root_.applySchedule ring T C schedule)
              (groupOffset ring
                (stableGroupStart ring leaderPos ψ future) k) =
            C (groupOffset ring
              (stableGroupStart ring leaderPos ψ future) k))
  rw [hcombined]
  have hroundNext : WriterRoundState hp
      (writerWindowPullback ring
        (stableGroupStart ring leaderPos ψ carrier.route.target) D)
      nextPayload ψ := by
    rw [← hstableTarget]
    exact htransport.1
  have hcleanNext : ∀ i, WriterTransportCleanFrame
      ((writerWindowPullback ring
        (stableGroupStart ring leaderPos ψ carrier.route.target) D) i) := by
    rw [← hstableTarget]
    exact htransport.2.1
  have hlabelNext : WriterLabelFrame hp
      (writerWindowPullback ring
        (stableGroupStart ring leaderPos ψ carrier.route.target) D) := by
    rw [← hstableTarget]
    exact htransport.2.2.1
  have hnextPayloadBit' : ∀ k, k < ψ →
      (nextPayload k).bit = boolBitValue
        (D (groupOffset ring
          (stableGroupStart ring leaderPos ψ next.route.source) k)).bit := by
    intro k hk
    rw [hnextSource]
    exact hnextPayloadBit k hk
  have hnextPayloadFlag' : ∀ k, k < ψ →
      (nextPayload k).flag = next.flag := by
    intro k hk
    exact (hnextPayloadFlag k hk).trans hnextFlag.symm
  exact ⟨next, hnextSource, hnextTarget, hnextPayload, hnextHistory,
    hroundNext, hcleanNext, hlabelNext, hnextPayloadLabel,
    hnextPayloadBit', hnextPayloadFlag', hnextGroupID, hfuturePreserved⟩

/-- The reusable ruler-writer state advances one target while consuming only
the next fresh group.  All later fresh/stable groups are preserved pointwise,
so the result has the same induction-state type at `target+1`. -/
theorem RulerWriterAtTarget.exists_next
    {ψ n : Nat} (hψ : 1 < ψ) (ring : DirectedRing n)
    (leaderPos : Fin n) (C : Fin n → AgentState ψ) (target : Nat)
    (state : RulerWriterAtTarget (by omega) ring C leaderPos target)
    (hnextRange : target + 1 < n / ψ) :
    ∃ schedule : DetSchedule n,
      let D := _root_.applySchedule ring
        (writeSeqPersistentComparisonTransportLifecycle (by omega)) C schedule
      Nonempty (RulerWriterAtTarget (by omega) ring D leaderPos (target + 1)) := by
  let hp : 0 < ψ := by omega
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  have hbound : (target + 2) * ψ ≤ n := by
    have hcoeff : target + 2 ≤ n / ψ := by omega
    exact Nat.le_trans (Nat.mul_le_mul_right ψ hcoeff)
      (Nat.div_mul_le_self n ψ)
  have hnextFresh : ∀ k, k < ψ →
      let u := C (groupOffset ring
        (stableGroupStart ring leaderPos ψ (target - 1)) (2 * ψ + k))
      u.path3 = none ∧ WriterTransportCleanFrame u ∧ u.label.val = k := by
    intro k hk
    have hfresh := state.fresh_suffix (target + 1) (by omega) hnextRange
    have hcoord : groupOffset ring
        (stableGroupStart ring leaderPos ψ (target - 1)) (2 * ψ + k) =
      groupOffset ring (stableGroupStart ring leaderPos ψ (target + 1)) k := by
      rw [← groupOffset_compose,
        ← stableGroupStart_add_two_eq_groupOffset (ψ := ψ) ring leaderPos
          (target - 1)]
      have hindex : target - 1 + 2 = target + 1 := by
        have htargetPos : 0 < target := by
          rw [← state.carrier_target]
          exact state.history.target_pos
        omega
      rw [hindex]
    rw [hcoord]
    exact hfresh.1 k hk
  have hphysical := RulerOverwritingHistory.exists_next_physical hψ ring
    leaderPos C state.carrier state.history
    (by rw [state.carrier_target]; exact state.source_lt_target)
    (by rw [state.carrier_target]; exact hnextRange)
    (by rw [state.carrier_target]; exact hbound)
    state.payload state.payload_label state.payload_bit state.payload_flag
    (by simpa [state.carrier_target] using state.round)
    (by simpa [state.carrier_target] using state.clean)
    (by simpa [state.carrier_target] using state.labels)
    (by simpa [state.carrier_target] using hnextFresh)
    (by simpa [state.carrier_target] using state.target_id)
  obtain ⟨schedule, nextPayload, hresult⟩ := hphysical
  let D := _root_.applySchedule ring T C schedule
  change ∃ next : SourceTaggedCompleteOverwritingCarrier ring D D leaderPos,
      next.route.source = state.carrier.route.source ∧
        next.route.target = state.carrier.route.target + 1 ∧
        next.route.payload = state.carrier.route.payload ∧
        RulerOverwritingHistory ring D leaderPos next ∧
        WriterRoundState hp
          (writerWindowPullback ring
            (stableGroupStart ring leaderPos ψ state.carrier.route.target) D)
          nextPayload ψ ∧
        (∀ i, WriterTransportCleanFrame
          ((writerWindowPullback ring
            (stableGroupStart ring leaderPos ψ state.carrier.route.target) D) i)) ∧
        WriterLabelFrame hp
          (writerWindowPullback ring
            (stableGroupStart ring leaderPos ψ state.carrier.route.target) D) ∧
        (∀ k, k < ψ → (nextPayload k).label = k) ∧
        (∀ k, k < ψ →
          (nextPayload k).bit = boolBitValue
            (D (groupOffset ring
              (stableGroupStart ring leaderPos ψ next.route.source) k)).bit) ∧
        (∀ k, k < ψ → (nextPayload k).flag = next.flag) ∧
        groupID ring.hn D
            (stableGroupStart ring leaderPos ψ
              (state.carrier.route.target + 1)) =
          groupID ring.hn C
            (stableGroupStart ring leaderPos ψ
              (state.carrier.route.target + 1)) ∧
        (∀ future, state.carrier.route.target + 1 < future →
          future < n / ψ → ∀ k, k < ψ →
            D (groupOffset ring
              (stableGroupStart ring leaderPos ψ future) k) =
            C (groupOffset ring
              (stableGroupStart ring leaderPos ψ future) k)) at hresult
  obtain ⟨next, hnextSource, hnextTarget, hnextPayload, hnextHistory,
    hnextRound, hnextClean, hnextLabels, hnextPayloadLabel,
    hnextPayloadBit, hnextPayloadFlag, hnextGroupID,
    hfuturePreserved⟩ := hresult
  have htargetPos : 0 < target := by
    rw [← state.carrier_target]
    exact state.history.target_pos
  have holdNext := state.fresh_suffix (target + 1) (by omega) hnextRange
  have hnextTargetID : groupID ring.hn D
      (stableGroupStart ring leaderPos ψ (target + 1)) =
        trailingZeros (target + 1) := by
    calc
      groupID ring.hn D
          (stableGroupStart ring leaderPos ψ (target + 1)) =
        groupID ring.hn C
          (stableGroupStart ring leaderPos ψ (target + 1)) := by
            simpa [state.carrier_target] using hnextGroupID
      _ = trailingZeros (target + 1) := holdNext.2
  have hnextFreshSuffix : WriterFreshStableSuffix ring D leaderPos
      (target + 1) := by
    intro future hfuture hfutureRange
    have hold := state.fresh_suffix future (by omega) hfutureRange
    have hpreserve : ∀ k, k < ψ →
        D (groupOffset ring
          (stableGroupStart ring leaderPos ψ future) k) =
        C (groupOffset ring
          (stableGroupStart ring leaderPos ψ future) k) := by
      intro k hk
      exact hfuturePreserved future (by
        rw [state.carrier_target]
        exact hfuture) hfutureRange k hk
    refine ⟨?_, ?_⟩
    · intro k hk
      have holdK := hold.1 k hk
      rw [hpreserve k hk]
      exact holdK
    · have hgroupEq : groupID ring.hn D
          (stableGroupStart ring leaderPos ψ future) =
          groupID ring.hn C
            (stableGroupStart ring leaderPos ψ future) := by
        apply groupID_eq_of_bits ring D C _ _
        intro k hk
        exact congrArg AgentState.bit (hpreserve k hk)
      rw [hgroupEq]
      exact hold.2
  have hnextState : RulerWriterAtTarget hp ring D leaderPos (target + 1) :=
    { carrier := next
      carrier_target := by rw [hnextTarget, state.carrier_target]
      source_lt_target := by
        rw [hnextSource]
        exact Nat.lt_trans state.source_lt_target (by omega)
      history := hnextHistory
      payload := nextPayload
      payload_label := hnextPayloadLabel
      payload_bit := hnextPayloadBit
      payload_flag := hnextPayloadFlag
      round := by
        simpa [state.carrier_target, show target + 1 - 1 = target by omega]
          using hnextRound
      clean := by
        simpa [state.carrier_target, show target + 1 - 1 = target by omega]
          using hnextClean
      labels := by
        simpa [state.carrier_target, show target + 1 - 1 = target by omega]
          using hnextLabels
      target_id := hnextTargetID
      fresh_suffix := hnextFreshSuffix }
  exact ⟨schedule, ⟨hnextState⟩⟩

/-- **Finite arbitrary-width ruler traversal.** Repeatedly composing the
phase-correct physical step advances one certified writer through any finite
prefix of the fresh stable suffix.  The witness is one concrete concatenated
directed-edge schedule. -/
theorem RulerWriterAtTarget.exists_after_steps
    {ψ n : Nat} (hψ : 1 < ψ) (ring : DirectedRing n)
    (leaderPos : Fin n) (steps : Nat)
    (C : Fin n → AgentState ψ) (target : Nat)
    (state : RulerWriterAtTarget (by omega) ring C leaderPos target)
    (hfinalRange : target + steps < n / ψ) :
    ∃ schedule : DetSchedule n,
      let D := _root_.applySchedule ring
        (writeSeqPersistentComparisonTransportLifecycle (by omega)) C schedule
      Nonempty
        (RulerWriterAtTarget (by omega) ring D leaderPos (target + steps)) := by
  induction steps generalizing C target with
  | zero =>
      refine ⟨[], ?_⟩
      simpa [applySchedule] using Nonempty.intro state
  | succ steps ih =>
      have hmidRange : target + steps < n / ψ := by omega
      obtain ⟨first, hmid⟩ := ih C target state hmidRange
      let T := writeSeqPersistentComparisonTransportLifecycle (by omega : 0 < ψ)
      let C₁ := _root_.applySchedule ring T C first
      change (Nonempty
        (RulerWriterAtTarget (by omega) ring C₁ leaderPos (target + steps))) at hmid
      obtain ⟨midState⟩ := hmid
      obtain ⟨second, hnext⟩ := RulerWriterAtTarget.exists_next hψ ring
        leaderPos C₁ (target + steps) midState (by omega)
      let C₂ := _root_.applySchedule ring T C₁ second
      change Nonempty (RulerWriterAtTarget (by omega) ring C₂ leaderPos
        (target + steps + 1)) at hnext
      let schedule := first ++ second
      have hcombined : _root_.applySchedule ring T C schedule = C₂ := by
        rw [show schedule = first ++ second by rfl, applySchedule_append]
      refine ⟨schedule, ?_⟩
      rw [hcombined]
      simpa [Nat.add_assoc] using hnext

/-! ## Clean target-one base -/

/-- A source-authenticated flag-one writer at stable group zero enters the
reusable ruler traversal state after one real block transport to group one.
This is the clean-regime base; protocol birth/cleanup must still establish its
round-zero and fresh-suffix premises. -/
theorem RulerWriterAtTarget.exists_target_one_base
    {ψ n : Nat} (hψ : 1 < ψ) (ring : DirectedRing n)
    (leaderPos : Fin n) (C : Fin n → AgentState ψ)
    (payload : Nat → Path3Info) (honeRange : 1 < n / ψ)
    (hpayloadLabel : ∀ k, k < ψ → (payload k).label = k)
    (hpayloadBit : ∀ k, k < ψ →
      (payload k).bit = boolBitValue
        (C (groupOffset ring
          (stableGroupStart ring leaderPos ψ 0) k)).bit)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = 1)
    (hstate : WriterRoundState (by omega)
      (writerWindowPullback ring
        (stableGroupStart ring leaderPos ψ 0) C) payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame
      ((writerWindowPullback ring
        (stableGroupStart ring leaderPos ψ 0) C) i))
    (hlabel : WriterLabelFrame (by omega)
      (writerWindowPullback ring
        (stableGroupStart ring leaderPos ψ 0) C))
    (hfresh : WriterFreshStableSuffix ring C leaderPos 0) :
    ∃ schedule : DetSchedule n,
      let D := _root_.applySchedule ring
        (writeSeqPersistentComparisonTransportLifecycle (by omega)) C schedule
      Nonempty (RulerWriterAtTarget (by omega) ring D leaderPos 1) := by
  let hp : 0 < ψ := by omega
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let start := stableGroupStart ring leaderPos ψ 0
  have hwindow : 2 * ψ ≤ n := by
    have hcoeff : 2 ≤ n / ψ := by omega
    exact Nat.le_trans (Nat.mul_le_mul_right ψ hcoeff)
      (Nat.div_mul_le_self n ψ)
  let schedule := writerBlockTransportSchedule
    (genericWriterRing hp) (genericWriterStart hp) ψ
  let D := _root_.applySchedule ring T C
    (relocateWriterSchedule ring start schedule)
  have htransport := writerBlockTransportSchedule_relocated_from_zero hψ ring
    start hwindow C payload hpayloadLabel hstate hclean hlabel
  change WriterRoundState hp (writerWindowPullback ring start D) payload ψ ∧
      (∀ i, WriterTransportCleanFrame
        ((writerWindowPullback ring start D) i)) ∧
      WriterLabelFrame hp (writerWindowPullback ring start D) ∧
      WriterBitFrame (writerWindowPullback ring start C)
        (writerWindowPullback ring start D) at htransport
  have htargetStart : stableGroupStart ring leaderPos ψ 1 =
      groupOffset ring start ψ := by
    simpa [start] using
      stableGroupStart_succ_eq_groupOffset (ψ := ψ) ring leaderPos 0
  have hsourceBits : ∀ k, k < ψ →
      (D (groupOffset ring
        (stableGroupStart ring leaderPos ψ 0) k)).bit =
      (C (groupOffset ring
        (stableGroupStart ring leaderPos ψ 0) k)).bit := by
    intro k hk
    have hbitK := htransport.2.2.2 (genericWriterPos hp k)
    unfold writerWindowPullback at hbitK
    have hcoord : writerWindowEmbed ring start (genericWriterPos hp k) =
        groupOffset ring start k := by
      unfold writerWindowEmbed
      rw [genericWriterPos_val_of_lt hp (by omega)]
    rw [hcoord] at hbitK
    exact hbitK
  have hpayloadBitD : ∀ k, k < ψ →
      (payload k).bit = boolBitValue
        (D (groupOffset ring
          (stableGroupStart ring leaderPos ψ 0) k)).bit := by
    intro k hk
    rw [hpayloadBit k hk, hsourceBits k hk]
  have hsourceGroupID : groupID ring.hn D
      (stableGroupStart ring leaderPos ψ 0) =
      groupID ring.hn C (stableGroupStart ring leaderPos ψ 0) := by
    apply groupID_eq_of_bits ring D C _ _
    exact hsourceBits
  have htargetBits : ∀ k, k < ψ →
      (D (groupOffset ring
        (stableGroupStart ring leaderPos ψ 1) k)).bit =
      (C (groupOffset ring
        (stableGroupStart ring leaderPos ψ 1) k)).bit := by
    intro k hk
    have hbitK := htransport.2.2.2 (genericWriterPos hp (ψ + k))
    unfold writerWindowPullback at hbitK
    rw [writerWindowEmbed_target hp ring start hk, ← htargetStart] at hbitK
    exact hbitK
  have htargetGroupID : groupID ring.hn D
      (stableGroupStart ring leaderPos ψ 1) =
      groupID ring.hn C (stableGroupStart ring leaderPos ψ 1) := by
    apply groupID_eq_of_bits ring D C _ _
    exact htargetBits
  obtain ⟨carrier, hcarrierSource, hcarrierTarget, hcarrierPayload,
      hcarrierFlag⟩ :=
    WriterRoundState.existsSourceTaggedCarrier hp ring leaderPos start D payload
      0 1 (groupID ring.hn D (stableGroupStart ring leaderPos ψ 0)) 1
      (by omega) honeRange htargetStart rfl htransport.1 hpayloadLabel
      hpayloadBitD hpayloadFlag (by omega)
  have hhistory : RulerOverwritingHistory ring D leaderPos carrier := by
    refine ⟨?_, ?_⟩
    · rw [hcarrierTarget]
      omega
    · rw [hcarrierFlag, hcarrierTarget]
      simp [rulerWriterFlagBefore]
  have htargetID : groupID ring.hn D
      (stableGroupStart ring leaderPos ψ 1) = trailingZeros 1 := by
    rw [htargetGroupID]
    exact (hfresh 1 (by omega) honeRange).2
  have hfreshD : WriterFreshStableSuffix ring D leaderPos 1 := by
    intro future hfuture hfutureRange
    have hold := hfresh future (by omega) hfutureRange
    have hpreserveRaw := relocateWriterSchedule_preserves_later_stable_group
      hψ ring leaderPos (future := future) (window := 0) (by omega)
      hfutureRange T C schedule
      (writerBlockTransportSchedule_nonwrapping hp)
    have hpreserve : ∀ k, k < ψ →
        D (groupOffset ring
          (stableGroupStart ring leaderPos ψ future) k) =
        C (groupOffset ring
          (stableGroupStart ring leaderPos ψ future) k) := by
      intro k hk
      exact hpreserveRaw k hk
    refine ⟨?_, ?_⟩
    · intro k hk
      rw [hpreserve k hk]
      exact hold.1 k hk
    · have hgid : groupID ring.hn D
          (stableGroupStart ring leaderPos ψ future) =
          groupID ring.hn C
            (stableGroupStart ring leaderPos ψ future) := by
        apply groupID_eq_of_bits ring D C _ _
        intro k hk
        exact congrArg AgentState.bit (hpreserve k hk)
      rw [hgid]
      exact hold.2
  have hbase : RulerWriterAtTarget hp ring D leaderPos 1 :=
    { carrier := carrier
      carrier_target := hcarrierTarget
      source_lt_target := by rw [hcarrierSource]; omega
      history := hhistory
      payload := payload
      payload_label := hpayloadLabel
      payload_bit := by
        intro k hk
        rw [hcarrierSource]
        exact hpayloadBitD k hk
      payload_flag := by
        intro k hk
        rw [hcarrierFlag]
        exact hpayloadFlag k hk
      round := by simpa [start] using htransport.1
      clean := by simpa [start] using htransport.2.1
      labels := by simpa [start] using htransport.2.2.1
      target_id := htargetID
      fresh_suffix := hfreshD }
  exact ⟨relocateWriterSchedule ring start schedule, ⟨hbase⟩⟩

end PPLLWriteSeqRulerHistory

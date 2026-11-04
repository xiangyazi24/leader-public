import Leader.Wu.WriteSeq.Relocation

/-!
# Arithmetic bridge from writer comparisons to the ruler history

The executable WRITE_SEQ schedules compare a target group and an attached
writer from their most significant bit to their least significant bit.  The
ruler certificate, by contrast, is phrased as an inequality between the two
numeric group IDs.  This module supplies the structural binary arithmetic that
connects those views.  It is part of the repair lane: no claim is made that the
paper stated these missing comparison lemmas.
-/

namespace PPLLWriteSeqRulerBridge

open PPLL PPLLWriteSeqPersistenceRepair
  PPLLWriteSeqPersistenceRegression PPLLWriteSeqUnequalRegression
  PPLLWriteSeqRelocation

/-! ## Most-significant-bit-first binary values -/

/-- Numeric value of one Boolean bit. -/
def boolBitValue (bit : Bool) : Nat :=
  if bit then 1 else 0

/-- The MSB-first value of the first `width` entries of `bits`.  Its weights
match `groupID`: entry zero has weight `2^(width-1)` and the last entry has
weight one. -/
def msbBitValue (width : Nat) (bits : Nat → Bool) : Nat :=
  ((List.range width).map fun k =>
    boolBitValue (bits k) * 2 ^ (width - 1 - k)).sum

/-- Removing the leading bit gives the standard recursive decomposition of an
MSB-first binary value. -/
theorem msbBitValue_succ (width : Nat) (bits : Nat → Bool) :
    msbBitValue (width + 1) bits =
      boolBitValue (bits 0) * 2 ^ width +
        msbBitValue width (fun k => bits (k + 1)) := by
  unfold msbBitValue
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.sum_cons, List.map_map,
    Nat.add_sub_cancel, Nat.sub_zero]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  have hklt : k < width := List.mem_range.mp hk
  have hoffset : width - (k + 1) = width - 1 - k := by omega
  change boolBitValue (bits (k + 1)) * 2 ^ (width - (k + 1)) = _
  rw [hoffset]

/-- A `width`-bit value is strictly below `2^width`.  This is the domination
fact that makes the first unequal bit decide the entire numeric comparison. -/
theorem msbBitValue_lt_two_pow (width : Nat) (bits : Nat → Bool) :
    msbBitValue width bits < 2 ^ width := by
  induction width generalizing bits with
  | zero => simp [msbBitValue]
  | succ width ih =>
      rw [show width + 1 = Nat.succ width by omega,
        msbBitValue_succ]
      have htail := ih (fun k => bits (k + 1))
      have hpow : 0 < 2 ^ width := Nat.pow_pos (by omega)
      cases bits 0 <;> simp [boolBitValue, Nat.pow_succ] <;> omega

/-- The first differing bit determines strict order: a zero on the left and a
one on the right makes the left binary value smaller, independently of the
suffix. -/
theorem msbBitValue_lt_of_first_mismatch
    {width mismatch : Nat} (left right : Nat → Bool)
    (hmismatch : mismatch < width)
    (hprefix : ∀ k, k < mismatch → left k = right k)
    (hleft : left mismatch = false)
    (hright : right mismatch = true) :
    msbBitValue width left < msbBitValue width right := by
  induction width generalizing mismatch left right with
  | zero => omega
  | succ width ih =>
      rw [msbBitValue_succ, msbBitValue_succ]
      cases mismatch with
      | zero =>
          have htail := msbBitValue_lt_two_pow width
            (fun k => left (k + 1))
          simp [hleft, hright, boolBitValue]
          omega
      | succ mismatch =>
          have hhead : left 0 = right 0 := hprefix 0 (by omega)
          have htail := ih (mismatch := mismatch)
            (left := fun k => left (k + 1))
            (right := fun k => right (k + 1)) (by omega)
            (by
              intro k hk
              exact hprefix (k + 1) (by omega))
            (by simpa [Nat.succ_eq_add_one] using hleft)
            (by simpa [Nat.succ_eq_add_one] using hright)
          rw [hhead]
          omega

/-- Pointwise equal bit families have equal MSB-first values. -/
theorem msbBitValue_eq_of_bits {width : Nat} (left right : Nat → Bool)
    (hequal : ∀ k, k < width → left k = right k) :
    msbBitValue width left = msbBitValue width right := by
  unfold msbBitValue
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  rw [hequal k (List.mem_range.mp hk)]

/-! ## Connection to physical group IDs -/

/-- `groupID` is exactly the abstract MSB-first value of the physical bits at
successive group offsets. -/
theorem groupID_eq_msbBitValue {ψ n : Nat} (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (start : Fin n) :
    groupID ring.hn C start =
      msbBitValue ψ (fun k => (C (groupOffset ring start k)).bit) := by
  unfold groupID msbBitValue groupOffset boolBitValue
  rw [List.sum_eq_foldl_nat, List.foldl_map]

/-- For two physical groups, a first `0/1` mismatch implies strict numeric
order in the same direction. -/
theorem groupID_lt_of_first_mismatch {ψ n : Nat} (ring : DirectedRing n)
    (leftC rightC : Fin n → AgentState ψ) (leftStart rightStart : Fin n)
    (mismatch : Nat) (hmismatch : mismatch < ψ)
    (hprefix : ∀ k, k < mismatch →
      (leftC (groupOffset ring leftStart k)).bit =
        (rightC (groupOffset ring rightStart k)).bit)
    (hleft : (leftC (groupOffset ring leftStart mismatch)).bit = false)
    (hright : (rightC (groupOffset ring rightStart mismatch)).bit = true) :
    groupID ring.hn leftC leftStart < groupID ring.hn rightC rightStart := by
  rw [groupID_eq_msbBitValue ring leftC leftStart,
    groupID_eq_msbBitValue ring rightC rightStart]
  exact msbBitValue_lt_of_first_mismatch _ _ hmismatch hprefix hleft hright

/-- Pointwise equal physical group bits give equal group IDs. -/
theorem groupID_eq_of_bits {ψ n : Nat} (ring : DirectedRing n)
    (leftC rightC : Fin n → AgentState ψ) (leftStart rightStart : Fin n)
    (hequal : ∀ k, k < ψ →
      (leftC (groupOffset ring leftStart k)).bit =
        (rightC (groupOffset ring rightStart k)).bit) :
    groupID ring.hn leftC leftStart = groupID ring.hn rightC rightStart := by
  rw [groupID_eq_msbBitValue ring leftC leftStart,
    groupID_eq_msbBitValue ring rightC rightStart]
  exact msbBitValue_eq_of_bits _ _ hequal

/-! ## Comparison orientation and source tags -/

/-- With a Boolean-valued payload bit, `checkBitWS` reports equality exactly
when the physical target bit equals the payload/source bit. -/
theorem checkBitWS_boolBitValue_eq_equal_iff (target source : Bool) :
    checkBitWS target (boolBitValue source) = .equal ↔ target = source := by
  cases target <;> cases source <;> simp [checkBitWS, boolBitValue]

/-- `larger` means target one and writer/source zero.  The argument order is
important: Algorithm 12 compares the physical target against the signal. -/
theorem checkBitWS_boolBitValue_eq_larger_iff (target source : Bool) :
    checkBitWS target (boolBitValue source) = .larger ↔
      target = true ∧ source = false := by
  cases target <;> cases source <;> simp [checkBitWS, boolBitValue]

/-- `less` means target zero and writer/source one. -/
theorem checkBitWS_boolBitValue_eq_less_iff (target source : Bool) :
    checkBitWS target (boolBitValue source) = .less ↔
      target = false ∧ source = true := by
  cases target <;> cases source <;> simp [checkBitWS, boolBitValue]

/-- Source authentication plus a first `larger` comparison gives the strict
order between the abstract payload and target bit families. -/
theorem msbBitValue_source_lt_target_of_first_larger
    {width mismatch : Nat} (source target : Nat → Bool)
    (payload : Nat → Path3Info) (hmismatch : mismatch < width)
    (hsource : ∀ k, k < width →
      (payload k).bit = boolBitValue (source k))
    (hprefix : ∀ k, k < mismatch →
      checkBitWS (target k) (payload k).bit = .equal)
    (hcomparison :
      checkBitWS (target mismatch) (payload mismatch).bit = .larger) :
    msbBitValue width source < msbBitValue width target := by
  apply msbBitValue_lt_of_first_mismatch source target hmismatch
  · intro k hk
    have hkcmp := hprefix k hk
    rw [hsource k (by omega)] at hkcmp
    exact (checkBitWS_boolBitValue_eq_equal_iff _ _).mp hkcmp |>.symm
  · rw [hsource mismatch hmismatch] at hcomparison
    exact (checkBitWS_boolBitValue_eq_larger_iff _ _).mp hcomparison |>.2
  · rw [hsource mismatch hmismatch] at hcomparison
    exact (checkBitWS_boolBitValue_eq_larger_iff _ _).mp hcomparison |>.1

/-- Source authentication plus a first `less` comparison gives the opposite
strict order. -/
theorem msbBitValue_target_lt_source_of_first_less
    {width mismatch : Nat} (source target : Nat → Bool)
    (payload : Nat → Path3Info) (hmismatch : mismatch < width)
    (hsource : ∀ k, k < width →
      (payload k).bit = boolBitValue (source k))
    (hprefix : ∀ k, k < mismatch →
      checkBitWS (target k) (payload k).bit = .equal)
    (hcomparison :
      checkBitWS (target mismatch) (payload mismatch).bit = .less) :
    msbBitValue width target < msbBitValue width source := by
  apply msbBitValue_lt_of_first_mismatch target source hmismatch
  · intro k hk
    have hkcmp := hprefix k hk
    rw [hsource k (by omega)] at hkcmp
    exact (checkBitWS_boolBitValue_eq_equal_iff _ _).mp hkcmp
  · rw [hsource mismatch hmismatch] at hcomparison
    exact (checkBitWS_boolBitValue_eq_less_iff _ _).mp hcomparison |>.1
  · rw [hsource mismatch hmismatch] at hcomparison
    exact (checkBitWS_boolBitValue_eq_less_iff _ _).mp hcomparison |>.2

/-- Source authentication and an all-equal scan identify the two abstract
binary values. -/
theorem msbBitValue_source_eq_target_of_all_equal {width : Nat}
    (source target : Nat → Bool) (payload : Nat → Path3Info)
    (hsource : ∀ k, k < width →
      (payload k).bit = boolBitValue (source k))
    (hequal : ∀ k, k < width →
      checkBitWS (target k) (payload k).bit = .equal) :
    msbBitValue width source = msbBitValue width target := by
  apply msbBitValue_eq_of_bits
  intro k hk
  have hkcmp := hequal k hk
  rw [hsource k hk] at hkcmp
  exact (checkBitWS_boolBitValue_eq_equal_iff _ _).mp hkcmp |>.symm

/-- Every bit comparison has one of the three states used by the schedule
split; no other `WriteState` constructor can be produced by Algorithm 12. -/
theorem checkBitWS_equal_or_larger_or_less (target : Bool) (payload : Nat) :
    checkBitWS target payload = .equal ∨
      checkBitWS target payload = .larger ∨
        checkBitWS target payload = .less := by
  cases target with
  | false =>
      by_cases hzero : payload = 0
      · simp [checkBitWS, hzero]
      · have hne : 0 ≠ payload := by omega
        simp [checkBitWS, hne]
  | true =>
      by_cases hone : payload = 1
      · simp [checkBitWS, hone]
      · have hne : 1 ≠ payload := by omega
        by_cases hgt : 1 > payload
        · simp [checkBitWS, hne, hgt]
        · simp [checkBitWS, hne, hgt]

/-- A finite comparison scan either finds the first unequal component, with
an exact equal prefix, or proves all components equal.  This structural split
is the schedule selector; it does not assume a numeric comparison in advance. -/
theorem first_writer_comparison_or_all_equal (width : Nat)
    (target : Nat → Bool) (payload : Nat → Nat) :
    (∀ k, k < width → checkBitWS (target k) (payload k) = .equal) ∨
      ∃ mismatch, mismatch < width ∧
        (∀ k, k < mismatch →
          checkBitWS (target k) (payload k) = .equal) ∧
        (checkBitWS (target mismatch) (payload mismatch) = .larger ∨
          checkBitWS (target mismatch) (payload mismatch) = .less) := by
  induction width generalizing target payload with
  | zero =>
      left
      intro k hk
      omega
  | succ width ih =>
      by_cases hhead : checkBitWS (target 0) (payload 0) = .equal
      · rcases ih (fun k => target (k + 1)) (fun k => payload (k + 1)) with
          htail | ⟨mismatch, hmismatch, hprefix, hcomparison⟩
        · left
          intro k hk
          cases k with
          | zero => exact hhead
          | succ k =>
              exact htail k (by omega)
        · right
          refine ⟨mismatch + 1, by omega, ?_, ?_⟩
          · intro k hk
            cases k with
            | zero => exact hhead
            | succ k =>
                exact hprefix k (by omega)
          · simpa [Nat.succ_eq_add_one] using hcomparison
      · right
        refine ⟨0, by omega, ?_, ?_⟩
        · intro k hk
          omega
        · rcases checkBitWS_equal_or_larger_or_less
            (target 0) (payload 0) with hequal | hlarger | hless
          · exact (hhead hequal).elim
          · exact Or.inl hlarger
          · exact Or.inr hless

/-- The finite scan plus a Boolean-valued common flag selects exactly one of
the three verified schedule families: equal/flag-one, equal/flag-zero, or an
unequal schedule with its concrete command. -/
theorem writer_action_cases (width : Nat) (target : Nat → Bool)
    (payload : Nat → Path3Info) (flag : Nat) (hflag : flag ≤ 1) :
    ((∀ k, k < width →
        checkBitWS (target k) (payload k).bit = .equal) ∧ flag = 1) ∨
      ((∀ k, k < width →
        checkBitWS (target k) (payload k).bit = .equal) ∧ flag = 0) ∨
      ∃ mismatch comparison command,
        mismatch < width ∧
        (∀ k, k < mismatch →
          checkBitWS (target k) (payload k).bit = .equal) ∧
        checkBitWS (target mismatch) (payload mismatch).bit = comparison ∧
        WriterUnequalCommand comparison flag command := by
  rcases first_writer_comparison_or_all_equal width target
      (fun k => (payload k).bit) with hall | hunequal
  · by_cases hone : flag = 1
    · exact Or.inl ⟨hall, hone⟩
    · right
      left
      exact ⟨hall, by omega⟩
  · obtain ⟨mismatch, hmismatch, hprefix, hlarger | hless⟩ := hunequal
    · by_cases hone : flag = 1
      · exact Or.inr (Or.inr ⟨mismatch, .larger, .overwrite,
          hmismatch, hprefix, hlarger, Or.inl ⟨rfl, hone, rfl⟩⟩)
      · have hzero : flag = 0 := by omega
        exact Or.inr (Or.inr ⟨mismatch, .larger, .move_flip,
          hmismatch, hprefix, hlarger,
          Or.inr (Or.inl ⟨rfl, hzero, rfl⟩)⟩)
    · exact Or.inr (Or.inr ⟨mismatch, .less, .move,
        hmismatch, hprefix, hless, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩)

/-! ## Payload preservation and flag update -/

/-- Unequal actions never change the authenticated payload label. -/
theorem writerUnequalPayload_label (command : WriteAction) (p : Path3Info) :
    (writerUnequalPayload command p).label = p.label := by
  cases command <;> rfl

/-- Unequal actions never change the authenticated payload bit.  Overwrite
changes the physical target bit, not the attached source bit. -/
theorem writerUnequalPayload_bit (command : WriteAction) (p : Path3Info) :
    (writerUnequalPayload command p).bit = p.bit := by
  cases command <;> rfl

/-- The command relation has exactly the flag semantics needed by the ruler
recurrence: `larger` complements the common flag, while `less` preserves it. -/
theorem WriterUnequalCommand.payload_flag
    {comparison : WriteState} {flag : Nat} {command : WriteAction}
    (hcommand : WriterUnequalCommand comparison flag command)
    (p : Path3Info) (hpflag : p.flag = flag) :
    (writerUnequalPayload command p).flag =
      if comparison = .larger then 1 - flag else flag := by
  rcases hcommand with ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [writerUnequalPayload, hpflag]

/-! ## Executable arbitrary-window case selection -/

/-- Exact relation between a finite comparison scan and the concrete schedule
and payload family selected for it.  The three alternatives correspond to the
three already-verified relocated schedule theorems. -/
def WriterSelectedOutcome {ψ : Nat} (hψ : 0 < ψ)
    (target : Nat → Bool) (payload : Nat → Path3Info) (flag : Nat)
    (schedule : DetSchedule (2 * ψ))
    (nextPayload : Nat → Path3Info) : Prop :=
  ((∀ k, k < ψ → checkBitWS (target k) (payload k).bit = .equal) ∧
      flag = 1 ∧ schedule = writerFirstEqualFlagOneSchedule hψ ∧
      nextPayload = fun k =>
        { payload k with flag := 1 - (payload k).flag }) ∨
    ((∀ k, k < ψ → checkBitWS (target k) (payload k).bit = .equal) ∧
      flag = 0 ∧ schedule = writerFirstEqualFlagZeroSchedule hψ ∧
      nextPayload = fun k =>
        { payload k with flag := 1 - (payload k).flag }) ∨
    ∃ mismatch comparison command,
      mismatch < ψ ∧
      (∀ k, k < mismatch →
        checkBitWS (target k) (payload k).bit = .equal) ∧
      checkBitWS (target mismatch) (payload mismatch).bit = comparison ∧
      WriterUnequalCommand comparison flag command ∧
      schedule = writerFirstUnequalSchedule hψ mismatch ∧
      nextPayload = fun k => writerUnequalPayload command (payload k)

/-- Every selected outcome preserves the attached source labels and bits and
updates one common flag exactly when the numeric source value is at most the
numeric target value.  This is the arithmetic side of
`RulerOverwritingHistory.advance`. -/
theorem WriterSelectedOutcome.payload_update {ψ : Nat} (hψ : 0 < ψ)
    (source target : Nat → Bool) (payload : Nat → Path3Info)
    (flag : Nat) (schedule : DetSchedule (2 * ψ))
    (nextPayload : Nat → Path3Info)
    (hsource : ∀ k, k < ψ →
      (payload k).bit = boolBitValue (source k))
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = flag)
    (houtcome : WriterSelectedOutcome hψ target payload flag schedule
      nextPayload) :
    ∃ nextFlag,
      (∀ k, k < ψ →
        (nextPayload k).label = (payload k).label ∧
        (nextPayload k).bit = (payload k).bit ∧
        (nextPayload k).flag = nextFlag) ∧
      nextFlag =
        if msbBitValue ψ source ≤ msbBitValue ψ target
        then 1 - flag else flag := by
  rcases houtcome with
      ⟨hequal, hflag, _, rfl⟩ | ⟨hequal, hflag, _, rfl⟩ |
        ⟨mismatch, comparison, command, hmismatch, hprefix,
          hcomparison, hcommand, _, rfl⟩
  · refine ⟨1 - flag, ?_, ?_⟩
    · intro k hk
      simp [hpayloadFlag k hk]
    · have hid := msbBitValue_source_eq_target_of_all_equal
        source target payload hsource hequal
      rw [hid]
      simp
  · refine ⟨1 - flag, ?_, ?_⟩
    · intro k hk
      simp [hpayloadFlag k hk]
    · have hid := msbBitValue_source_eq_target_of_all_equal
        source target payload hsource hequal
      rw [hid]
      simp
  · rcases hcommand with ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hlt := msbBitValue_source_lt_target_of_first_larger
        source target payload hmismatch hsource hprefix hcomparison
      refine ⟨0, ?_, ?_⟩
      · intro k hk
        simp [writerUnequalPayload, hpayloadFlag k hk]
      · simp [Nat.le_of_lt hlt]
    · have hlt := msbBitValue_source_lt_target_of_first_larger
        source target payload hmismatch hsource hprefix hcomparison
      refine ⟨1, ?_, ?_⟩
      · intro k hk
        simp [writerUnequalPayload, hpayloadFlag k hk]
      · simp [Nat.le_of_lt hlt]
    · have hlt := msbBitValue_target_lt_source_of_first_less
        source target payload hmismatch hsource hprefix hcomparison
      refine ⟨flag, ?_, ?_⟩
      · intro k hk
        simp [writerUnequalPayload, hpayloadFlag k hk]
      · simp [Nat.not_le_of_lt hlt]

/-- The target bit seen at offset `ψ+k` of the current pullback is the physical
bit at offset `k` of the next group start. -/
theorem writerWindowPullback_target_bit {ψ n k : Nat} (hψ : 0 < ψ)
    (ring : DirectedRing n) (start : Fin n)
    (C : Fin n → AgentState ψ) (hk : k < ψ) :
    ((writerWindowPullback ring start C)
      (genericWriterPos hψ (ψ + k))).bit =
        (C (groupOffset ring (groupOffset ring start ψ) k)).bit := by
  change (C (writerWindowEmbed ring start
    (genericWriterPos hψ (ψ + k)))).bit = _
  rw [← writerWindowEmbed_next_source hψ ring start hk]
  unfold writerWindowEmbed
  rw [genericWriterPos_val_of_lt hψ (by omega)]

/-- Physical specialization of `payload_update`: the selected schedule's
common flag changes exactly when the source-group `groupID` is at most the
target-group `groupID`. -/
theorem WriterSelectedOutcome.payload_update_groupID
    {ψ n : Nat} (hψ : 0 < ψ) (ring : DirectedRing n) (start : Fin n)
    (reference : Fin n → AgentState ψ) (payload : Nat → Path3Info)
    (flag : Nat) (schedule : DetSchedule (2 * ψ))
    (nextPayload : Nat → Path3Info)
    (hsource : ∀ k, k < ψ →
      (payload k).bit = boolBitValue
        (reference (groupOffset ring start k)).bit)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = flag)
    (houtcome : WriterSelectedOutcome hψ
      (fun k => ((writerWindowPullback ring start reference)
        (genericWriterPos hψ (ψ + k))).bit)
      payload flag schedule nextPayload) :
    ∃ nextFlag,
      (∀ k, k < ψ →
        (nextPayload k).label = (payload k).label ∧
        (nextPayload k).bit = (payload k).bit ∧
        (nextPayload k).flag = nextFlag) ∧
      nextFlag =
        if groupID ring.hn reference start ≤
            groupID ring.hn reference (groupOffset ring start ψ)
        then 1 - flag else flag := by
  let source := fun k => (reference (groupOffset ring start k)).bit
  let target := fun k => ((writerWindowPullback ring start reference)
    (genericWriterPos hψ (ψ + k))).bit
  obtain ⟨nextFlag, hfields, hupdate⟩ :=
    WriterSelectedOutcome.payload_update hψ source target payload flag
      schedule nextPayload (by simpa [source] using hsource)
      hpayloadFlag (by simpa [target] using houtcome)
  have hsourceValue : msbBitValue ψ source =
      groupID ring.hn reference start := by
    exact (groupID_eq_msbBitValue ring reference start).symm
  have htargetValue : msbBitValue ψ target =
      groupID ring.hn reference (groupOffset ring start ψ) := by
    rw [groupID_eq_msbBitValue]
    apply msbBitValue_eq_of_bits
    intro k hk
    exact writerWindowPullback_target_bit hψ ring start reference hk
  refine ⟨nextFlag, hfields, ?_⟩
  rw [hsourceValue, htargetValue] at hupdate
  exact hupdate

/-- **Arbitrary-window schedule selector.** From one canonical writer-round
state, the actual target bits select a concrete equal or unequal schedule.
Executing that schedule in the large ring yields round zero at the next
window, with the exact transformed payload family recorded by
`WriterSelectedOutcome`. -/
theorem writerActionSchedule_relocated_toNextRoundState_exists
    {ψ n : Nat} (hψ : 1 < ψ)
    (ring : DirectedRing n) (start : Fin n) (hthree : 3 * ψ ≤ n)
    (C reference : Fin n → AgentState ψ) (payload : Nat → Path3Info)
    (flag : Nat) (hflag : flag ≤ 1)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = flag)
    (hstate : WriterRoundState (by omega)
      (writerWindowPullback ring start C) payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame
      ((writerWindowPullback ring start C) i))
    (hlabel : WriterLabelFrame (by omega)
      (writerWindowPullback ring start C))
    (hbit : WriterBitFrame (writerWindowPullback ring start reference)
      (writerWindowPullback ring start C))
    (hnextEmpty : ∀ k, k < ψ →
      (C (groupOffset ring start (2 * ψ + k))).path3 = none) :
    let target := fun k =>
      ((writerWindowPullback ring start reference)
        (genericWriterPos (by omega) (ψ + k))).bit
    ∃ schedule nextPayload,
      WriterSelectedOutcome (ψ := ψ) (by omega) target payload flag schedule
          nextPayload ∧
        let largeAfter := _root_.applySchedule ring
          (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
          (relocateWriterSchedule ring start schedule)
        WriterRoundState (by omega)
          (writerWindowPullback ring (groupOffset ring start ψ) largeAfter)
          nextPayload 0 := by
  let hp : 0 < ψ := by omega
  let target := fun k =>
    ((writerWindowPullback ring start reference)
      (genericWriterPos hp (ψ + k))).bit
  rcases writer_action_cases ψ target payload flag hflag with
      ⟨hequal, hflagOne⟩ | ⟨hequal, hflagZero⟩ |
        ⟨mismatch, comparison, command, hmismatch, hprefix,
          hcomparison, hcommand⟩
  · refine ⟨writerFirstEqualFlagOneSchedule hp,
      (fun k => { payload k with flag := 1 - (payload k).flag }), ?_, ?_⟩
    · exact Or.inl ⟨hequal, hflagOne, rfl, rfl⟩
    · exact writerFirstEqualFlagOneSchedule_relocated_toNextRoundState
        hψ ring start hthree C reference payload hpayload
        (by simpa [target] using hequal)
        (by
          intro k hk
          rw [hpayloadFlag k hk, hflagOne])
        hstate hclean hlabel hbit hnextEmpty
  · refine ⟨writerFirstEqualFlagZeroSchedule hp,
      (fun k => { payload k with flag := 1 - (payload k).flag }), ?_, ?_⟩
    · exact Or.inr (Or.inl ⟨hequal, hflagZero, rfl, rfl⟩)
    · exact writerFirstEqualFlagZeroSchedule_relocated_toNextRoundState
        hψ ring start hthree C reference payload hpayload
        (by simpa [target] using hequal)
        (by
          intro k hk
          rw [hpayloadFlag k hk, hflagZero])
        hstate hclean hlabel hbit hnextEmpty
  · refine ⟨writerFirstUnequalSchedule hp mismatch,
      (fun k => writerUnequalPayload command (payload k)), ?_, ?_⟩
    · exact Or.inr (Or.inr ⟨mismatch, comparison, command, hmismatch,
        hprefix, hcomparison, hcommand, rfl, rfl⟩)
    · exact writerFirstUnequalSchedule_relocated_toNextRoundState
        hψ ring start hthree C reference payload mismatch comparison flag
        command hmismatch hpayload hpayloadFlag
        (by simpa [target] using hprefix)
        (by simpa [target] using hcomparison) hcommand hstate hclean hlabel
        hbit hnextEmpty

/-- **C4 arithmetic/execution join.** A source-authenticated complete writer
in an arbitrary large-ring window chooses and executes one concrete schedule,
reappears as round zero of the next window, preserves every attached source
label and bit, and updates its common flag by the exact numeric ruler test
`sourceID ≤ targetID`.  No comparison result or action command is supplied by
the caller. -/
theorem writerActionSchedule_relocated_toNextRoundState_with_groupID_update
    {ψ n : Nat} (hψ : 1 < ψ)
    (ring : DirectedRing n) (start : Fin n) (hthree : 3 * ψ ≤ n)
    (C reference : Fin n → AgentState ψ) (payload : Nat → Path3Info)
    (flag : Nat) (hflag : flag ≤ 1)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hsource : ∀ k, k < ψ →
      (payload k).bit = boolBitValue
        (reference (groupOffset ring start k)).bit)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = flag)
    (hstate : WriterRoundState (by omega)
      (writerWindowPullback ring start C) payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame
      ((writerWindowPullback ring start C) i))
    (hlabel : WriterLabelFrame (by omega)
      (writerWindowPullback ring start C))
    (hbit : WriterBitFrame (writerWindowPullback ring start reference)
      (writerWindowPullback ring start C))
    (hnextEmpty : ∀ k, k < ψ →
      (C (groupOffset ring start (2 * ψ + k))).path3 = none) :
    let target := fun k =>
      ((writerWindowPullback ring start reference)
        (genericWriterPos (by omega) (ψ + k))).bit
    ∃ schedule nextPayload nextFlag,
      WriterSelectedOutcome (ψ := ψ) (by omega) target payload flag schedule
          nextPayload ∧
        (let largeAfter := _root_.applySchedule ring
          (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
          (relocateWriterSchedule ring start schedule)
        WriterRoundState (by omega)
          (writerWindowPullback ring (groupOffset ring start ψ) largeAfter)
          nextPayload 0) ∧
        (∀ k, k < ψ →
          (nextPayload k).label = (payload k).label ∧
          (nextPayload k).bit = (payload k).bit ∧
          (nextPayload k).flag = nextFlag) ∧
        nextFlag =
          if groupID ring.hn reference start ≤
              groupID ring.hn reference (groupOffset ring start ψ)
          then 1 - flag else flag := by
  let hp : 0 < ψ := by omega
  let target := fun k =>
    ((writerWindowPullback ring start reference)
      (genericWriterPos hp (ψ + k))).bit
  obtain ⟨schedule, nextPayload, houtcome, hround⟩ :=
    writerActionSchedule_relocated_toNextRoundState_exists hψ ring start
      hthree C reference payload flag hflag hpayload hpayloadFlag hstate
      hclean hlabel hbit hnextEmpty
  change (WriterSelectedOutcome hp target payload flag schedule nextPayload) at houtcome
  obtain ⟨nextFlag, hfields, hupdate⟩ :=
    WriterSelectedOutcome.payload_update_groupID hp ring start reference
      payload flag schedule nextPayload hsource hpayloadFlag houtcome
  exact ⟨schedule, nextPayload, nextFlag, houtcome, hround, hfields, hupdate⟩

/-- If the attached writer bits are authenticated against a source group, a
first `larger` comparison proves that the numeric writer payload is strictly
smaller than the current target group ID. -/
theorem source_groupID_lt_target_of_first_larger {ψ n : Nat}
    (ring : DirectedRing n) (sourceC targetC : Fin n → AgentState ψ)
    (sourceStart targetStart : Fin n) (payload : Nat → Path3Info)
    (mismatch : Nat) (hmismatch : mismatch < ψ)
    (hsource : ∀ k, k < ψ →
      (payload k).bit = boolBitValue
        (sourceC (groupOffset ring sourceStart k)).bit)
    (hprefix : ∀ k, k < mismatch →
      checkBitWS (targetC (groupOffset ring targetStart k)).bit
        (payload k).bit = .equal)
    (hmismatchComparison :
      checkBitWS (targetC (groupOffset ring targetStart mismatch)).bit
        (payload mismatch).bit = .larger) :
    groupID ring.hn sourceC sourceStart <
      groupID ring.hn targetC targetStart := by
  have hprefixBits : ∀ k, k < mismatch →
      (sourceC (groupOffset ring sourceStart k)).bit =
        (targetC (groupOffset ring targetStart k)).bit := by
    intro k hk
    have hkcmp := hprefix k hk
    rw [hsource k (by omega)] at hkcmp
    exact (checkBitWS_boolBitValue_eq_equal_iff _ _).mp
      hkcmp |>.symm
  rw [hsource mismatch hmismatch] at hmismatchComparison
  have hmismatchBits :=
    (checkBitWS_boolBitValue_eq_larger_iff _ _).mp hmismatchComparison
  exact groupID_lt_of_first_mismatch ring sourceC targetC
    sourceStart targetStart mismatch hmismatch hprefixBits
    hmismatchBits.2 hmismatchBits.1

/-- Under the same source authentication, a first `less` comparison proves
that the current target group ID is strictly smaller than the writer payload. -/
theorem target_groupID_lt_source_of_first_less {ψ n : Nat}
    (ring : DirectedRing n) (sourceC targetC : Fin n → AgentState ψ)
    (sourceStart targetStart : Fin n) (payload : Nat → Path3Info)
    (mismatch : Nat) (hmismatch : mismatch < ψ)
    (hsource : ∀ k, k < ψ →
      (payload k).bit = boolBitValue
        (sourceC (groupOffset ring sourceStart k)).bit)
    (hprefix : ∀ k, k < mismatch →
      checkBitWS (targetC (groupOffset ring targetStart k)).bit
        (payload k).bit = .equal)
    (hmismatchComparison :
      checkBitWS (targetC (groupOffset ring targetStart mismatch)).bit
        (payload mismatch).bit = .less) :
    groupID ring.hn targetC targetStart <
      groupID ring.hn sourceC sourceStart := by
  have hprefixBits : ∀ k, k < mismatch →
      (targetC (groupOffset ring targetStart k)).bit =
        (sourceC (groupOffset ring sourceStart k)).bit := by
    intro k hk
    have hkcmp := hprefix k hk
    rw [hsource k (by omega)] at hkcmp
    exact (checkBitWS_boolBitValue_eq_equal_iff _ _).mp hkcmp
  rw [hsource mismatch hmismatch] at hmismatchComparison
  have hmismatchBits :=
    (checkBitWS_boolBitValue_eq_less_iff _ _).mp hmismatchComparison
  exact groupID_lt_of_first_mismatch ring targetC sourceC
    targetStart sourceStart mismatch hmismatch hprefixBits
    hmismatchBits.1 hmismatchBits.2

/-- If every WRITE_SEQ comparison is equal, source and target group IDs are
equal. -/
theorem source_groupID_eq_target_of_all_equal {ψ n : Nat}
    (ring : DirectedRing n) (sourceC targetC : Fin n → AgentState ψ)
    (sourceStart targetStart : Fin n) (payload : Nat → Path3Info)
    (hsource : ∀ k, k < ψ →
      (payload k).bit = boolBitValue
        (sourceC (groupOffset ring sourceStart k)).bit)
    (hequal : ∀ k, k < ψ →
      checkBitWS (targetC (groupOffset ring targetStart k)).bit
        (payload k).bit = .equal) :
    groupID ring.hn sourceC sourceStart =
      groupID ring.hn targetC targetStart := by
  apply groupID_eq_of_bits ring sourceC targetC sourceStart targetStart
  intro k hk
  have hkcmp := hequal k hk
  rw [hsource k hk] at hkcmp
  exact (checkBitWS_boolBitValue_eq_equal_iff _ _).mp hkcmp |>.symm

/-! ## Phase-correct transport interface for ruler history -/

/-- Consecutive stable groups differ by exactly one physical group offset,
including windows that cross physical index zero. -/
theorem stableGroupStart_succ_eq_groupOffset {ψ n : Nat}
    (ring : DirectedRing n) (leaderPos : Fin n) (target : Nat) :
    stableGroupStart ring leaderPos ψ (target + 1) =
      groupOffset ring (stableGroupStart ring leaderPos ψ target) ψ := by
  apply Fin.ext
  simp only [stableGroupStart, groupOffset]
  rw [Nat.add_mul]
  simp only [Nat.one_mul]
  rw [Nat.mod_add_mod]
  congr 1
  ac_rfl

/-- Action-only analogue of `WriterSelectedOutcome`.  Its schedules start with
the writer already resident in the target group, so they stop at the phase
needed by `RulerOverwritingHistory.advance`. -/
def WriterSelectedActionOutcome {ψ : Nat} (hψ : 0 < ψ)
    (target : Nat → Bool) (payload : Nat → Path3Info) (flag : Nat)
    (schedule : DetSchedule (2 * ψ))
    (nextPayload : Nat → Path3Info) : Prop :=
  ((∀ k, k < ψ → checkBitWS (target k) (payload k).bit = .equal) ∧
      flag = 1 ∧ schedule = writerEqualFlagOneActionSchedule hψ ∧
      nextPayload = fun k =>
        { payload k with flag := 1 - (payload k).flag }) ∨
    ((∀ k, k < ψ → checkBitWS (target k) (payload k).bit = .equal) ∧
      flag = 0 ∧ schedule = writerEqualFlagZeroActionSchedule hψ ∧
      nextPayload = fun k =>
        { payload k with flag := 1 - (payload k).flag }) ∨
    ∃ mismatch comparison command,
      mismatch < ψ ∧
      (∀ k, k < mismatch →
        checkBitWS (target k) (payload k).bit = .equal) ∧
      checkBitWS (target mismatch) (payload mismatch).bit = comparison ∧
      WriterUnequalCommand comparison flag command ∧
      schedule = writerUnequalActionSchedule hψ mismatch ∧
      nextPayload = fun k => writerUnequalPayload command (payload k)

/-- Forgetting whether the initial transport prefix is present does not change
the selected payload transformation. -/
theorem WriterSelectedActionOutcome.toSelectedOutcome
    {ψ : Nat} (hψ : 0 < ψ) (target : Nat → Bool)
    (payload : Nat → Path3Info) (flag : Nat)
    (schedule : DetSchedule (2 * ψ)) (nextPayload : Nat → Path3Info)
    (h : WriterSelectedActionOutcome hψ target payload flag schedule
      nextPayload) :
    ∃ firstSchedule,
      WriterSelectedOutcome hψ target payload flag firstSchedule
        nextPayload := by
  rcases h with ⟨hequal, hflag, _, hnext⟩ |
      ⟨hequal, hflag, _, hnext⟩ |
        ⟨mismatch, comparison, command, hmismatch, hprefix,
          hcomparison, hcommand, _, hnext⟩
  · exact ⟨writerFirstEqualFlagOneSchedule hψ,
      Or.inl ⟨hequal, hflag, rfl, hnext⟩⟩
  · exact ⟨writerFirstEqualFlagZeroSchedule hψ,
      Or.inr (Or.inl ⟨hequal, hflag, rfl, hnext⟩)⟩
  · exact ⟨writerFirstUnequalSchedule hψ mismatch,
      Or.inr (Or.inr ⟨mismatch, comparison, command, hmismatch, hprefix,
        hcomparison, hcommand, rfl, hnext⟩)⟩

/-- The action-only selector has the same exact numeric flag semantics as the
combined transport/action selector, now for arbitrary physical source and
target group starts. -/
theorem WriterSelectedActionOutcome.payload_update_between_groupIDs
    {ψ n : Nat} (hψ : 0 < ψ) (ring : DirectedRing n)
    (sourceReference targetReference : Fin n → AgentState ψ)
    (sourceStart targetStart : Fin n)
    (payload : Nat → Path3Info) (flag : Nat)
    (schedule : DetSchedule (2 * ψ)) (nextPayload : Nat → Path3Info)
    (hsource : ∀ k, k < ψ →
      (payload k).bit = boolBitValue
        (sourceReference (groupOffset ring sourceStart k)).bit)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = flag)
    (houtcome : WriterSelectedActionOutcome hψ
      (fun k => (targetReference (groupOffset ring targetStart k)).bit)
      payload flag schedule nextPayload) :
    ∃ nextFlag,
      (∀ k, k < ψ →
        (nextPayload k).label = (payload k).label ∧
        (nextPayload k).bit = (payload k).bit ∧
        (nextPayload k).flag = nextFlag) ∧
      nextFlag =
        if groupID ring.hn sourceReference sourceStart ≤
            groupID ring.hn targetReference targetStart
        then 1 - flag else flag := by
  obtain ⟨firstSchedule, hfirst⟩ :=
    WriterSelectedActionOutcome.toSelectedOutcome hψ
      (fun k => (targetReference (groupOffset ring targetStart k)).bit)
      payload flag schedule nextPayload houtcome
  obtain ⟨nextFlag, hfields, hupdate⟩ :=
    WriterSelectedOutcome.payload_update hψ
      (fun k => (sourceReference (groupOffset ring sourceStart k)).bit)
      (fun k => (targetReference (groupOffset ring targetStart k)).bit)
      payload flag firstSchedule nextPayload hsource hpayloadFlag hfirst
  have hsourceValue := groupID_eq_msbBitValue ring sourceReference sourceStart
  have htargetValue := groupID_eq_msbBitValue ring targetReference targetStart
  refine ⟨nextFlag, hfields, ?_⟩
  rw [hsourceValue, htargetValue]
  exact hupdate

/-- Same-configuration specialization retained for the physical-source repair
lane. -/
theorem WriterSelectedActionOutcome.payload_update_groupIDs
    {ψ n : Nat} (hψ : 0 < ψ) (ring : DirectedRing n)
    (reference : Fin n → AgentState ψ) (sourceStart targetStart : Fin n)
    (payload : Nat → Path3Info) (flag : Nat)
    (schedule : DetSchedule (2 * ψ)) (nextPayload : Nat → Path3Info)
    (hsource : ∀ k, k < ψ →
      (payload k).bit = boolBitValue
        (reference (groupOffset ring sourceStart k)).bit)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = flag)
    (houtcome : WriterSelectedActionOutcome hψ
      (fun k => (reference (groupOffset ring targetStart k)).bit)
      payload flag schedule nextPayload) :
    ∃ nextFlag,
      (∀ k, k < ψ →
        (nextPayload k).label = (payload k).label ∧
        (nextPayload k).bit = (payload k).bit ∧
        (nextPayload k).flag = nextFlag) ∧
      nextFlag =
        if groupID ring.hn reference sourceStart ≤
            groupID ring.hn reference targetStart
        then 1 - flag else flag := by
  exact WriterSelectedActionOutcome.payload_update_between_groupIDs hψ ring
    reference reference sourceStart targetStart payload flag schedule
    nextPayload hsource hpayloadFlag houtcome

/-- The completed-window seam also transports the clean-control and cyclic
label frames needed by the following block transport.  The old target half is
read through exact window agreement; the fresh future half is outside the old
schedule and is therefore read from the pre-state. -/
theorem WriterCanonicalCompletedState.toNextRoundState_frames
    {ψ n : Nat} (hψ : 1 < ψ) (ring : DirectedRing n) (start : Fin n)
    (hthree : 3 * ψ ≤ n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (C : Fin n → AgentState ψ) (schedule : DetSchedule (2 * ψ))
    (hnonwrap : WriterScheduleNonwrapping schedule)
    (smallAfter : Fin (2 * ψ) → AgentState ψ)
    (nextPayload : Nat → Path3Info)
    (hagree : WriterWindowAgrees ring start smallAfter
      (_root_.applySchedule ring T C
        (relocateWriterSchedule ring start schedule)))
    (hcomplete : WriterCanonicalCompletedState (by omega) smallAfter
      nextPayload)
    (hsmallClean : ∀ i, WriterTransportCleanFrame (smallAfter i))
    (hsmallLabel : WriterLabelFrame (by omega) smallAfter)
    (hnextFresh : ∀ k, k < ψ →
      let u := C (groupOffset ring start (2 * ψ + k))
      u.path3 = none ∧ WriterTransportCleanFrame u ∧ u.label.val = k) :
    let largeAfter := _root_.applySchedule ring T C
      (relocateWriterSchedule ring start schedule)
    let nextStart := groupOffset ring start ψ
    WriterRoundState (by omega)
        (writerWindowPullback ring nextStart largeAfter) nextPayload 0 ∧
      (∀ i, WriterTransportCleanFrame
        ((writerWindowPullback ring nextStart largeAfter) i)) ∧
      WriterLabelFrame (by omega)
        (writerWindowPullback ring nextStart largeAfter) := by
  let hp : 0 < ψ := by omega
  let largeAfter := _root_.applySchedule ring T C
    (relocateWriterSchedule ring start schedule)
  let nextStart := groupOffset ring start ψ
  have hnextEmpty : ∀ k, k < ψ →
      (C (groupOffset ring start (2 * ψ + k))).path3 = none := by
    intro k hk
    exact (hnextFresh k hk).1
  have hround := WriterCanonicalCompletedState.toNextRoundState hψ ring start
    hthree T C schedule hnonwrap smallAfter nextPayload hagree hcomplete
    hnextEmpty
  change WriterRoundState hp
    (writerWindowPullback ring nextStart largeAfter) nextPayload 0 at hround
  refine ⟨hround, ?_, ?_⟩
  · intro i
    have hi : i.val < 2 * ψ := i.isLt
    have hpos : genericWriterPos hp i.val = i := by
      apply Fin.ext
      rw [genericWriterPos_val_of_lt hp hi]
    rw [← hpos]
    change WriterTransportCleanFrame
      (largeAfter (writerWindowEmbed ring nextStart
        (genericWriterPos hp i.val)))
    rw [show nextStart = groupOffset ring start ψ by rfl,
      writerWindowEmbed_next_offset hp ring start hi]
    by_cases hsource : i.val < ψ
    · have hold : groupOffset ring start (ψ + i.val) =
          writerWindowEmbed ring start (genericWriterPos hp (ψ + i.val)) := by
        unfold writerWindowEmbed
        rw [genericWriterPos_val_of_lt hp (by omega)]
      rw [hold]
      have hagreeI := hagree (genericWriterPos hp (ψ + i.val))
      change largeAfter
          (writerWindowEmbed ring start (genericWriterPos hp (ψ + i.val))) =
        smallAfter (genericWriterPos hp (ψ + i.val)) at hagreeI
      rw [hagreeI]
      exact hsmallClean _
    · have hk : i.val - ψ < ψ := by omega
      have hoffset : ψ + i.val = 2 * ψ + (i.val - ψ) := by omega
      let future := groupOffset ring start (ψ + i.val)
      have hfutureOutside : ∀ j : Fin (2 * ψ),
          future ≠ writerWindowEmbed ring start j := by
        intro j
        unfold future writerWindowEmbed
        apply groupOffset_ne_of_lt ring start
        · omega
        · omega
        · omega
      have houtside := relocateWriterSchedule_eq_of_outside hψ ring start
        (by omega) T C schedule hnonwrap future hfutureOutside
      have houtside' : largeAfter future = C future := by
        simpa [largeAfter] using houtside
      change WriterTransportCleanFrame (largeAfter future)
      rw [houtside']
      rw [show future = groupOffset ring start
        (2 * ψ + (i.val - ψ)) by unfold future; rw [hoffset]]
      exact (hnextFresh (i.val - ψ) hk).2.1
  · intro x hx
    change (largeAfter (writerWindowEmbed ring nextStart
      (genericWriterPos hp x))).label.val = x % ψ
    rw [show nextStart = groupOffset ring start ψ by rfl,
      writerWindowEmbed_next_offset hp ring start hx]
    by_cases hsource : x < ψ
    · have hold : groupOffset ring start (ψ + x) =
          writerWindowEmbed ring start (genericWriterPos hp (ψ + x)) := by
        unfold writerWindowEmbed
        rw [genericWriterPos_val_of_lt hp (by omega)]
      rw [hold]
      have hagreeX := hagree (genericWriterPos hp (ψ + x))
      change largeAfter
          (writerWindowEmbed ring start (genericWriterPos hp (ψ + x))) =
        smallAfter (genericWriterPos hp (ψ + x)) at hagreeX
      rw [hagreeX]
      have hlabelX := hsmallLabel (ψ + x) (by omega)
      simpa [Nat.add_mod_left, Nat.mod_eq_of_lt hsource] using hlabelX
    · have hk : x - ψ < ψ := by omega
      have hoffset : ψ + x = 2 * ψ + (x - ψ) := by omega
      let future := groupOffset ring start (ψ + x)
      have hfutureOutside : ∀ j : Fin (2 * ψ),
          future ≠ writerWindowEmbed ring start j := by
        intro j
        unfold future writerWindowEmbed
        apply groupOffset_ne_of_lt ring start
        · omega
        · omega
        · omega
      have houtside := relocateWriterSchedule_eq_of_outside hψ ring start
        (by omega) T C schedule hnonwrap future hfutureOutside
      have houtside' : largeAfter future = C future := by
        simpa [largeAfter] using houtside
      change (largeAfter future).label.val = x % ψ
      rw [houtside']
      rw [show future = groupOffset ring start (2 * ψ + (x - ψ)) by
        unfold future
        rw [hoffset]]
      have hfresh := (hnextFresh (x - ψ) hk).2.2
      rw [hfresh]
      have hshape : x = ψ + (x - ψ) := by omega
      rw [hshape, Nat.add_mod_left, Nat.mod_eq_of_lt hk]
      omega

/-- Generic relocation wrapper for an action-only canonical endpoint.  Once a
canonical schedule has produced a completed writer plus clean/label frames,
this theorem moves that exact endpoint through the strengthened seam. -/
theorem canonicalActionSchedule_relocated_toNextRoundState_frames
    {ψ n : Nat} (hψ : 1 < ψ) (ring : DirectedRing n) (start : Fin n)
    (hthree : 3 * ψ ≤ n) (C : Fin n → AgentState ψ)
    (schedule : DetSchedule (2 * ψ))
    (hnonwrap : WriterScheduleNonwrapping schedule)
    (nextPayload : Nat → Path3Info)
    (hcanonical :
      let small := writerWindowPullback ring start C
      let smallAfter := _root_.applySchedule (genericWriterRing (by omega))
        (writeSeqPersistentComparisonTransportLifecycle (by omega)) small
        schedule
      WriterCanonicalCompletedState (by omega) smallAfter nextPayload ∧
        (∀ i, WriterTransportCleanFrame (smallAfter i)) ∧
        WriterLabelFrame (by omega) smallAfter)
    (hnextFresh : ∀ k, k < ψ →
      let u := C (groupOffset ring start (2 * ψ + k))
      u.path3 = none ∧ WriterTransportCleanFrame u ∧ u.label.val = k) :
    let largeAfter := _root_.applySchedule ring
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (relocateWriterSchedule ring start schedule)
    WriterRoundState (by omega)
        (writerWindowPullback ring (groupOffset ring start ψ) largeAfter)
        nextPayload 0 ∧
      (∀ i, WriterTransportCleanFrame
        ((writerWindowPullback ring (groupOffset ring start ψ) largeAfter) i)) ∧
      WriterLabelFrame (by omega)
        (writerWindowPullback ring (groupOffset ring start ψ) largeAfter) := by
  let hp : 0 < ψ := by omega
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let small := writerWindowPullback ring start C
  let smallAfter := _root_.applySchedule (genericWriterRing hp) T small schedule
  let largeAfter := _root_.applySchedule ring T C
    (relocateWriterSchedule ring start schedule)
  change WriterCanonicalCompletedState hp smallAfter nextPayload ∧
      (∀ i, WriterTransportCleanFrame (smallAfter i)) ∧
      WriterLabelFrame hp smallAfter at hcanonical
  rcases hcanonical with ⟨hcomplete, hclean, hlabel⟩
  have hagree := WriterWindowAgrees.applySchedule hψ ring start (by omega) T
    small C schedule hnonwrap (writerWindowPullback_agrees ring start C)
  change WriterWindowAgrees ring start smallAfter largeAfter at hagree
  exact WriterCanonicalCompletedState.toNextRoundState_frames hψ ring start
    hthree T C schedule hnonwrap smallAfter nextPayload hagree hcomplete
    hclean hlabel hnextFresh

/-- A canonical source-half bit frame transfers through exact window
agreement to the physical first group of the relocated action. -/
theorem WriterWindowAgrees.source_group_bits {ψ n : Nat} (hψ : 0 < ψ)
    (ring : DirectedRing n) (start : Fin n)
    (reference largeAfter : Fin n → AgentState ψ)
    (smallAfter : Fin (2 * ψ) → AgentState ψ)
    (hagree : WriterWindowAgrees ring start smallAfter largeAfter)
    (hsource : WriterSourceBitFrame hψ
      (writerWindowPullback ring start reference) smallAfter) :
    ∀ k, k < ψ →
      (largeAfter (groupOffset ring start k)).bit =
        (reference (groupOffset ring start k)).bit := by
  intro k hk
  have hcoord : writerWindowEmbed ring start (genericWriterPos hψ k) =
      groupOffset ring start k := by
    unfold writerWindowEmbed
    rw [genericWriterPos_val_of_lt hψ (by omega)]
  have hagreeK := hagree (genericWriterPos hψ k)
  have hsourceK := hsource k hk
  change largeAfter
      (writerWindowEmbed ring start (genericWriterPos hψ k)) =
    smallAfter (genericWriterPos hψ k) at hagreeK
  change (smallAfter (genericWriterPos hψ k)).bit =
    ((writerWindowPullback ring start reference)
      (genericWriterPos hψ k)).bit at hsourceK
  rw [hcoord] at hagreeK
  unfold writerWindowPullback at hsourceK
  rw [hcoord] at hsourceK
  rw [hagreeK]
  exact hsourceK

/-- **Standalone arbitrary-window block transport.** A round-zero writer in a
large-ring window crosses into the second group under the actual repaired
lifecycle.  Unlike the `writerFirst...` capstones, this theorem stops before
processing the new target, which is the phase where a next
`SourceTaggedCompleteOverwritingCarrier` must be constructed. -/
theorem writerBlockTransportSchedule_relocated_from_zero
    {ψ n : Nat} (hψ : 1 < ψ)
    (ring : DirectedRing n) (start : Fin n) (hwindow : 2 * ψ ≤ n)
    (C : Fin n → AgentState ψ) (payload : Nat → Path3Info)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hstate : WriterRoundState (by omega)
      (writerWindowPullback ring start C) payload 0)
    (hclean : ∀ i, WriterTransportCleanFrame
      ((writerWindowPullback ring start C) i))
    (hlabel : WriterLabelFrame (by omega)
      (writerWindowPullback ring start C)) :
    let schedule := writerBlockTransportSchedule
      (genericWriterRing (ψ := ψ) (by omega))
      (genericWriterStart (ψ := ψ) (by omega)) ψ
    let D := _root_.applySchedule ring
      (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
      (relocateWriterSchedule ring start schedule)
    WriterRoundState (by omega)
        (writerWindowPullback ring start D) payload ψ ∧
      (∀ i, WriterTransportCleanFrame
        ((writerWindowPullback ring start D) i)) ∧
      WriterLabelFrame (by omega) (writerWindowPullback ring start D) ∧
      WriterBitFrame (writerWindowPullback ring start C)
        (writerWindowPullback ring start D) := by
  let hp : 0 < ψ := by omega
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let schedule := writerBlockTransportSchedule (genericWriterRing hp)
    (genericWriterStart hp) ψ
  let small := writerWindowPullback ring start C
  let smallAfter := _root_.applySchedule (genericWriterRing hp) T small
    schedule
  let D := _root_.applySchedule ring T C
    (relocateWriterSchedule ring start schedule)
  have hcanonical := writerBlockTransportSchedule_from_zero hp small payload
    small hpayload hstate hclean hlabel (fun _ => rfl)
  change (WriterRoundState hp smallAfter payload ψ ∧
      (∀ i, WriterTransportCleanFrame (smallAfter i)) ∧
      WriterLabelFrame hp smallAfter ∧ WriterBitFrame small smallAfter) at hcanonical
  have hagree := WriterWindowAgrees.applySchedule hψ ring start hwindow T
    small C schedule (writerBlockTransportSchedule_nonwrapping hp)
    (writerWindowPullback_agrees ring start C)
  change WriterWindowAgrees ring start smallAfter D at hagree
  have hpull : writerWindowPullback ring start D = smallAfter := by
    funext i
    exact hagree i
  change WriterRoundState hp (writerWindowPullback ring start D) payload ψ ∧
    (∀ i, WriterTransportCleanFrame
      ((writerWindowPullback ring start D) i)) ∧
    WriterLabelFrame hp (writerWindowPullback ring start D) ∧
    WriterBitFrame small (writerWindowPullback ring start D)
  rw [hpull]
  exact hcanonical

/-- The second-half component `k` of a window is exactly component `k` of the
next physical group. -/
theorem writerWindowEmbed_target {ψ n k : Nat} (hψ : 0 < ψ)
    (ring : DirectedRing n) (start : Fin n) (hk : k < ψ) :
    writerWindowEmbed ring start (genericWriterPos hψ (ψ + k)) =
      groupOffset ring (groupOffset ring start ψ) k := by
  rw [← writerWindowEmbed_next_source hψ ring start hk]
  unfold writerWindowEmbed
  rw [genericWriterPos_val_of_lt hψ (by omega)]

/-- A fully transported round is exactly the componentwise source-tagged
carrier interface at the second group.  This theorem performs no history
inference: callers must separately prove that `sourceC` is the preserved
source configuration used by the route. -/
theorem WriterRoundState.toOverwritingBitsMatchBetweenAt
    {ψ n : Nat} (hψ : 0 < ψ) (ring : DirectedRing n) (start sourceStart : Fin n)
    (C sourceC : Fin n → AgentState ψ) (payload : Nat → Path3Info)
    (flag : Nat) (hflag : flag ≤ 1)
    (hstate : WriterRoundState hψ (writerWindowPullback ring start C)
      payload ψ)
    (hpayloadLabel : ∀ k, k < ψ → (payload k).label = k)
    (hpayloadBit : ∀ k, k < ψ →
      (payload k).bit = boolBitValue
        (sourceC (groupOffset ring sourceStart k)).bit)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = flag) :
    overwritingBitsMatchBetweenAt ring C sourceC
      (groupOffset ring start ψ) sourceStart flag := by
  refine ⟨hflag, ?_⟩
  intro k hk
  refine ⟨payload k, ?_, hpayloadLabel k hk, ?_, hpayloadFlag k hk⟩
  · have htoken := hstate.2.1 k hk
    simp only [if_true] at htoken
    unfold WriterTokenAt writerWindowPullback at htoken
    rw [writerWindowEmbed_target hψ ring start hk] at htoken
    exact htoken.1
  · exact hpayloadBit k hk

/-- A transported, source-authenticated round packages into the repository's
existing complete-carrier structure at an explicitly indexed stable target.
The route keeps the supplied older source and numeric payload; it does not
retag the writer to its current host group. -/
theorem WriterRoundState.existsSourceTaggedCarrierFromReference
    {ψ n : Nat} (hψ : 0 < ψ) (ring : DirectedRing n)
    (leaderPos start : Fin n) (C referenceC : Fin n → AgentState ψ)
    (payload : Nat → Path3Info) (source target payloadID flag : Nat)
    (hsourceRange : source < n / ψ) (htargetRange : target < n / ψ)
    (htargetStart : stableGroupStart ring leaderPos ψ target =
      groupOffset ring start ψ)
    (hpayloadID : payloadID = groupID ring.hn referenceC
      (stableGroupStart ring leaderPos ψ source))
    (hstate : WriterRoundState hψ (writerWindowPullback ring start C)
      payload ψ)
    (hpayloadLabel : ∀ k, k < ψ → (payload k).label = k)
    (hpayloadBit : ∀ k, k < ψ →
      (payload k).bit = boolBitValue
        (referenceC (groupOffset ring
          (stableGroupStart ring leaderPos ψ source) k)).bit)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = flag)
    (hflag : flag ≤ 1) :
    ∃ carrier : SourceTaggedCompleteOverwritingCarrier
        ring C referenceC leaderPos,
      carrier.route.source = source ∧ carrier.route.target = target ∧
        carrier.route.payload = payloadID ∧ carrier.flag = flag := by
  have hcomponents := WriterRoundState.toOverwritingBitsMatchBetweenAt hψ
    ring start (stableGroupStart ring leaderPos ψ source) C referenceC payload
    flag hflag hstate hpayloadLabel hpayloadBit hpayloadFlag
  let route : OverwritingCarrierRoute ring referenceC leaderPos :=
    { source := source
      target := target
      payload := payloadID
      source_in_range := hsourceRange
      target_in_range := htargetRange
      payload_from_source := hpayloadID }
  let carrier : SourceTaggedCompleteOverwritingCarrier
      ring C referenceC leaderPos :=
    { route := route
      flag := flag
      components := by
        change overwritingBitsMatchBetweenAt ring C referenceC
          (stableGroupStart ring leaderPos ψ target)
          (stableGroupStart ring leaderPos ψ source) flag
        rw [htargetStart]
        exact hcomponents }
  exact ⟨carrier, rfl, rfl, rfl, rfl⟩

/-- Same-configuration specialization used by the physical-source repair
lane. -/
theorem WriterRoundState.existsSourceTaggedCarrier
    {ψ n : Nat} (hψ : 0 < ψ) (ring : DirectedRing n)
    (leaderPos start : Fin n) (C : Fin n → AgentState ψ)
    (payload : Nat → Path3Info) (source target payloadID flag : Nat)
    (hsourceRange : source < n / ψ) (htargetRange : target < n / ψ)
    (htargetStart : stableGroupStart ring leaderPos ψ target =
      groupOffset ring start ψ)
    (hpayloadID : payloadID = groupID ring.hn C
      (stableGroupStart ring leaderPos ψ source))
    (hstate : WriterRoundState hψ (writerWindowPullback ring start C)
      payload ψ)
    (hpayloadLabel : ∀ k, k < ψ → (payload k).label = k)
    (hpayloadBit : ∀ k, k < ψ →
      (payload k).bit = boolBitValue
        (C (groupOffset ring
          (stableGroupStart ring leaderPos ψ source) k)).bit)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = flag)
    (hflag : flag ≤ 1) :
    ∃ carrier : SourceTaggedCompleteOverwritingCarrier ring C C leaderPos,
      carrier.route.source = source ∧ carrier.route.target = target ∧
        carrier.route.payload = payloadID ∧ carrier.flag = flag := by
  exact WriterRoundState.existsSourceTaggedCarrierFromReference hψ ring
    leaderPos start C C payload source target payloadID flag hsourceRange
    htargetRange htargetStart hpayloadID hstate hpayloadLabel hpayloadBit
    hpayloadFlag hflag

/-- **Phase-correct C4 action step.** A source-authenticated writer already
resident at the current target chooses and executes the real action-only
schedule.  The endpoint is round zero of the current/next window with the
frames required for standalone transport, and its common flag obeys the exact
source-ID/target-ID ruler update. -/
theorem writerActionOnlySchedule_relocated_toNextRoundState_with_groupID_update
    {ψ n : Nat} (hψ : 1 < ψ) (ring : DirectedRing n)
    (start sourceStart : Fin n) (hthree : 3 * ψ ≤ n)
    (C reference sourceReference : Fin n → AgentState ψ)
    (payload : Nat → Path3Info)
    (flag : Nat) (hflag : flag ≤ 1)
    (hpayload : ∀ k, k < ψ → (payload k).label = k)
    (hsource : ∀ k, k < ψ →
      (payload k).bit = boolBitValue
        (sourceReference (groupOffset ring sourceStart k)).bit)
    (hpayloadFlag : ∀ k, k < ψ → (payload k).flag = flag)
    (hstate : WriterRoundState (by omega)
      (writerWindowPullback ring start C) payload ψ)
    (hclean : ∀ i, WriterTransportCleanFrame
      ((writerWindowPullback ring start C) i))
    (hlabel : WriterLabelFrame (by omega)
      (writerWindowPullback ring start C))
    (hbit : WriterBitFrame (writerWindowPullback ring start reference)
      (writerWindowPullback ring start C))
    (hnextFresh : ∀ k, k < ψ →
      let u := C (groupOffset ring start (2 * ψ + k))
      u.path3 = none ∧ WriterTransportCleanFrame u ∧ u.label.val = k) :
    let targetStart := groupOffset ring start ψ
    let target := fun k => (reference (groupOffset ring targetStart k)).bit
    ∃ schedule nextPayload nextFlag,
      WriterSelectedActionOutcome (ψ := ψ) (by omega) target payload flag
          schedule nextPayload ∧
        (let largeAfter := _root_.applySchedule ring
          (writeSeqPersistentComparisonTransportLifecycle (by omega)) C
          (relocateWriterSchedule ring start schedule)
        WriterRoundState (by omega)
            (writerWindowPullback ring targetStart largeAfter) nextPayload 0 ∧
          (∀ i, WriterTransportCleanFrame
            ((writerWindowPullback ring targetStart largeAfter) i)) ∧
          WriterLabelFrame (by omega)
            (writerWindowPullback ring targetStart largeAfter) ∧
          (∀ k, k < ψ →
            (largeAfter (groupOffset ring start k)).bit =
              (reference (groupOffset ring start k)).bit)) ∧
        (∀ k, k < ψ →
          (nextPayload k).label = (payload k).label ∧
          (nextPayload k).bit = (payload k).bit ∧
          (nextPayload k).flag = nextFlag) ∧
        nextFlag =
          if groupID ring.hn sourceReference sourceStart ≤
              groupID ring.hn reference targetStart
          then 1 - flag else flag := by
  let hp : 0 < ψ := by omega
  let T := writeSeqPersistentComparisonTransportLifecycle hp
  let small := writerWindowPullback ring start C
  let smallReference := writerWindowPullback ring start reference
  let targetStart := groupOffset ring start ψ
  let target := fun k => (reference (groupOffset ring targetStart k)).bit
  have hequalPrefix : WriterEqualPrefixState hp small payload 0 :=
    WriterRoundState.toEqualPrefix hp small payload hstate
  rcases writer_action_cases ψ target payload flag hflag with
      ⟨hequal, hflagOne⟩ | ⟨hequal, hflagZero⟩ |
        ⟨mismatch, comparison, command, hmismatch, hprefix,
          hcomparison, hcommand⟩
  · let schedule := writerEqualFlagOneActionSchedule hp
    let smallAfter := _root_.applySchedule (genericWriterRing hp) T small
      schedule
    have hequalSmall : ∀ k, k < ψ →
        checkBitWS (smallReference (genericWriterPos hp (ψ + k))).bit
          (payload k).bit = .equal := by
      intro k hk
      change checkBitWS
        ((writerWindowPullback ring start reference)
          (genericWriterPos hp (ψ + k))).bit (payload k).bit = .equal
      rw [writerWindowPullback_target_bit hp ring start reference hk]
      exact hequal k hk
    have haction := writerEqualFlagOneActionSchedule_reaches hψ small
      smallReference payload hpayload hequalSmall
      (by
        intro k hk
        rw [hpayloadFlag k hk, hflagOne])
      hequalPrefix hclean hlabel hbit
    change WriterMoveFlipSweepState hp smallAfter payload ψ ∧
        (∀ i, WriterTransportCleanFrame (smallAfter i)) ∧
        WriterLabelFrame hp smallAfter ∧
        WriterBitFrame smallReference smallAfter at haction
    rcases haction with ⟨hprocessed, hcleanAfter, hlabelAfter, hbitAfter⟩
    have hsourceSmall : WriterSourceBitFrame hp smallReference smallAfter := by
      intro k hk
      exact hbitAfter (genericWriterPos hp k)
    have hcanonical : WriterCanonicalCompletedState hp smallAfter
          (fun k => { payload k with flag := 1 - (payload k).flag }) ∧
        (∀ i, WriterTransportCleanFrame (smallAfter i)) ∧
        WriterLabelFrame hp smallAfter :=
      ⟨WriterMoveFlipSweepState.toCompleted hp smallAfter payload hprocessed,
        hcleanAfter, hlabelAfter⟩
    have hseam := canonicalActionSchedule_relocated_toNextRoundState_frames
      hψ ring start hthree C schedule
      (writerEqualFlagOneActionSchedule_nonwrapping hp)
      (fun k => { payload k with flag := 1 - (payload k).flag })
      hcanonical hnextFresh
    have houtcome : WriterSelectedActionOutcome hp target payload flag schedule
        (fun k => { payload k with flag := 1 - (payload k).flag }) :=
      Or.inl ⟨hequal, hflagOne, rfl, rfl⟩
    obtain ⟨nextFlag, hfields, hupdate⟩ :=
      WriterSelectedActionOutcome.payload_update_between_groupIDs hp ring
        sourceReference reference sourceStart targetStart payload flag schedule
        (fun k => { payload k with flag := 1 - (payload k).flag })
        hsource hpayloadFlag houtcome
    let largeAfter := _root_.applySchedule ring T C
      (relocateWriterSchedule ring start schedule)
    have hagree := WriterWindowAgrees.applySchedule hψ ring start (by omega) T
      small C schedule (writerEqualFlagOneActionSchedule_nonwrapping hp)
      (writerWindowPullback_agrees ring start C)
    change WriterWindowAgrees ring start smallAfter largeAfter at hagree
    have hsourceLarge := WriterWindowAgrees.source_group_bits hp ring start
      reference largeAfter smallAfter hagree hsourceSmall
    change (WriterRoundState hp
        (writerWindowPullback ring targetStart largeAfter)
          (fun k => { payload k with flag := 1 - (payload k).flag }) 0 ∧
      (∀ i, WriterTransportCleanFrame
        ((writerWindowPullback ring targetStart largeAfter) i)) ∧
      WriterLabelFrame hp (writerWindowPullback ring targetStart largeAfter)) at hseam
    have hendpoint : WriterRoundState hp
        (writerWindowPullback ring targetStart largeAfter)
          (fun k => { payload k with flag := 1 - (payload k).flag }) 0 ∧
      (∀ i, WriterTransportCleanFrame
        ((writerWindowPullback ring targetStart largeAfter) i)) ∧
      WriterLabelFrame hp (writerWindowPullback ring targetStart largeAfter) ∧
      (∀ k, k < ψ →
        (largeAfter (groupOffset ring start k)).bit =
          (reference (groupOffset ring start k)).bit) :=
      ⟨hseam.1, hseam.2.1, hseam.2.2, hsourceLarge⟩
    exact ⟨schedule, _, nextFlag, houtcome, hendpoint, hfields, hupdate⟩
  · let schedule := writerEqualFlagZeroActionSchedule hp
    let smallAfter := _root_.applySchedule (genericWriterRing hp) T small
      schedule
    have hequalSmall : ∀ k, k < ψ →
        checkBitWS (smallReference (genericWriterPos hp (ψ + k))).bit
          (payload k).bit = .equal := by
      intro k hk
      change checkBitWS
        ((writerWindowPullback ring start reference)
          (genericWriterPos hp (ψ + k))).bit (payload k).bit = .equal
      rw [writerWindowPullback_target_bit hp ring start reference hk]
      exact hequal k hk
    have haction := writerEqualFlagZeroActionSchedule_reaches hψ small
      smallReference payload hpayload hequalSmall
      (by
        intro k hk
        rw [hpayloadFlag k hk, hflagZero])
      hequalPrefix hclean hlabel hbit
    change WriterIncrementSweepState hp smallReference smallAfter payload ψ ∧
        (∀ i, WriterTransportCleanFrame (smallAfter i)) ∧
        WriterLabelFrame hp smallAfter ∧
        WriterSourceBitFrame hp smallReference smallAfter at haction
    rcases haction with ⟨hprocessed, hcleanAfter, hlabelAfter, hsourceSmall⟩
    have hcanonical : WriterCanonicalCompletedState hp smallAfter
          (fun k => { payload k with flag := 1 - (payload k).flag }) ∧
        (∀ i, WriterTransportCleanFrame (smallAfter i)) ∧
        WriterLabelFrame hp smallAfter :=
      ⟨WriterIncrementSweepState.toCompleted hp smallReference smallAfter
          payload hprocessed,
        hcleanAfter, hlabelAfter⟩
    have hseam := canonicalActionSchedule_relocated_toNextRoundState_frames
      hψ ring start hthree C schedule
      (writerEqualFlagZeroActionSchedule_nonwrapping hp)
      (fun k => { payload k with flag := 1 - (payload k).flag })
      hcanonical hnextFresh
    have houtcome : WriterSelectedActionOutcome hp target payload flag schedule
        (fun k => { payload k with flag := 1 - (payload k).flag }) :=
      Or.inr (Or.inl ⟨hequal, hflagZero, rfl, rfl⟩)
    obtain ⟨nextFlag, hfields, hupdate⟩ :=
      WriterSelectedActionOutcome.payload_update_between_groupIDs hp ring
        sourceReference reference sourceStart targetStart payload flag schedule
        (fun k => { payload k with flag := 1 - (payload k).flag })
        hsource hpayloadFlag houtcome
    let largeAfter := _root_.applySchedule ring T C
      (relocateWriterSchedule ring start schedule)
    have hagree := WriterWindowAgrees.applySchedule hψ ring start (by omega) T
      small C schedule (writerEqualFlagZeroActionSchedule_nonwrapping hp)
      (writerWindowPullback_agrees ring start C)
    change WriterWindowAgrees ring start smallAfter largeAfter at hagree
    have hsourceLarge := WriterWindowAgrees.source_group_bits hp ring start
      reference largeAfter smallAfter hagree hsourceSmall
    change (WriterRoundState hp
        (writerWindowPullback ring targetStart largeAfter)
          (fun k => { payload k with flag := 1 - (payload k).flag }) 0 ∧
      (∀ i, WriterTransportCleanFrame
        ((writerWindowPullback ring targetStart largeAfter) i)) ∧
      WriterLabelFrame hp (writerWindowPullback ring targetStart largeAfter)) at hseam
    have hendpoint : WriterRoundState hp
        (writerWindowPullback ring targetStart largeAfter)
          (fun k => { payload k with flag := 1 - (payload k).flag }) 0 ∧
      (∀ i, WriterTransportCleanFrame
        ((writerWindowPullback ring targetStart largeAfter) i)) ∧
      WriterLabelFrame hp (writerWindowPullback ring targetStart largeAfter) ∧
      (∀ k, k < ψ →
        (largeAfter (groupOffset ring start k)).bit =
          (reference (groupOffset ring start k)).bit) :=
      ⟨hseam.1, hseam.2.1, hseam.2.2, hsourceLarge⟩
    exact ⟨schedule, _, nextFlag, houtcome, hendpoint, hfields, hupdate⟩
  · let schedule := writerUnequalActionSchedule hp mismatch
    let smallAfter := _root_.applySchedule (genericWriterRing hp) T small
      schedule
    have hprefixSmall : ∀ k, k < mismatch →
        checkBitWS (smallReference (genericWriterPos hp (ψ + k))).bit
          (payload k).bit = .equal := by
      intro k hk
      change checkBitWS
        ((writerWindowPullback ring start reference)
          (genericWriterPos hp (ψ + k))).bit (payload k).bit = .equal
      rw [writerWindowPullback_target_bit hp ring start reference (by omega)]
      exact hprefix k hk
    have hcomparisonSmall :
        checkBitWS
          (smallReference (genericWriterPos hp (ψ + mismatch))).bit
          (payload mismatch).bit = comparison := by
      change checkBitWS
        ((writerWindowPullback ring start reference)
          (genericWriterPos hp (ψ + mismatch))).bit
        (payload mismatch).bit = comparison
      rw [writerWindowPullback_target_bit hp ring start reference hmismatch]
      exact hcomparison
    have haction := writerUnequalActionSchedule_reaches hψ small
      smallReference payload mismatch comparison flag command hmismatch
      hpayload hpayloadFlag hprefixSmall hcomparisonSmall hcommand
      hequalPrefix hclean hlabel hbit
    change WriterUnequalSweepState hp smallReference smallAfter payload
        command ψ ∧
      (∀ i, WriterTransportCleanFrame (smallAfter i)) ∧
      WriterLabelFrame hp smallAfter ∧
      WriterSourceBitFrame hp smallReference smallAfter at haction
    rcases haction with ⟨hprocessed, hcleanAfter, hlabelAfter, hsourceSmall⟩
    have hcanonical : WriterCanonicalCompletedState hp smallAfter
          (fun k => writerUnequalPayload command (payload k)) ∧
        (∀ i, WriterTransportCleanFrame (smallAfter i)) ∧
        WriterLabelFrame hp smallAfter :=
      ⟨WriterUnequalSweepState.toCompleted hp smallReference smallAfter
          payload command hprocessed,
        hcleanAfter, hlabelAfter⟩
    have hseam := canonicalActionSchedule_relocated_toNextRoundState_frames
      hψ ring start hthree C schedule
      (writerUnequalActionSchedule_nonwrapping hp hmismatch)
      (fun k => writerUnequalPayload command (payload k)) hcanonical
      hnextFresh
    have houtcome : WriterSelectedActionOutcome hp target payload flag schedule
        (fun k => writerUnequalPayload command (payload k)) :=
      Or.inr (Or.inr ⟨mismatch, comparison, command, hmismatch, hprefix,
        hcomparison, hcommand, rfl, rfl⟩)
    obtain ⟨nextFlag, hfields, hupdate⟩ :=
      WriterSelectedActionOutcome.payload_update_between_groupIDs hp ring
        sourceReference reference sourceStart targetStart payload flag schedule
        (fun k => writerUnequalPayload command (payload k))
        hsource hpayloadFlag houtcome
    let largeAfter := _root_.applySchedule ring T C
      (relocateWriterSchedule ring start schedule)
    have hagree := WriterWindowAgrees.applySchedule hψ ring start (by omega) T
      small C schedule (writerUnequalActionSchedule_nonwrapping hp hmismatch)
      (writerWindowPullback_agrees ring start C)
    change WriterWindowAgrees ring start smallAfter largeAfter at hagree
    have hsourceLarge := WriterWindowAgrees.source_group_bits hp ring start
      reference largeAfter smallAfter hagree hsourceSmall
    change (WriterRoundState hp
        (writerWindowPullback ring targetStart largeAfter)
          (fun k => writerUnequalPayload command (payload k)) 0 ∧
      (∀ i, WriterTransportCleanFrame
        ((writerWindowPullback ring targetStart largeAfter) i)) ∧
      WriterLabelFrame hp (writerWindowPullback ring targetStart largeAfter)) at hseam
    have hendpoint : WriterRoundState hp
        (writerWindowPullback ring targetStart largeAfter)
          (fun k => writerUnequalPayload command (payload k)) 0 ∧
      (∀ i, WriterTransportCleanFrame
        ((writerWindowPullback ring targetStart largeAfter) i)) ∧
      WriterLabelFrame hp (writerWindowPullback ring targetStart largeAfter) ∧
      (∀ k, k < ψ →
        (largeAfter (groupOffset ring start k)).bit =
          (reference (groupOffset ring start k)).bit) :=
      ⟨hseam.1, hseam.2.1, hseam.2.2, hsourceLarge⟩
    exact ⟨schedule, _, nextFlag, houtcome, hendpoint, hfields, hupdate⟩

end PPLLWriteSeqRulerBridge

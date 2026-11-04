import Leader.Wu.WallSweep.RestartableGeneric

/-!
# Binary rank for source-covered reset retries

The stronger unshielded cleanup route cannot use raw echo count: a terminal
crossing may replace one blocking echo by several echoes strictly behind the
reset frontier.  The correct round-boundary measure is the binary value of the
clockwise follower-echo pattern.  Clearing one blocker while leaving all
higher positions unchanged strictly decreases this value, regardless of what
happens at lower positions.
-/

namespace PPLLWallSweepEchoRank

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  PPLLWallSweepSchedule
  PPLLWallSweepFiniteCleanup PPLLWallSweepRestartableGeneric
  PPLLWallSweepPreCheckResetRepair PPLLWallSweepPreCheckResetContracts
  PPLLWriteSeqRelocation PPLLWriteSeqPersistenceRegression
  PPLLNoCheckBirthConditionTwoGeometry

variable {n psi kappa tau : Nat}

/-- Little-endian binary value of a finite Boolean vector. -/
def binaryRank {m : Nat} (bits : Fin m → Bool) : Nat :=
  (List.ofFn fun i => if bits i then 2 ^ i.val else 0).sum

private theorem sum_map_two (xs : List Nat) :
    (xs.map (fun x => 2 * x)).sum = 2 * xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih, Nat.mul_add]

/-- Splitting off the least significant bit doubles the remaining vector. -/
theorem binaryRank_succ {m : Nat} (bits : Fin (m + 1) → Bool) :
    binaryRank bits = (if bits 0 then 1 else 0) +
      2 * binaryRank (fun i : Fin m => bits i.succ) := by
  unfold binaryRank
  rw [List.ofFn_succ, List.sum_cons]
  simp only [Fin.val_zero, Nat.pow_zero]
  congr 1
  rw [← sum_map_two]
  apply congrArg List.sum
  rw [List.map_ofFn]
  apply List.ext_getElem?
  intro i
  by_cases hi : i < m
  · by_cases hb : bits ⟨i + 1, by omega⟩ = true
    · simp [hi, hb, Nat.pow_succ, Nat.mul_comm]
    · simp [hi, hb, Nat.pow_succ, Nat.mul_comm]
  · simp [hi]

/-- Every `m`-bit echo pattern has value strictly below `2^m`. -/
theorem binaryRank_lt_two_pow {m : Nat} (bits : Fin m → Bool) :
    binaryRank bits < 2 ^ m := by
  induction m with
  | zero => simp [binaryRank]
  | succ m ih =>
      rw [binaryRank_succ]
      have htail := ih (fun i : Fin m => bits i.succ)
      cases hbit : bits 0 <;> simp [Nat.pow_succ] <;> omega

/-- The rank vanishes exactly when every bit vanishes. -/
theorem binaryRank_eq_zero_iff {m : Nat} (bits : Fin m → Bool) :
    binaryRank bits = 0 ↔ ∀ i, bits i = false := by
  induction m with
  | zero => simp [binaryRank]
  | succ m ih =>
      rw [binaryRank_succ]
      constructor
      · intro hrank
        have hzero : bits 0 = false := by
          cases hb : bits 0 <;> simp_all
        have htailRank :
            binaryRank (fun i : Fin m => bits i.succ) = 0 := by
          simp [hzero] at hrank
          omega
        have htail := (ih (fun i : Fin m => bits i.succ)).mp htailRank
        intro i
        cases i using Fin.cases with
        | zero => exact hzero
        | succ i => exact htail i
      · intro hall
        have hzero := hall 0
        have htail : ∀ i : Fin m, bits i.succ = false :=
          fun i => hall i.succ
        rw [(ih (fun i : Fin m => bits i.succ)).mpr htail]
        simp [hzero]

/-- A positive rank has a concrete echo bit, and conversely. -/
theorem binaryRank_ne_zero_iff {m : Nat} (bits : Fin m → Bool) :
    binaryRank bits ≠ 0 ↔ ∃ i, bits i = true := by
  rw [ne_eq, binaryRank_eq_zero_iff]
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    apply h
    intro i
    cases hb : bits i
    · rfl
    · exact False.elim (hn ⟨i, hb⟩)
  · rintro ⟨i, hi⟩ hall
    rw [hall i] at hi
    contradiction

/-- Least true bit, if one exists, computed from the low end of the vector. -/
def firstTrue? : {m : Nat} → (Fin m → Bool) → Option (Fin m)
  | 0, _ => none
  | m + 1, bits =>
      if bits 0 then some 0
      else (firstTrue? (fun i : Fin m => bits i.succ)).map Fin.succ

/-- The search fails exactly on the all-false pattern. -/
theorem firstTrue?_eq_none_iff {m : Nat} (bits : Fin m → Bool) :
    firstTrue? bits = none ↔ ∀ i, bits i = false := by
  induction m with
  | zero => simp [firstTrue?]
  | succ m ih =>
      rw [Fin.forall_fin_succ]
      cases h0 : bits 0
      · simp [firstTrue?, h0, ih]
      · simp [firstTrue?, h0]

/-- A returned index is true and every lower bit is false. -/
theorem firstTrue?_eq_some_spec {m : Nat} (bits : Fin m → Bool)
    (t : Fin m) (h : firstTrue? bits = some t) :
    bits t = true ∧ ∀ i, i.val < t.val → bits i = false := by
  induction m with
  | zero => exact Fin.elim0 t
  | succ m ih =>
      cases h0 : bits 0
      · cases ht : firstTrue? (fun i : Fin m => bits i.succ) with
        | none => simp [firstTrue?, h0, ht] at h
        | some t' =>
            simp [firstTrue?, h0, ht] at h
            subst t
            have hspec := ih
              (fun i : Fin m => bits i.succ) t' ht
            constructor
            · exact hspec.1
            · intro i hi
              cases i using Fin.cases with
              | zero => exact h0
              | succ i => exact hspec.2 i (by simpa using hi)
      · simp [firstTrue?, h0] at h
        subst t
        exact ⟨h0, by
          intro i hi
          exact (Nat.not_lt_zero _ hi).elim⟩

/-- Every positive rank has a canonical least blocking echo. -/
theorem exists_firstTrue_of_binaryRank_ne_zero {m : Nat}
    (bits : Fin m → Bool) (h : binaryRank bits ≠ 0) :
    ∃ t, firstTrue? bits = some t ∧ bits t = true ∧
      ∀ i, i.val < t.val → bits i = false := by
  have hnotnone : firstTrue? bits ≠ none := by
    intro hnone
    apply h
    rw [binaryRank_eq_zero_iff]
    exact (firstTrue?_eq_none_iff bits).mp hnone
  cases ht : firstTrue? bits with
  | none => exact (hnotnone ht).elim
  | some t =>
      have hspec := firstTrue?_eq_some_spec bits t ht
      exact ⟨t, rfl, hspec⟩

/-- A change from one to zero at the highest position where two patterns may
differ strictly decreases the binary value; all lower bits are unrestricted. -/
theorem binaryRank_lt_of_highest_diff {m : Nat}
    (a b : Fin m → Bool) (t : Fin m)
    (hat : a t = false) (hbt : b t = true)
    (hhigher : ∀ i : Fin m, t.val < i.val → a i = b i) :
    binaryRank a < binaryRank b := by
  induction m with
  | zero => exact Fin.elim0 t
  | succ m ih =>
      cases t using Fin.cases with
      | zero =>
        have htail : (fun i : Fin m => a i.succ) =
            (fun i : Fin m => b i.succ) := by
          funext i
          exact hhigher i.succ (by simp)
        rw [binaryRank_succ, binaryRank_succ, htail]
        simp [hat, hbt]
      | succ t' =>
        have htail := ih
          (fun i : Fin m => a i.succ)
          (fun i : Fin m => b i.succ) t'
          (by exact hat) (by exact hbt) (by
            intro i hi
            exact hhigher i.succ (by simpa using hi))
        rw [binaryRank_succ, binaryRank_succ]
        cases ha0 : a 0 <;> cases hb0 : b 0 <;>
          simp_all <;> omega

/-- Follower echoes in clockwise order after the designated leader. -/
def clockwiseFollowerEchoBits
    (ring : DirectedRing n) (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    Fin (n - 1) → Bool :=
  fun i => (C (groupOffset ring leader (i.val + 1))).core.erase.core.echo

/-- Binary rank of the clockwise follower-echo pattern. -/
def clockwiseEchoRank
    (ring : DirectedRing n) (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau) : Nat :=
  binaryRank (clockwiseFollowerEchoBits ring leader C)

/-- Dummy bullets in clockwise follower order after the designated leader.
Offset one is the least-significant bit: a dummy moved one edge toward the
leader therefore moves to a strictly lower bit. -/
def clockwiseFollowerDummyBits
    (ring : DirectedRing n) (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    Fin (n - 1) → Bool :=
  fun i => if
    (C (groupOffset ring leader (i.val + 1))).core.erase.core.bullet =
      ⟨1, by omega⟩
    then true else false

/-- Binary rank of the clockwise follower-dummy pattern.  Binary weights are
stronger than a raw dummy count: moving one blocking dummy toward the leader
strictly decreases the rank even if a lower site already contains a dummy. -/
def clockwiseDummyRank
    (ring : DirectedRing n) (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau) : Nat :=
  binaryRank (clockwiseFollowerDummyBits ring leader C)

/-- Dummy bullets at the mobile follower offsets, beginning at clockwise
offset two.  Offset one is deliberately excluded: the two leader-edge
interactions used to restart a retry may rewrite that site, while every
farther follower is framed exactly. -/
def clockwiseMobileDummyBits
    (ring : DirectedRing n) (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    Fin (n - 2) → Bool :=
  fun i => if
    (C (groupOffset ring leader (i.val + 2))).core.erase.core.bullet =
      ⟨1, by omega⟩
    then true else false

/-- Binary rank of dummy bullets that can still obstruct propagation beyond
the first outgoing follower.  Moving a responder dummy one edge toward the
leader clears a positive-weight bit; a dummy arriving at offset one has left
this rank. -/
def clockwiseMobileDummyRank
    (ring : DirectedRing n) (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau) : Nat :=
  binaryRank (clockwiseMobileDummyBits ring leader C)

/-- Clearing one dummy at a chosen follower offset while framing every higher
follower bullet strictly decreases the binary dummy rank.  Lower offsets are
unrestricted, which permits the same interaction to move the cleared dummy
one edge toward the leader. -/
theorem clockwiseDummyRank_lt_of_cleared_blocker
    (ring : DirectedRing n) (leader : Fin n)
    (before after : Fin n → ExpiringAgentState psi kappa tau)
    (t : Fin (n - 1))
    (hafter :
      (after (groupOffset ring leader (t.val + 1))).core.erase.core.bullet ≠
        ⟨1, by omega⟩)
    (hbefore :
      (before (groupOffset ring leader (t.val + 1))).core.erase.core.bullet =
        ⟨1, by omega⟩)
    (hhigher : ∀ s : Fin (n - 1), t.val < s.val →
      (after (groupOffset ring leader (s.val + 1))).core.erase.core.bullet =
        (before (groupOffset ring leader (s.val + 1))).core.erase.core.bullet) :
    clockwiseDummyRank ring leader after <
      clockwiseDummyRank ring leader before := by
  apply binaryRank_lt_of_highest_diff
    (clockwiseFollowerDummyBits ring leader after)
    (clockwiseFollowerDummyBits ring leader before) t
  · change (if
        (after (groupOffset ring leader (t.val + 1))).core.erase.core.bullet =
          ⟨1, by omega⟩
        then true else false) = false
    rw [if_neg hafter]
  · change (if
        (before (groupOffset ring leader (t.val + 1))).core.erase.core.bullet =
          ⟨1, by omega⟩
        then true else false) = true
    rw [if_pos hbefore]
  · intro s hts
    simp only [clockwiseFollowerDummyBits]
    rw [hhigher s hts]

/-- Clearing one dummy at a mobile follower offset while framing every higher
mobile follower strictly decreases the restart-stable dummy rank. -/
theorem clockwiseMobileDummyRank_lt_of_cleared_blocker
    (ring : DirectedRing n) (leader : Fin n)
    (before after : Fin n → ExpiringAgentState psi kappa tau)
    (t : Fin (n - 2))
    (hafter :
      (after (groupOffset ring leader (t.val + 2))).core.erase.core.bullet ≠
        ⟨1, by omega⟩)
    (hbefore :
      (before (groupOffset ring leader (t.val + 2))).core.erase.core.bullet =
        ⟨1, by omega⟩)
    (hhigher : ∀ s : Fin (n - 2), t.val < s.val →
      (after (groupOffset ring leader (s.val + 2))).core.erase.core.bullet =
        (before (groupOffset ring leader (s.val + 2))).core.erase.core.bullet) :
    clockwiseMobileDummyRank ring leader after <
      clockwiseMobileDummyRank ring leader before := by
  apply binaryRank_lt_of_highest_diff
    (clockwiseMobileDummyBits ring leader after)
    (clockwiseMobileDummyBits ring leader before) t
  · change (if
        (after (groupOffset ring leader (t.val + 2))).core.erase.core.bullet =
          ⟨1, by omega⟩
        then true else false) = false
    rw [if_neg hafter]
  · change (if
        (before (groupOffset ring leader (t.val + 2))).core.erase.core.bullet =
          ⟨1, by omega⟩
        then true else false) = true
    rw [if_pos hbefore]
  · intro s hts
    simp only [clockwiseMobileDummyBits]
    rw [hhigher s hts]

/-- Exact framing of every follower beyond offset one preserves the mobile
dummy rank. -/
theorem clockwiseMobileDummyRank_eq_of_bullets
    (ring : DirectedRing n) (leader : Fin n)
    (before after : Fin n → ExpiringAgentState psi kappa tau)
    (hframe : ∀ k, 1 < k → k < n →
      (after (groupOffset ring leader k)).core.erase.core.bullet =
        (before (groupOffset ring leader k)).core.erase.core.bullet) :
    clockwiseMobileDummyRank ring leader after =
      clockwiseMobileDummyRank ring leader before := by
  apply congrArg binaryRank
  funext i
  simp only [clockwiseMobileDummyBits]
  rw [hframe (i.val + 2) (by omega) (by omega)]

/-- The mobile dummy rank is bounded by its finite bit-pattern space. -/
theorem clockwiseMobileDummyRank_lt_two_pow
    (ring : DirectedRing n) (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    clockwiseMobileDummyRank ring leader C < 2 ^ (n - 2) :=
  binaryRank_lt_two_pow _

/-- Live bullets at the mobile follower offsets, beginning at clockwise
offset two.  Offset one is handled separately by the named leader edge, so
leader-edge reseeding cannot permute this bit vector. -/
def clockwiseMobileLiveBits
    (ring : DirectedRing n) (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    Fin (n - 2) → Bool :=
  fun i => if
    (C (groupOffset ring leader (i.val + 2))).core.erase.core.bullet =
      ⟨2, by omega⟩
    then true else false

/-- Binary position rank of live bullets beyond the immediate follower.  A
live bullet moving one edge toward the leader clears its old positive-weight
bit, while any new bit lies at a lower offset. -/
def clockwiseMobileLiveRank
    (ring : DirectedRing n) (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau) : Nat :=
  binaryRank (clockwiseMobileLiveBits ring leader C)

/-- Clearing one live bullet at a mobile offset while framing every higher
mobile offset strictly decreases the fixed-root live-bullet rank. -/
theorem clockwiseMobileLiveRank_lt_of_cleared_blocker
    (ring : DirectedRing n) (leader : Fin n)
    (before after : Fin n → ExpiringAgentState psi kappa tau)
    (t : Fin (n - 2))
    (hafter :
      (after (groupOffset ring leader (t.val + 2))).core.erase.core.bullet ≠
        ⟨2, by omega⟩)
    (hbefore :
      (before (groupOffset ring leader (t.val + 2))).core.erase.core.bullet =
        ⟨2, by omega⟩)
    (hhigher : ∀ s : Fin (n - 2), t.val < s.val →
      (after (groupOffset ring leader (s.val + 2))).core.erase.core.bullet =
        (before (groupOffset ring leader (s.val + 2))).core.erase.core.bullet) :
    clockwiseMobileLiveRank ring leader after <
      clockwiseMobileLiveRank ring leader before := by
  apply binaryRank_lt_of_highest_diff
    (clockwiseMobileLiveBits ring leader after)
    (clockwiseMobileLiveBits ring leader before) t
  · change (if
        (after (groupOffset ring leader (t.val + 2))).core.erase.core.bullet =
          ⟨2, by omega⟩
        then true else false) = false
    rw [if_neg hafter]
  · change (if
        (before (groupOffset ring leader (t.val + 2))).core.erase.core.bullet =
          ⟨2, by omega⟩
        then true else false) = true
    rw [if_pos hbefore]
  · intro s hts
    simp only [clockwiseMobileLiveBits]
    rw [hhigher s hts]

/-- Exact framing of every follower beyond offset one preserves the mobile
live-bullet rank. -/
theorem clockwiseMobileLiveRank_eq_of_bullets
    (ring : DirectedRing n) (leader : Fin n)
    (before after : Fin n → ExpiringAgentState psi kappa tau)
    (hframe : ∀ k, 1 < k → k < n →
      (after (groupOffset ring leader k)).core.erase.core.bullet =
        (before (groupOffset ring leader k)).core.erase.core.bullet) :
    clockwiseMobileLiveRank ring leader after =
      clockwiseMobileLiveRank ring leader before := by
  apply congrArg binaryRank
  funext i
  simp only [clockwiseMobileLiveBits]
  rw [hframe (i.val + 2) (by omega) (by omega)]

/-- The mobile live-bullet rank is bounded by its finite bit-pattern space. -/
theorem clockwiseMobileLiveRank_lt_two_pow
    (ring : DirectedRing n) (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    clockwiseMobileLiveRank ring leader C < 2 ^ (n - 2) :=
  binaryRank_lt_two_pow _

/-- Lexicographic retry measure.  The echo rank is the low digit and the
mobile dummy rank is the high digit in base `2^(n-1)`, which exceeds every
possible follower-echo pattern. -/
def clockwiseSignalRetryRank
    (ring : DirectedRing n) (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau) : Nat :=
  clockwiseMobileDummyRank ring leader C * 2 ^ (n - 1) +
    clockwiseEchoRank ring leader C

/-- A strict mobile-dummy decrease strictly decreases the combined retry
measure regardless of the new echo pattern. -/
theorem clockwiseSignalRetryRank_lt_of_mobile_lt
    (ring : DirectedRing n) (leader : Fin n)
    (before after : Fin n → ExpiringAgentState psi kappa tau)
    (hmobile : clockwiseMobileDummyRank ring leader after <
      clockwiseMobileDummyRank ring leader before) :
    clockwiseSignalRetryRank ring leader after <
      clockwiseSignalRetryRank ring leader before := by
  have hechoAfter : clockwiseEchoRank ring leader after < 2 ^ (n - 1) :=
    binaryRank_lt_two_pow _
  have hsucc : clockwiseMobileDummyRank ring leader after + 1 ≤
      clockwiseMobileDummyRank ring leader before := by omega
  have hmul := Nat.mul_le_mul_right (2 ^ (n - 1)) hsucc
  unfold clockwiseSignalRetryRank
  calc
    clockwiseMobileDummyRank ring leader after * 2 ^ (n - 1) +
          clockwiseEchoRank ring leader after <
        clockwiseMobileDummyRank ring leader after * 2 ^ (n - 1) +
          2 ^ (n - 1) :=
      Nat.add_lt_add_left hechoAfter _
    _ = (clockwiseMobileDummyRank ring leader after + 1) *
          2 ^ (n - 1) := by
      simp [Nat.add_mul]
    _ ≤ clockwiseMobileDummyRank ring leader before * 2 ^ (n - 1) := hmul
    _ ≤ clockwiseMobileDummyRank ring leader before * 2 ^ (n - 1) +
          clockwiseEchoRank ring leader before := by omega

/-- If the mobile rank does not increase and the echo rank strictly decreases,
the combined retry measure strictly decreases. -/
theorem clockwiseSignalRetryRank_lt_of_mobile_le_echo_lt
    (ring : DirectedRing n) (leader : Fin n)
    (before after : Fin n → ExpiringAgentState psi kappa tau)
    (hmobile : clockwiseMobileDummyRank ring leader after ≤
      clockwiseMobileDummyRank ring leader before)
    (hecho : clockwiseEchoRank ring leader after <
      clockwiseEchoRank ring leader before) :
    clockwiseSignalRetryRank ring leader after <
      clockwiseSignalRetryRank ring leader before := by
  by_cases heq : clockwiseMobileDummyRank ring leader after =
      clockwiseMobileDummyRank ring leader before
  · unfold clockwiseSignalRetryRank
    rw [heq]
    exact Nat.add_lt_add_left hecho _
  · exact clockwiseSignalRetryRank_lt_of_mobile_lt
      ring leader before after (Nat.lt_of_le_of_ne hmobile heq)

/-- The follower-echo rank is bounded by the number of follower bit patterns. -/
theorem clockwiseEchoRank_lt_two_pow
    (ring : DirectedRing n) (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    clockwiseEchoRank ring leader C < 2 ^ (n - 1) :=
  binaryRank_lt_two_pow _

/-- Clearing one clockwise blocker while framing every higher follower echo
strictly decreases the rank, even if arbitrary lower echoes are generated. -/
theorem clockwiseEchoRank_lt_of_cleared_blocker
    (ring : DirectedRing n) (leader : Fin n)
    (C D : Fin n → ExpiringAgentState psi kappa tau)
    (t : Fin (n - 1))
    (hD : (D (groupOffset ring leader (t.val + 1))).core.erase.core.echo =
      false)
    (hC : (C (groupOffset ring leader (t.val + 1))).core.erase.core.echo =
      true)
    (hhigher : ∀ i : Fin (n - 1), t.val < i.val →
      (D (groupOffset ring leader (i.val + 1))).core.erase.core.echo =
        (C (groupOffset ring leader (i.val + 1))).core.erase.core.echo) :
    clockwiseEchoRank ring leader D < clockwiseEchoRank ring leader C := by
  exact binaryRank_lt_of_highest_diff
    (clockwiseFollowerEchoBits ring leader D)
    (clockwiseFollowerEchoBits ring leader C) t hD hC hhigher

/-- The first true follower echo in clockwise order exists whenever the rank is
positive, with all earlier followers echo-free. -/
theorem exists_firstClockwiseEcho_of_rank_ne_zero
    (ring : DirectedRing n) (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (h : clockwiseEchoRank ring leader C ≠ 0) :
    ∃ t : Fin (n - 1),
      firstTrue? (clockwiseFollowerEchoBits ring leader C) = some t ∧
      (C (groupOffset ring leader (t.val + 1))).core.erase.core.echo = true ∧
      ∀ i : Fin (n - 1), i.val < t.val →
        (C (groupOffset ring leader (i.val + 1))).core.erase.core.echo =
          false :=
  exists_firstTrue_of_binaryRank_ne_zero
    (clockwiseFollowerEchoBits ring leader C) h

/-- A reset/echo configuration frame preserves the complete binary rank. -/
theorem clockwiseEchoRank_eq_of_resetEchoConfigFrame
    (ring : DirectedRing n) (leader : Fin n)
    {C D : Fin n → ExpiringAgentState psi kappa tau}
    (hframe : ResetEchoConfigFrame C D) :
    clockwiseEchoRank ring leader D = clockwiseEchoRank ring leader C := by
  apply congrArg binaryRank
  funext t
  exact (hframe (groupOffset ring leader (t.val + 1))).2.2.2.1

/-! ## Transition-independent clockwise prefix locality -/

/-- Configuration after the first `steps` clockwise edges starting at the
designated leader. -/
def clockwiseAttemptConfig
    (T : ExpiringTransition psi kappa tau)
    (ring : DirectedRing n) (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (steps : Nat) : Fin n → ExpiringAgentState psi kappa tau :=
  runLocalSchedule ring T C (resetSweepSchedule ring leader steps)

/-- One additional clockwise attempt edge is the expected local step. -/
theorem clockwiseAttemptConfig_succ
    (T : ExpiringTransition psi kappa tau)
    (ring : DirectedRing n) (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (steps : Nat) :
    clockwiseAttemptConfig T ring leader C (steps + 1) =
      localStep ring T (clockwiseAttemptConfig T ring leader C steps)
        (groupOffset ring leader steps) := by
  rw [clockwiseAttemptConfig,
    PPLLWallSweepSchedule.resetSweepSchedule.eq_def,
    runLocalSchedule_append_generic]
  rfl

/-- A clockwise prefix cannot modify any ring offset strictly ahead of its
last responder. -/
theorem clockwiseAttemptConfig_ahead_eq
    (T : ExpiringTransition psi kappa tau)
    (ring : DirectedRing n) (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (steps k : Nat) (hsk : steps < k) (hk : k < n) :
    clockwiseAttemptConfig T ring leader C steps
        (groupOffset ring leader k) =
      C (groupOffset ring leader k) := by
  induction steps with
  | zero => simp [clockwiseAttemptConfig, resetSweepSchedule, runLocalSchedule]
  | succ steps ih =>
      have hsteps : steps < n := by omega
      have hnext : steps + 1 < n := by omega
      have hke : groupOffset ring leader k ≠
          groupOffset ring leader steps := by
        apply groupOffset_ne_of_lt ring leader hk hsteps
        omega
      have hkj : groupOffset ring leader k ≠
          groupOffset ring leader (steps + 1) := by
        apply groupOffset_ne_of_lt ring leader hk hnext
        omega
      rw [clockwiseAttemptConfig_succ]
      have hsame :
          localStep ring T
            (clockwiseAttemptConfig T ring leader C steps)
            (groupOffset ring leader steps)
            (groupOffset ring leader k) =
          clockwiseAttemptConfig T ring leader C steps
            (groupOffset ring leader k) := by
        simp [localStep, hke, rightNeighbor_groupOffset, hkj]
      rw [hsame]
      exact ih (by omega)

/-- After an attempt through blocker `t`, every strictly higher follower echo
is unchanged. -/
theorem clockwiseAttempt_higher_echo_eq
    (T : ExpiringTransition psi kappa tau)
    (ring : DirectedRing n) (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (t s : Fin (n - 1)) (hts : t.val < s.val) :
    (clockwiseAttemptConfig T ring leader C (t.val + 1)
      (groupOffset ring leader (s.val + 1))).core.erase.core.echo =
    (C (groupOffset ring leader (s.val + 1))).core.erase.core.echo := by
  rw [clockwiseAttemptConfig_ahead_eq T ring leader C
    (t.val + 1) (s.val + 1) (by omega) (by omega)]

/-- Exact rank-relevant effect of a failed first-blocker attempt. -/
structure FirstBlockerEffect
    (ring : DirectedRing n) (leader : Fin n)
    (before after : Fin n → ExpiringAgentState psi kappa tau)
    (t : Fin (n - 1)) : Prop where
  blocker_present :
    (before (groupOffset ring leader (t.val + 1))).core.erase.core.echo = true
  blocker_cleared :
    (after (groupOffset ring leader (t.val + 1))).core.erase.core.echo = false
  higher_unchanged : ∀ s : Fin (n - 1), t.val < s.val →
    (after (groupOffset ring leader (s.val + 1))).core.erase.core.echo =
      (before (groupOffset ring leader (s.val + 1))).core.erase.core.echo

/-- Any newly generated echo after a first-blocker effect lies strictly below
the cleared blocker. -/
theorem FirstBlockerEffect.new_echo_lt
    {ring : DirectedRing n} {leader : Fin n}
    {before after : Fin n → ExpiringAgentState psi kappa tau}
    {t s : Fin (n - 1)}
    (h : FirstBlockerEffect ring leader before after t)
    (hbefore :
      (before (groupOffset ring leader (s.val + 1))).core.erase.core.echo =
        false)
    (hafter :
      (after (groupOffset ring leader (s.val + 1))).core.erase.core.echo =
        true) :
    s.val < t.val := by
  apply Classical.byContradiction
  intro hnot
  have hle : t.val ≤ s.val := by omega
  by_cases heq : t.val = s.val
  · have hfin : t = s := by
      apply Fin.ext
      exact heq
    subst s
    rw [h.blocker_cleared] at hafter
    contradiction
  · have hhigher := h.higher_unchanged s (by omega)
    rw [hhigher, hbefore] at hafter
    contradiction

/-- First-blocker effects strictly decrease the binary echo rank. -/
theorem FirstBlockerEffect.rank_lt
    {ring : DirectedRing n} {leader : Fin n}
    {before after : Fin n → ExpiringAgentState psi kappa tau}
    {t : Fin (n - 1)}
    (h : FirstBlockerEffect ring leader before after t) :
    clockwiseEchoRank ring leader after <
      clockwiseEchoRank ring leader before :=
  clockwiseEchoRank_lt_of_cleared_blocker ring leader before after t
    h.blocker_cleared h.blocker_present h.higher_unchanged

/-! ## Blocking-edge effect from a local transition contract -/

/-- If the final-input configuration is deletion-free and the transition
clears every priority-open responder echo, one more clockwise edge clears the
chosen blocker. -/
theorem clockwiseAttempt_blocker_cleared
    (T : ExpiringTransition psi kappa tau)
    (hresp : ∀ l r, WallPriorityOpen l r →
      (T l r).2.core.erase.core.echo = false)
    (ring : DirectedRing n) (hn : 1 < n) (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (t : Fin (n - 1))
    (hnoActive : NoActiveDeletion
      (clockwiseAttemptConfig T ring leader C t.val)) :
    (clockwiseAttemptConfig T ring leader C (t.val + 1)
      (groupOffset ring leader (t.val + 1))).core.erase.core.echo = false := by
  let current := clockwiseAttemptConfig T ring leader C t.val
  let e := groupOffset ring leader t.val
  let j := groupOffset ring leader (t.val + 1)
  have htBound : t.val < n := by omega
  have hjBound : t.val + 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j :=
    rightNeighbor_groupOffset ring leader t.val
  have hene : e ≠ j := by
    apply groupOffset_ne_of_lt ring leader htBound hjBound
    omega
  have hopen : WallPriorityOpen (current e) (current j) := by
    simpa [hneighbor] using
      WallPriorityOpen.of_noActiveDeletion current hnoActive ring e
  let q := T (current e) (current j)
  have hq : q.2.core.erase.core.echo = false :=
    hresp (current e) (current j) hopen
  have hright : localStep ring T current e j = q.2 := by
    simp [localStep, q, hneighbor, Ne.symm hene]
  rw [clockwiseAttemptConfig_succ]
  change (localStep ring T current e j).core.erase.core.echo = false
  rw [hright]
  exact hq

/-- A partial attempt through one present blocker has exactly the bit effect
needed by the rank proof. -/
theorem firstBlockerEffect_of_attempt
    (T : ExpiringTransition psi kappa tau)
    (hresp : ∀ l r, WallPriorityOpen l r →
      (T l r).2.core.erase.core.echo = false)
    (ring : DirectedRing n) (hn : 1 < n) (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (t : Fin (n - 1))
    (hpresent :
      (C (groupOffset ring leader (t.val + 1))).core.erase.core.echo = true)
    (hnoActive : NoActiveDeletion
      (clockwiseAttemptConfig T ring leader C t.val)) :
    FirstBlockerEffect ring leader C
      (clockwiseAttemptConfig T ring leader C (t.val + 1)) t := by
  refine ⟨hpresent,
    clockwiseAttempt_blocker_cleared T hresp ring hn leader C t hnoActive,
    ?_⟩
  intro s hts
  exact clockwiseAttempt_higher_echo_eq T ring leader C t s hts

/-- Concrete blocker attempts for the pre-CHECK transition strictly lower the
binary rank once the source-covered prefix supplies a deletion-free final
input. -/
theorem preCheckReset_firstBlockerAttempt_rank_lt
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (t : Fin (n - 1))
    (hpresent :
      (C (groupOffset ring leader (t.val + 1))).core.erase.core.echo = true)
    (hnoActive : NoActiveDeletion
      (clockwiseAttemptConfig
        (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
        ring leader C t.val)) :
    clockwiseEchoRank ring leader
        (clockwiseAttemptConfig
          (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
          ring leader C (t.val + 1)) <
      clockwiseEchoRank ring leader C := by
  exact (firstBlockerEffect_of_attempt
    (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
    (fun l r hopen =>
      wallSweepPreCheckResetPathStall_priority_open_responder_echo_false
        hpsi l r hopen)
    ring hn leader C t hpresent hnoActive).rank_lt

end PPLLWallSweepEchoRank

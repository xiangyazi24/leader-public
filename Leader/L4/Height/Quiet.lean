import Leader.L4.Compiler.NativeSpec
import Leader.L4.Height.Core

/-!
# One publication makes a site quiet, and quietness persists

Only `NativeRecord.tick` and `NativeRecord.err` are used below.  The native
base error is literally `err = true, tick = 0`, because the reset branch of
`finishNative` is `⟨0, true, {}, {}⟩`.
-/

namespace L4.Height.Recover.StageOne

open L4.Compiler.Native

set_option maxHeartbeats 4000000

variable {m : Nat}

/-- The modulus assumptions from the recovery statement: `M ≥ 4` and even. -/
def ClockParams (M : Nat) : Prop :=
  4 ≤ M ∧ 2 * (M / 2) = M

/-- The erroneous-lower-neighbour predicate used in the root guard. -/
def LowerErr (t : Nat) (y : NativeRecord) : Prop :=
  y.err = true ∧ y.tick < t

/-- Proposition-level form of the exceptional upper-gap guard. -/
def upperGapTick (M t u : Nat) : Prop :=
  t + 2 ≤ u ∧ ¬ (t = M / 2 ∧ u = M - 1)

/-- Record-level upper-gap predicate. -/
def UpperGap (M t : Nat) (y : NativeRecord) : Prop :=
  upperGapTick M t y.tick

/-- Exactly the `root` let-binding of `nativeClock`. -/
def IsRoot (M : Nat) (leftRec centerRec rightRec : NativeRecord) : Bool :=
  let t := centerRec.tick
  let p := M / 2
  let lowerErr := fun y : NativeRecord => y.err && decide (y.tick < t)
  let upperGap := fun y : NativeRecord =>
    decide (t + 2 ≤ y.tick) &&
      !(decide (t = p) && decide (y.tick = M - 1))
  if centerRec.err then !(lowerErr leftRec || lowerErr rightRec)
  else upperGap leftRec || upperGap rightRec

/-- The native base error, i.e. signed clock `-P`. -/
def BaseError (y : NativeRecord) : Prop :=
  y.err = true ∧ y.tick = 0

/-- Quietness of one three-record window. -/
def QuietWindow (M : Nat)
    (leftRec centerRec rightRec : NativeRecord) : Prop :=
  IsRoot M leftRec centerRec rightRec = true → BaseError centerRec

/-- Proposal made by one neighbour in `nativeClock`. -/
def proposalTick (M : Nat) (centerRec y : NativeRecord) : Nat :=
  if y.err && decide (y.tick + 1 < M / 2) &&
      decide (y.tick + 1 < centerRec.tick) then
    y.tick + 1
  else centerRec.tick

/-- The least propagation proposal. -/
def leastProposal (M : Nat)
    (leftRec centerRec rightRec : NativeRecord) : Nat :=
  min (proposalTick M centerRec leftRec)
    (proposalTick M centerRec rightRec)

/-- The Boolean `near` test in `nativeClock`. -/
def nearBool (centerRec y : NativeRecord) : Bool :=
  decide (y.tick ≤ centerRec.tick + 1) &&
    decide (centerRec.tick ≤ y.tick + 1) &&
    (decide (y.tick ≤ centerRec.tick) || !y.err)

/-- The Boolean successor-front test in `nativeClock`. -/
def atFrontBool (M : Nat) (centerRec y : NativeRecord) : Bool :=
  decide (y.tick = centerRec.tick) ||
    decide (y.tick = successor M centerRec.tick)

/-- First priority guard of `nativeClock`. -/
def resetGuard (M : Nat)
    (leftRec centerRec rightRec : NativeRecord) : Bool :=
  IsRoot M leftRec centerRec rightRec &&
    !(centerRec.err && decide (centerRec.tick = 0))

/-- Third priority guard of `nativeClock`. -/
def clearGuard (leftRec centerRec rightRec : NativeRecord) : Bool :=
  centerRec.err && nearBool centerRec leftRec && nearBool centerRec rightRec

/-- Fourth priority guard of `nativeClock`. -/
def incGuard (M : Nat)
    (leftRec centerRec rightRec : NativeRecord) : Bool :=
  !centerRec.err && atFrontBool M centerRec leftRec &&
    atFrontBool M centerRec rightRec

/-- `nativeClock` rewritten with named copies of all its guards. -/
theorem nativeClock_guards (M : Nat)
    (leftRec centerRec rightRec : NativeRecord) :
    nativeClock M leftRec centerRec rightRec =
      if resetGuard M leftRec centerRec rightRec then .reset
      else if leastProposal M leftRec centerRec rightRec < centerRec.tick then
        .propagate (leastProposal M leftRec centerRec rightRec)
      else if clearGuard leftRec centerRec rightRec then .clear
      else if incGuard M leftRec centerRec rightRec then
        .inc (successor M centerRec.tick)
      else .hold := by
  rfl

private theorem boolNot_true_iff_false (b : Bool) :
    ((!b) = true) ↔ b = false := by
  cases b <;> simp

private theorem isRoot_error_false_iff
    (M : Nat) (leftRec centerRec rightRec : NativeRecord)
    (hcenter : centerRec.err = true) :
    IsRoot M leftRec centerRec rightRec = false ↔
      LowerErr centerRec.tick leftRec ∨
        LowerErr centerRec.tick rightRec := by
  cases hleftErr : leftRec.err <;>
    cases hrightErr : rightRec.err <;>
      by_cases hleftTick : leftRec.tick < centerRec.tick <;>
        by_cases hrightTick : rightRec.tick < centerRec.tick <;>
          simp [IsRoot, LowerErr, hcenter, hleftErr, hrightErr,
            hleftTick, hrightTick]

private theorem isRoot_correct_false_iff
    (M : Nat) (leftRec centerRec rightRec : NativeRecord)
    (hcenter : centerRec.err = false) :
    IsRoot M leftRec centerRec rightRec = false ↔
      ¬ UpperGap M centerRec.tick leftRec ∧
        ¬ UpperGap M centerRec.tick rightRec := by
  by_cases hleftGap : centerRec.tick + 2 ≤ leftRec.tick <;>
    by_cases hrightGap : centerRec.tick + 2 ≤ rightRec.tick <;>
      by_cases hhalf : centerRec.tick = M / 2 <;>
        by_cases hleftLast : leftRec.tick = M - 1 <;>
          by_cases hrightLast : rightRec.tick = M - 1 <;>
            simp [IsRoot, UpperGap, upperGapTick, hcenter,
              hleftGap, hrightGap, hhalf, hleftLast, hrightLast]

private theorem proposal_lt_witness
    (M : Nat) (centerRec y : NativeRecord)
    (h : proposalTick M centerRec y < centerRec.tick) :
    y.err = true ∧ y.tick < proposalTick M centerRec y := by
  cases hy : y.err with
  | false =>
      simp [proposalTick, hy] at h
  | true =>
      by_cases hp : y.tick + 1 < M / 2
      · by_cases ht : y.tick + 1 < centerRec.tick
        · constructor
          · rfl
          · simp [proposalTick, hy, hp, ht]
        · simp [proposalTick, hy, hp, ht] at h
      · simp [proposalTick, hy, hp] at h

private theorem proposal_lt_half
    (M : Nat) (centerRec y : NativeRecord)
    (h : proposalTick M centerRec y < centerRec.tick) :
    proposalTick M centerRec y < M / 2 := by
  cases hy : y.err with
  | false =>
      simp [proposalTick, hy] at h
  | true =>
      by_cases hp : y.tick + 1 < M / 2
      · by_cases ht : y.tick + 1 < centerRec.tick
        · simp [proposalTick, hy, hp, ht]
        · simp [proposalTick, hy, hp, ht] at h
      · simp [proposalTick, hy, hp] at h

private theorem least_lt_witness
    (M : Nat) (leftRec centerRec rightRec : NativeRecord)
    (h : leastProposal M leftRec centerRec rightRec < centerRec.tick) :
    (leftRec.err = true ∧
      leftRec.tick < leastProposal M leftRec centerRec rightRec) ∨
    (rightRec.err = true ∧
      rightRec.tick < leastProposal M leftRec centerRec rightRec) := by
  unfold leastProposal at h ⊢
  by_cases hle : proposalTick M centerRec leftRec ≤
      proposalTick M centerRec rightRec
  · rw [Nat.min_eq_left hle] at h ⊢
    exact Or.inl (proposal_lt_witness M centerRec leftRec h)
  · have hge : proposalTick M centerRec rightRec ≤
        proposalTick M centerRec leftRec := by omega
    rw [Nat.min_eq_right hge] at h ⊢
    exact Or.inr (proposal_lt_witness M centerRec rightRec h)

private theorem least_lt_half
    (M : Nat) (leftRec centerRec rightRec : NativeRecord)
    (h : leastProposal M leftRec centerRec rightRec < centerRec.tick) :
    leastProposal M leftRec centerRec rightRec < M / 2 := by
  unfold leastProposal at h ⊢
  by_cases hle : proposalTick M centerRec leftRec ≤
      proposalTick M centerRec rightRec
  · rw [Nat.min_eq_left hle] at h ⊢
    exact proposal_lt_half M centerRec leftRec h
  · have hge : proposalTick M centerRec rightRec ≤
        proposalTick M centerRec leftRec := by omega
    rw [Nat.min_eq_right hge] at h ⊢
    exact proposal_lt_half M centerRec rightRec h

private theorem nativeClock_propagate_info
    (M : Nat) (leftRec centerRec rightRec : NativeRecord) (q : Nat)
    (hact : nativeClock M leftRec centerRec rightRec = .propagate q) :
    q < centerRec.tick ∧ q < M / 2 ∧
      ((leftRec.err = true ∧ leftRec.tick < q) ∨
       (rightRec.err = true ∧ rightRec.tick < q)) := by
  rw [nativeClock_guards] at hact
  by_cases hreset : resetGuard M leftRec centerRec rightRec = true
  · simp [hreset] at hact
  · by_cases hprop : leastProposal M leftRec centerRec rightRec < centerRec.tick
    · have hq : leastProposal M leftRec centerRec rightRec = q := by
        simpa [hreset, hprop] using hact
      subst q
      exact ⟨hprop, least_lt_half M leftRec centerRec rightRec hprop,
        least_lt_witness M leftRec centerRec rightRec hprop⟩
    · by_cases hclear : clearGuard leftRec centerRec rightRec = true
      · simp [hreset, hprop, hclear] at hact
      · by_cases hinc : incGuard M leftRec centerRec rightRec = true
        · simp [hreset, hprop, hclear, hinc] at hact
        · simp [hreset, hprop, hclear, hinc] at hact

private theorem nativeClock_clear_info
    (M : Nat) (leftRec centerRec rightRec : NativeRecord)
    (hact : nativeClock M leftRec centerRec rightRec = .clear) :
    centerRec.err = true ∧ nearBool centerRec leftRec = true ∧
      nearBool centerRec rightRec = true := by
  rw [nativeClock_guards] at hact
  by_cases hreset : resetGuard M leftRec centerRec rightRec = true
  · simp [hreset] at hact
  · by_cases hprop : leastProposal M leftRec centerRec rightRec < centerRec.tick
    · simp [hreset, hprop] at hact
    · by_cases hclear : clearGuard leftRec centerRec rightRec = true
      · unfold clearGuard at hclear
        have houter := Bool.and_eq_true_iff.mp hclear
        have hinner := Bool.and_eq_true_iff.mp houter.1
        exact ⟨hinner.1, hinner.2, houter.2⟩
      · by_cases hinc : incGuard M leftRec centerRec rightRec = true
        · simp [hreset, hprop, hclear, hinc] at hact
        · simp [hreset, hprop, hclear, hinc] at hact

private theorem nativeClock_inc_info
    (M : Nat) (leftRec centerRec rightRec : NativeRecord) (q : Nat)
    (hact : nativeClock M leftRec centerRec rightRec = .inc q) :
    q = successor M centerRec.tick ∧ centerRec.err = false ∧
      atFrontBool M centerRec leftRec = true ∧
      atFrontBool M centerRec rightRec = true := by
  rw [nativeClock_guards] at hact
  by_cases hreset : resetGuard M leftRec centerRec rightRec = true
  · simp [hreset] at hact
  · by_cases hprop : leastProposal M leftRec centerRec rightRec < centerRec.tick
    · simp [hreset, hprop] at hact
    · by_cases hclear : clearGuard leftRec centerRec rightRec = true
      · simp [hreset, hprop, hclear] at hact
      · by_cases hinc : incGuard M leftRec centerRec rightRec = true
        · have hq : successor M centerRec.tick = q := by
            simpa [hreset, hprop, hclear, hinc] using hact
          unfold incGuard at hinc
          have houter := Bool.and_eq_true_iff.mp hinc
          have hinner := Bool.and_eq_true_iff.mp houter.1
          have herr : centerRec.err = false :=
            (boolNot_true_iff_false centerRec.err).mp hinner.1
          exact ⟨hq.symm, herr, hinner.2, houter.2⟩
        · simp [hreset, hprop, hclear, hinc] at hact

private theorem near_true_tick_le
    (centerRec y : NativeRecord) (hnear : nearBool centerRec y = true) :
    y.tick ≤ centerRec.tick + 1 := by
  by_cases hle : y.tick ≤ centerRec.tick + 1
  · exact hle
  · have hfalse : nearBool centerRec y = false := by
      simp [nearBool, hle]
    rw [hfalse] at hnear
    cases hnear

private theorem near_higher_error_false
    (centerRec y : NativeRecord)
    (_hcenterErr : centerRec.err = true) (hyErr : y.err = true)
    (hlt : centerRec.tick < y.tick) :
    nearBool centerRec y = false := by
  have hnot : ¬ y.tick ≤ centerRec.tick := by omega
  simp [nearBool, hyErr, hnot]

private theorem atFront_true_cases
    (M : Nat) (centerRec y : NativeRecord)
    (hfront : atFrontBool M centerRec y = true) :
    y.tick = centerRec.tick ∨ y.tick = successor M centerRec.tick := by
  by_cases hsame : y.tick = centerRec.tick
  · exact Or.inl hsame
  · by_cases hnext : y.tick = successor M centerRec.tick
    · exact Or.inr hnext
    · have hfalse : atFrontBool M centerRec y = false := by
        simp [atFrontBool, hsame, hnext]
      rw [hfalse] at hfront
      cases hfront

private theorem half_lt {M : Nat} (hM : ClockParams M) : M / 2 < M := by
  unfold ClockParams at hM
  omega

private theorem successor_lt {M t : Nat} (hM : ClockParams M)
    (ht : t < M) : successor M t < M := by
  unfold successor
  by_cases hlast : t = M - 1
  · rw [if_pos hlast]
    exact half_lt hM
  · rw [if_neg hlast]
    omega

private theorem noUpper_after_center_increment
    {M t u : Nat}
    (hfront : u = t ∨ u = successor M t) :
    ¬ upperGapTick M (successor M t) u := by
  intro hgap
  rcases hfront with hsame | hnext
  · subst u
    unfold upperGapTick at hgap
    unfold successor at hgap
    by_cases hlast : t = M - 1
    · rw [if_pos hlast] at hgap
      apply hgap.2
      exact ⟨rfl, hlast⟩
    · rw [if_neg hlast] at hgap
      omega
  · rw [hnext] at hgap
    unfold upperGapTick at hgap
    omega

private theorem noUpper_after_neighbor_increment
    {M c t : Nat} (hM : ClockParams M)
    (hfront : c = t ∨ c = successor M t) :
    ¬ upperGapTick M c (successor M t) := by
  intro hgap
  rcases hfront with hsame | hnext
  · subst c
    unfold upperGapTick at hgap
    unfold successor at hgap
    by_cases hlast : t = M - 1
    · rw [if_pos hlast] at hgap
      have hp := half_lt hM
      omega
    · rw [if_neg hlast] at hgap
      omega
  · rw [hnext] at hgap
    unfold upperGapTick at hgap
    omega

private theorem noUpper_after_propagate
    {M c oldTick q : Nat}
    (hold : ¬ upperGapTick M c oldTick)
    (hqlt : q < oldTick) (hqhalf : q < M / 2) :
    ¬ upperGapTick M c q := by
  intro hnew
  unfold upperGapTick at hold hnew
  have holdGap : c + 2 ≤ oldTick := by omega
  have hexception : c = M / 2 ∧ oldTick = M - 1 := by
    by_cases hpair : c = M / 2 ∧ oldTick = M - 1
    · exact hpair
    · exact False.elim (hold ⟨holdGap, hpair⟩)
  omega

private theorem nativeClock_hold_root_base
    (M : Nat) (leftRec centerRec rightRec : NativeRecord)
    (hact : nativeClock M leftRec centerRec rightRec = .hold)
    (hroot : IsRoot M leftRec centerRec rightRec = true) :
    BaseError centerRec := by
  have hreset : resetGuard M leftRec centerRec rightRec ≠ true := by
    intro hg
    rw [nativeClock_guards] at hact
    simp [hg] at hact
  cases hcenter : centerRec.err with
  | false =>
      exfalso
      apply hreset
      simp [resetGuard, hroot, hcenter]
  | true =>
      by_cases hzero : centerRec.tick = 0
      · exact ⟨hcenter, hzero⟩
      · exfalso
        apply hreset
        simp [resetGuard, hroot, hcenter, hzero]

/-- One native update of the center of a three-record window. -/
def localUpdate (B M : Nat)
    (leftRec centerRec rightRec : NativeRecord) (delta : Bool) : NativeRecord :=
  finishNative B leftRec centerRec rightRec
    (nativeClock M leftRec centerRec rightRec) delta

private theorem localUpdate_tick_lt
    {B M : Nat} (hM : ClockParams M)
    (leftRec centerRec rightRec : NativeRecord) (delta : Bool)
    (hcenter : centerRec.tick < M) :
    (localUpdate B M leftRec centerRec rightRec delta).tick < M := by
  cases hact : nativeClock M leftRec centerRec rightRec with
  | reset =>
      simp [localUpdate, hact, finishNative]
      unfold ClockParams at hM
      omega
  | propagate q =>
      have hi := nativeClock_propagate_info M leftRec centerRec rightRec q hact
      simp [localUpdate, hact, finishNative]
      exact Nat.lt_trans hi.1 hcenter
  | clear =>
      simpa [localUpdate, hact, finishNative] using hcenter
  | inc q =>
      have hi := nativeClock_inc_info M leftRec centerRec rightRec q hact
      simp [localUpdate, hact, finishNative, hi.1]
      exact successor_lt hM hcenter
  | hold =>
      simpa [localUpdate, hact, finishNative] using hcenter

private theorem neighbor_update_preserves_lower
    {B M : Nat} (A Y D C : NativeRecord) (delta : Bool)
    (hside : C = A ∨ C = D) (hCerr : C.err = true)
    (hlower : LowerErr C.tick Y) :
    LowerErr C.tick (localUpdate B M A Y D delta) := by
  rcases hlower with ⟨hyErr, hlt⟩
  cases hact : nativeClock M A Y D with
  | reset =>
      simp only [localUpdate, hact, finishNative, LowerErr]
      exact ⟨True.intro, by omega⟩
  | propagate q =>
      have hi := nativeClock_propagate_info M A Y D q hact
      simp only [localUpdate, hact, finishNative, LowerErr]
      exact ⟨True.intro, Nat.lt_trans hi.1 hlt⟩
  | clear =>
      have hi := nativeClock_clear_info M A Y D hact
      have hnear : nearBool Y C = true := by
        rcases hside with hleft | hright
        · subst A
          exact hi.2.1
        · subst D
          exact hi.2.2
      have hfalse := near_higher_error_false Y C hyErr hCerr hlt
      rw [hfalse] at hnear
      cases hnear
  | inc q =>
      have hi := nativeClock_inc_info M A Y D q hact
      rw [hyErr] at hi
      cases hi.2.1
  | hold =>
      simpa [localUpdate, hact, finishNative, LowerErr] using
        (show Y.err = true ∧ Y.tick < C.tick from ⟨hyErr, hlt⟩)

private theorem neighbor_update_preserves_noUpper
    {B M : Nat} (hM : ClockParams M)
    (A Y D C : NativeRecord) (delta : Bool)
    (hside : C = A ∨ C = D)
    (hold : ¬ UpperGap M C.tick Y) :
    ¬ UpperGap M C.tick (localUpdate B M A Y D delta) := by
  cases hact : nativeClock M A Y D with
  | reset =>
      simp [localUpdate, hact, finishNative, UpperGap, upperGapTick]
  | propagate q =>
      have hi := nativeClock_propagate_info M A Y D q hact
      have holdTick : ¬ upperGapTick M C.tick Y.tick := by
        simpa [UpperGap] using hold
      have hnew := noUpper_after_propagate holdTick hi.1 hi.2.1
      simpa [localUpdate, hact, finishNative, UpperGap] using hnew
  | clear =>
      simpa [localUpdate, hact, finishNative, UpperGap] using hold
  | inc q =>
      have hi := nativeClock_inc_info M A Y D q hact
      have hfront : C.tick = Y.tick ∨ C.tick = successor M Y.tick := by
        rcases hside with hleft | hright
        · subst A
          exact atFront_true_cases M Y C hi.2.2.1
        · subst D
          exact atFront_true_cases M Y C hi.2.2.2
      have hnew := noUpper_after_neighbor_increment hM hfront
      simpa [localUpdate, hact, finishNative, UpperGap, hi.1] using hnew
  | hold =>
      simpa [localUpdate, hact, finishNative] using hold

private theorem root_false_of_quiet_correct
    (M : Nat) (leftRec centerRec rightRec : NativeRecord)
    (hquiet : QuietWindow M leftRec centerRec rightRec)
    (hcenter : centerRec.err = false) :
    IsRoot M leftRec centerRec rightRec = false := by
  cases hroot : IsRoot M leftRec centerRec rightRec with
  | false => rfl
  | true =>
      rcases hquiet hroot with ⟨herr, hzero⟩
      rw [hcenter] at herr
      cases herr

private theorem root_false_of_quiet_error_nonbase
    (M : Nat) (leftRec centerRec rightRec : NativeRecord)
    (hquiet : QuietWindow M leftRec centerRec rightRec)
    (hcenter : centerRec.err = true) (hnonbase : centerRec.tick ≠ 0) :
    IsRoot M leftRec centerRec rightRec = false := by
  cases hroot : IsRoot M leftRec centerRec rightRec with
  | false => rfl
  | true =>
      rcases hquiet hroot with ⟨herr, hzero⟩
      exact False.elim (hnonbase hzero)

private theorem self_correct_not_root
    (M : Nat) (y : NativeRecord) (hy : y.err = false) :
    IsRoot M y y y = false := by
  apply (isRoot_correct_false_iff M y y y hy).2
  constructor <;> intro hgap <;>
    unfold UpperGap upperGapTick at hgap <;> omega

private theorem quietWindow_after_own
    (B M : Nat) (leftRec centerRec rightRec : NativeRecord)
    (delta : Bool) :
    QuietWindow M leftRec
      (localUpdate B M leftRec centerRec rightRec delta) rightRec := by
  intro hroot
  cases hact : nativeClock M leftRec centerRec rightRec with
  | reset =>
      simp [localUpdate, hact, finishNative, BaseError]
  | propagate q =>
      have hi := nativeClock_propagate_info M leftRec centerRec rightRec q hact
      have hfalse :
          IsRoot M leftRec
            (localUpdate B M leftRec centerRec rightRec delta) rightRec = false := by
        apply (isRoot_error_false_iff M leftRec
          (localUpdate B M leftRec centerRec rightRec delta) rightRec
          (by simp [localUpdate, hact, finishNative])).2
        rcases hi.2.2 with hleft | hright
        · left
          simpa [localUpdate, hact, finishNative, LowerErr] using hleft
        · right
          simpa [localUpdate, hact, finishNative, LowerErr] using hright
      rw [hfalse] at hroot
      cases hroot
  | clear =>
      have hi := nativeClock_clear_info M leftRec centerRec rightRec hact
      have hleftLe := near_true_tick_le centerRec leftRec hi.2.1
      have hrightLe := near_true_tick_le centerRec rightRec hi.2.2
      have hnoLeft : ¬ UpperGap M centerRec.tick leftRec := by
        intro hgap
        unfold UpperGap upperGapTick at hgap
        omega
      have hnoRight : ¬ UpperGap M centerRec.tick rightRec := by
        intro hgap
        unfold UpperGap upperGapTick at hgap
        omega
      have hfalse :
          IsRoot M leftRec
            (localUpdate B M leftRec centerRec rightRec delta) rightRec = false := by
        apply (isRoot_correct_false_iff M leftRec
          (localUpdate B M leftRec centerRec rightRec delta) rightRec
          (by simp [localUpdate, hact, finishNative])).2
        constructor
        · simpa [localUpdate, hact, finishNative] using hnoLeft
        · simpa [localUpdate, hact, finishNative] using hnoRight
      rw [hfalse] at hroot
      cases hroot
  | inc q =>
      have hi := nativeClock_inc_info M leftRec centerRec rightRec q hact
      have hfrontLeft := atFront_true_cases M centerRec leftRec hi.2.2.1
      have hfrontRight := atFront_true_cases M centerRec rightRec hi.2.2.2
      have hnoLeftTick := noUpper_after_center_increment hfrontLeft
      have hnoRightTick := noUpper_after_center_increment hfrontRight
      have hnoLeft : ¬ UpperGap M q leftRec := by
        unfold UpperGap
        rw [hi.1]
        exact hnoLeftTick
      have hnoRight : ¬ UpperGap M q rightRec := by
        unfold UpperGap
        rw [hi.1]
        exact hnoRightTick
      have hfalse :
          IsRoot M leftRec
            (localUpdate B M leftRec centerRec rightRec delta) rightRec = false := by
        apply (isRoot_correct_false_iff M leftRec
          (localUpdate B M leftRec centerRec rightRec delta) rightRec
          (by simp [localUpdate, hact, finishNative])).2
        constructor
        · simpa [localUpdate, hact, finishNative] using hnoLeft
        · simpa [localUpdate, hact, finishNative] using hnoRight
      rw [hfalse] at hroot
      cases hroot
  | hold =>
      have hrootOld : IsRoot M leftRec centerRec rightRec = true := by
        simpa [localUpdate, hact, finishNative] using hroot
      have hbase := nativeClock_hold_root_base M leftRec centerRec rightRec
        hact hrootOld
      simpa [localUpdate, hact, finishNative, BaseError] using hbase

private theorem quietWindow_after_own_singleton
    (B M : Nat) (centerRec : NativeRecord) (delta : Bool) :
    let next := localUpdate B M centerRec centerRec centerRec delta
    QuietWindow M next next next := by
  dsimp
  intro hroot
  cases hact : nativeClock M centerRec centerRec centerRec with
  | reset =>
      simp [localUpdate, hact, finishNative, BaseError]
  | propagate q =>
      have hi := nativeClock_propagate_info M centerRec centerRec centerRec q hact
      rcases hi.2.2 with hleft | hright <;> omega
  | clear =>
      have herr :
          (localUpdate B M centerRec centerRec centerRec delta).err = false := by
        simp [localUpdate, hact, finishNative]
      have hfalse := self_correct_not_root M
        (localUpdate B M centerRec centerRec centerRec delta) herr
      rw [hfalse] at hroot
      cases hroot
  | inc q =>
      have herr :
          (localUpdate B M centerRec centerRec centerRec delta).err = false := by
        simp [localUpdate, hact, finishNative]
      have hfalse := self_correct_not_root M
        (localUpdate B M centerRec centerRec centerRec delta) herr
      rw [hfalse] at hroot
      cases hroot
  | hold =>
      have hrootOld : IsRoot M centerRec centerRec centerRec = true := by
        simpa [localUpdate, hact, finishNative] using hroot
      have hbase := nativeClock_hold_root_base M centerRec centerRec centerRec
        hact hrootOld
      simpa [localUpdate, hact, finishNative, BaseError] using hbase

private theorem quietWindow_preserved_left
    {B M : Nat} (hM : ClockParams M)
    (A leftRec centerRec rightRec : NativeRecord) (delta : Bool)
    (hquiet : QuietWindow M leftRec centerRec rightRec) :
    QuietWindow M (localUpdate B M A leftRec centerRec delta)
      centerRec rightRec := by
  intro hroot
  cases hcenter : centerRec.err with
  | true =>
      by_cases hzero : centerRec.tick = 0
      · exact ⟨hcenter, hzero⟩
      · have holdRoot := root_false_of_quiet_error_nonbase M
          leftRec centerRec rightRec hquiet hcenter hzero
        have hwitness :=
          (isRoot_error_false_iff M leftRec centerRec rightRec hcenter).1
            holdRoot
        have hwitness' :
            LowerErr centerRec.tick
                (localUpdate B M A leftRec centerRec delta) ∨
              LowerErr centerRec.tick rightRec := by
          rcases hwitness with hleft | hright
          · left
            exact neighbor_update_preserves_lower (B := B) (M := M)
              A leftRec centerRec centerRec delta (Or.inr rfl) hcenter hleft
          · exact Or.inr hright
        have hfalse :=
          (isRoot_error_false_iff M
            (localUpdate B M A leftRec centerRec delta)
            centerRec rightRec hcenter).2 hwitness'
        rw [hfalse] at hroot
        cases hroot
  | false =>
      have holdRoot := root_false_of_quiet_correct M
        leftRec centerRec rightRec hquiet hcenter
      have hno :=
        (isRoot_correct_false_iff M leftRec centerRec rightRec hcenter).1
          holdRoot
      have hnoLeft := neighbor_update_preserves_noUpper
        (B := B) (M := M) hM
        A leftRec centerRec centerRec delta (Or.inr rfl) hno.1
      have hfalse :=
        (isRoot_correct_false_iff M
          (localUpdate B M A leftRec centerRec delta)
          centerRec rightRec hcenter).2 ⟨hnoLeft, hno.2⟩
      rw [hfalse] at hroot
      cases hroot

private theorem quietWindow_preserved_right
    {B M : Nat} (hM : ClockParams M)
    (leftRec centerRec rightRec A : NativeRecord) (delta : Bool)
    (hquiet : QuietWindow M leftRec centerRec rightRec) :
    QuietWindow M leftRec centerRec
      (localUpdate B M centerRec rightRec A delta) := by
  intro hroot
  cases hcenter : centerRec.err with
  | true =>
      by_cases hzero : centerRec.tick = 0
      · exact ⟨hcenter, hzero⟩
      · have holdRoot := root_false_of_quiet_error_nonbase M
          leftRec centerRec rightRec hquiet hcenter hzero
        have hwitness :=
          (isRoot_error_false_iff M leftRec centerRec rightRec hcenter).1
            holdRoot
        have hwitness' :
            LowerErr centerRec.tick leftRec ∨
              LowerErr centerRec.tick
                (localUpdate B M centerRec rightRec A delta) := by
          rcases hwitness with hleft | hright
          · exact Or.inl hleft
          · right
            exact neighbor_update_preserves_lower (B := B) (M := M)
              centerRec rightRec A centerRec delta (Or.inl rfl)
              hcenter hright
        have hfalse :=
          (isRoot_error_false_iff M leftRec centerRec
            (localUpdate B M centerRec rightRec A delta) hcenter).2 hwitness'
        rw [hfalse] at hroot
        cases hroot
  | false =>
      have holdRoot := root_false_of_quiet_correct M
        leftRec centerRec rightRec hquiet hcenter
      have hno :=
        (isRoot_correct_false_iff M leftRec centerRec rightRec hcenter).1
          holdRoot
      have hnoRight := neighbor_update_preserves_noUpper
        (B := B) (M := M) hM
        centerRec rightRec A centerRec delta (Or.inl rfl) hno.2
      have hfalse :=
        (isRoot_correct_false_iff M leftRec centerRec
          (localUpdate B M centerRec rightRec A delta) hcenter).2
          ⟨hno.1, hnoRight⟩
      rw [hfalse] at hroot
      cases hroot

/-- Functional replacement of one site. -/
def setAt {α : Type} {m : Nat} (f : Fin m → α)
    (i : Fin m) (x : α) : Fin m → α :=
  fun j => if j = i then x else f j

@[simp] theorem setAt_self {α : Type} {m : Nat} (f : Fin m → α)
    (i : Fin m) (x : α) : setAt f i x i = x := by
  simp [setAt]

@[simp] theorem setAt_other {α : Type} {m : Nat} (f : Fin m → α)
    (i j : Fin m) (x : α) (h : j ≠ i) :
    setAt f i x j = f j := by
  simp [setAt, h]

/-- One asynchronous publication. -/
def activate {m : Nat} (B M : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) (i : Fin m) (delta : Bool) :
    Fin m → NativeRecord :=
  let next := localUpdate B M (c (left hm i)) (c i) (c (right hm i)) delta
  setAt c i next

/-- Every native tick lies in the clock alphabet. -/
def TickBound {m : Nat} (M : Nat) (c : Fin m → NativeRecord) : Prop :=
  ∀ i, (c i).tick < M

/-- A site is quiet when every current root there is the base error. -/
def Quiet {m : Nat} (M : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) (i : Fin m) : Prop :=
  QuietWindow M (c (left hm i)) (c i) (c (right hm i))

@[simp] private theorem recover_left_right (hm : 0 < m) (i : Fin m) :
    left hm (right hm i) = i := by
  apply Fin.ext
  by_cases h : i.val + 1 < m
  · have hr : (i.val + 1) % m = i.val + 1 := Nat.mod_eq_of_lt h
    simp only [right, hr, left]
    have he : i.val + 1 + m - 1 = i.val + m := by omega
    rw [he, Nat.add_mod]
    simp [Nat.mod_eq_of_lt i.isLt]
  · have h' : i.val + 1 = m := by omega
    simp only [right, left]
    rw [h', Nat.mod_self]
    simp only [Nat.zero_add]
    have hmone : m - 1 < m := by omega
    rw [Nat.mod_eq_of_lt hmone]
    omega

@[simp] private theorem recover_right_left (hm : 0 < m) (i : Fin m) :
    right hm (left hm i) = i := by
  apply Fin.ext
  by_cases hzero : i.val = 0
  · simp only [right, left]
    rw [hzero]
    simp only [Nat.zero_add]
    have hmone : m - 1 < m := by omega
    rw [Nat.mod_eq_of_lt hmone]
    have he : m - 1 + 1 = m := by omega
    rw [he, Nat.mod_self]
  · have hipos : 0 < i.val := Nat.pos_of_ne_zero hzero
    have hlt : i.val - 1 < m := by omega
    have hl : (i.val + m - 1) % m = i.val - 1 := by
      have he : i.val + m - 1 = (i.val - 1) + m := by omega
      rw [he, Nat.add_mod]
      simp [Nat.mod_eq_of_lt hlt]
    simp only [left, hl, right]
    have he : i.val - 1 + 1 = i.val := by omega
    rw [he, Nat.mod_eq_of_lt i.isLt]

private theorem recover_right_ne_self (hm : 0 < m) (hmone : m ≠ 1)
    (i : Fin m) : right hm i ≠ i := by
  intro h
  have hv : (i.val + 1) % m = i.val := by
    simpa [right] using congrArg Fin.val h
  by_cases hsmall : i.val + 1 < m
  · rw [Nat.mod_eq_of_lt hsmall] at hv
    omega
  · have heq : i.val + 1 = m := by omega
    rw [heq, Nat.mod_self] at hv
    apply hmone
    omega

private theorem recover_left_ne_self (hm : 0 < m) (hmone : m ≠ 1)
    (i : Fin m) : left hm i ≠ i := by
  intro h
  have hh := congrArg (right hm) h
  rw [recover_right_left hm i] at hh
  exact (recover_right_ne_self hm hmone i) hh.symm

/-- One publication by the site itself makes it quiet. -/
theorem quiet_after_own {B M : Nat} (hM : ClockParams M)
    (hm : 0 < m) (c : Fin m → NativeRecord)
    (i : Fin m) (delta : Bool) :
    Quiet M hm (activate B M hm c i delta) i := by
  by_cases hmone : m = 1
  · have hall : ∀ a b : Fin m, a = b := by
      intro a b
      apply Fin.ext
      omega
    have hleft : left hm i = i := hall _ _
    have hright : right hm i = i := hall _ _
    simpa [Quiet, activate, setAt, hleft, hright] using
      (quietWindow_after_own_singleton B M (c i) delta)
  · have hleft := recover_left_ne_self hm hmone i
    have hright := recover_right_ne_self hm hmone i
    simpa [Quiet, activate, setAt, hleft, hright] using
      (quietWindow_after_own B M (c (left hm i)) (c i)
        (c (right hm i)) delta)

/-- Updating one site preserves quietness at every already quiet site. -/
theorem quiet_preserved {B M : Nat} (hM : ClockParams M)
    (hm : 0 < m) (c : Fin m → NativeRecord)
    (i j : Fin m) (delta : Bool)
    (hquiet : Quiet M hm c i) :
    Quiet M hm (activate B M hm c j delta) i := by
  unfold Quiet at hquiet ⊢
  by_cases hji : j = i
  · subst j
    exact quiet_after_own (B := B) hM hm c i delta
  · have hic : i ≠ j := by
      intro h
      exact hji h.symm
    by_cases hleft : left hm i = j
    · by_cases hright : right hm i = j
      · have hj : j = left hm i := hleft.symm
        subst j
        have hci : i ≠ left hm i := by
          intro h
          exact hji h.symm
        have hll : left hm (left hm i) = i := by
          rw [← hright, recover_left_right]
        have hrr : right hm (left hm i) = i := recover_right_left hm i
        let Y := c (left hm i)
        let C := c i
        let N := localUpdate B M C Y C delta
        have hqzero : QuietWindow M Y C Y := by
          dsimp [Y, C]
          simpa [hright] using hquiet
        have hqleft : QuietWindow M N C Y := by
          dsimp [N]
          exact quietWindow_preserved_left (B := B) (M := M)
            hM C Y C Y delta hqzero
        have hqboth : QuietWindow M N C N := by
          exact quietWindow_preserved_right (B := B) (M := M)
            hM N C Y C delta hqleft
        simpa [activate, setAt, hci, hright, hll, hrr, Y, C, N] using hqboth
      · have hj : j = left hm i := hleft.symm
        subst j
        have hci : i ≠ left hm i := by
          intro h
          exact hji h.symm
        have hlocal := quietWindow_preserved_left (B := B) (M := M) hM
          (c (left hm (left hm i))) (c (left hm i)) (c i)
          (c (right hm i)) delta hquiet
        simpa [activate, setAt, hci, hright, recover_right_left] using hlocal
    · by_cases hright : right hm i = j
      · have hj : j = right hm i := hright.symm
        subst j
        have hci : i ≠ right hm i := by
          intro h
          exact hji h.symm
        have hlocal := quietWindow_preserved_right (B := B) (M := M) hM
          (c (left hm i)) (c i) (c (right hm i))
          (c (right hm (right hm i))) delta hquiet
        simpa [activate, setAt, hci, hleft, recover_left_right] using hlocal
      · simpa [activate, setAt, hic, hleft, hright] using hquiet

/-- The `tick < M` invariant is preserved by every publication. -/
theorem activate_tickBound {B M : Nat} (hM : ClockParams M)
    (hm : 0 < m) (c : Fin m → NativeRecord)
    (i : Fin m) (delta : Bool) (hbound : TickBound M c) :
    TickBound M (activate B M hm c i delta) := by
  intro j
  by_cases hji : j = i
  · subst j
    simp only [activate, setAt_self]
    exact localUpdate_tick_lt hM (c (left hm i)) (c i)
      (c (right hm i)) delta (hbound i)
  · simp [activate, hji, hbound j]

/-- First list element acts first. -/
def runWord {m : Nat} (B M : Nat) (hm : 0 < m) :
    List (Fin m × Bool) → (Fin m → NativeRecord) → Fin m → NativeRecord
  | [], c => c
  | e :: h, c => runWord B M hm h (activate B M hm c e.1 e.2)

/-- Site `i` occurs in an activation word. -/
def Activated {m : Nat} (h : List (Fin m × Bool)) (i : Fin m) : Prop :=
  ∃ delta, (i, delta) ∈ h

/-- Every site occurs at least once. -/
def Covered {m : Nat} (h : List (Fin m × Bool)) : Prop :=
  ∀ i, Activated h i

/-- Tick bounds persist along a word. -/
theorem runWord_tickBound {B M : Nat} (hM : ClockParams M)
    (hm : 0 < m) (h : List (Fin m × Bool))
    (c : Fin m → NativeRecord) (hbound : TickBound M c) :
    TickBound M (runWord B M hm h c) := by
  induction h generalizing c with
  | nil => exact hbound
  | cons e h ih =>
      exact ih (activate B M hm c e.1 e.2)
        (activate_tickBound (B := B) hM hm c e.1 e.2 hbound)

/-- Once quiet, a site remains quiet throughout any suffix. -/
theorem quiet_runWord {B M : Nat} (hM : ClockParams M)
    (hm : 0 < m) (h : List (Fin m × Bool))
    (c : Fin m → NativeRecord) (i : Fin m)
    (hquiet : Quiet M hm c i) :
    Quiet M hm (runWord B M hm h c) i := by
  induction h generalizing c with
  | nil => exact hquiet
  | cons e h ih =>
      exact ih (activate B M hm c e.1 e.2)
        (quiet_preserved (B := B) hM hm c i e.1 e.2 hquiet)

/-- If `i` occurs in the word, it is quiet at the endpoint. -/
theorem runWord_quiet_of_activated {B M : Nat} (hM : ClockParams M)
    (hm : 0 < m) (h : List (Fin m × Bool))
    (c : Fin m → NativeRecord) (i : Fin m)
    (hactivated : Activated h i) :
    Quiet M hm (runWord B M hm h c) i := by
  induction h generalizing c with
  | nil =>
      rcases hactivated with ⟨delta, hmem⟩
      simp at hmem
  | cons e h ih =>
      rcases e with ⟨j, delta⟩
      by_cases hji : j = i
      · subst j
        have hfirst : Quiet M hm (activate B M hm c i delta) i :=
          quiet_after_own (B := B) hM hm c i delta
        exact quiet_runWord (B := B) hM hm h
          (activate B M hm c i delta) i hfirst
      · have htail : Activated h i := by
          rcases hactivated with ⟨bit, hmem⟩
          refine ⟨bit, ?_⟩
          simp only [List.mem_cons] at hmem
          rcases hmem with hhead | htail
          · have hp := congrArg Prod.fst hhead
            exact False.elim (hji hp.symm)
          · exact htail
        exact ih (activate B M hm c j delta) htail

/-- After one covering prefix, every later state is quiet at every site. -/
theorem quiet_forever {B M : Nat} (hM : ClockParams M)
    (hm : 0 < m) (pre post : List (Fin m × Bool))
    (c : Fin m → NativeRecord) (hcover : Covered pre) :
    ∀ i, Quiet M hm
      (runWord B M hm post (runWord B M hm pre c)) i := by
  intro i
  have hcovered : Activated pre i := hcover i
  have hquiet := runWord_quiet_of_activated (B := B)
    hM hm pre c i hcovered
  exact quiet_runWord (B := B) hM hm post
    (runWord B M hm pre c) i hquiet

end L4.Height.Recover.StageOne

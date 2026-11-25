import Leader.L4.Compiler.NativeSpec
import Leader.L4.Height.Core

/-!
# Persistent bases, path caps, and the frozen clock condition

The paper uses the signed clock value `tick - P`, where `P = M/2`, for both
correct and erroneous records.  The proofs below carry the equivalent natural
inequalities on raw ticks: subtracting the same `P` from both sides preserves
order, `c_v ≤ c_u+1` is `tick_v ≤ tick_u+1`, and
`c_u < -P+D+1` is `tick_u < D+1`.

Quietness is stated literally as in the parallel Quiet module: whenever the
three-record window makes the center a root, the center is the base error.
-/

namespace L4.Height.Recover.StageTwo

open L4.Compiler.Native

set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

variable {m : Nat}

/-- The signed value used in the paper, expressed directly from a native
record.  The error bit does not change this conversion. -/
def signedVal (M : Nat) (r : NativeRecord) : Int :=
  Int.ofNat r.tick - Int.ofNat (M / 2)

/-- The clock assumptions used in recovery: an even modulus with nontrivial
half-period. -/
def ClockParams (M : Nat) : Prop :=
  2 ≤ M / 2 ∧ 2 * (M / 2) = M

/-- A record is in the range produced by decoding and by the recovery row. -/
def WellFormedRecord (M : Nat) (r : NativeRecord) : Prop :=
  r.tick < M ∧ (r.err = true → r.tick < M / 2)

def WellFormed {m : Nat} (M : Nat) (c : Fin m → NativeRecord) : Prop :=
  ∀ i, WellFormedRecord M (c i)

/-- Erroneous base: signed value `-P`. -/
def IsBase (M : Nat) (r : NativeRecord) : Prop :=
  r.err = true ∧ r.tick = 0

theorem isBase_signed (M : Nat) (r : NativeRecord) (h : IsBase M r) :
    signedVal M r = -(Int.ofNat (M / 2)) := by
  simp [signedVal, h.2]

theorem signedVal_le_cap_iff (M : Nat) (r : NativeRecord) (k : Nat) :
    signedVal M r ≤ -(Int.ofNat (M / 2)) + Int.ofNat k ↔
      r.tick ≤ k := by
  unfold signedVal
  constructor
  · intro h
    have hInt : Int.ofNat r.tick ≤ Int.ofNat k := by
      omega
    exact Int.ofNat_le.mp hInt
  · intro h
    have hInt : Int.ofNat r.tick ≤ Int.ofNat k :=
      Int.ofNat_le.mpr h
    omega

theorem signedVal_below_iff (M : Nat) (r : NativeRecord) (D : Nat) :
    signedVal M r < -(Int.ofNat (M / 2)) + Int.ofNat D + 1 ↔
      r.tick < D + 1 := by
  unfold signedVal
  constructor
  · intro h
    have hInt0 : Int.ofNat r.tick < Int.ofNat D + 1 := by
      omega
    have hInt : Int.ofNat r.tick < Int.ofNat (D + 1) := by
      simpa using hInt0
    exact Int.ofNat_lt.mp hInt
  · intro h
    have hInt : Int.ofNat r.tick < Int.ofNat (D + 1) :=
      Int.ofNat_lt.mpr h
    have hInt0 : Int.ofNat r.tick < Int.ofNat D + 1 := by
      simpa using hInt
    omega

/-! ## Literal decomposition of `nativeClock` -/

def lowerErrBool (t : Nat) (y : NativeRecord) : Bool :=
  y.err && decide (y.tick < t)

def upperGapBool (M t : Nat) (y : NativeRecord) : Bool :=
  decide (t + 2 ≤ y.tick) &&
    !(decide (t = M / 2) && decide (y.tick = M - 1))

/-- Exactly the `root` let-binding in `nativeClock`. -/
def IsRoot (M : Nat) (leftRec centerRec rightRec : NativeRecord) : Bool :=
  if centerRec.err then
    !(lowerErrBool centerRec.tick leftRec ||
      lowerErrBool centerRec.tick rightRec)
  else
    upperGapBool M centerRec.tick leftRec ||
      upperGapBool M centerRec.tick rightRec

def proposalTick (M : Nat) (centerRec y : NativeRecord) : Nat :=
  if y.err && decide (y.tick + 1 < M / 2) &&
      decide (y.tick + 1 < centerRec.tick) then
    y.tick + 1
  else centerRec.tick

def leastTick (M : Nat) (leftRec centerRec rightRec : NativeRecord) : Nat :=
  min (proposalTick M centerRec leftRec)
    (proposalTick M centerRec rightRec)

def nearBool (t : Nat) (y : NativeRecord) : Bool :=
  decide (y.tick ≤ t + 1) && decide (t ≤ y.tick + 1) &&
    (decide (y.tick ≤ t) || !y.err)

def frontBool (M t : Nat) (y : NativeRecord) : Bool :=
  decide (y.tick = t) || decide (y.tick = successor M t)

def resetGuard (M : Nat)
    (leftRec centerRec rightRec : NativeRecord) : Bool :=
  IsRoot M leftRec centerRec rightRec &&
    !(centerRec.err && decide (centerRec.tick = 0))

def clearGuard (leftRec centerRec rightRec : NativeRecord) : Bool :=
  centerRec.err && nearBool centerRec.tick leftRec &&
    nearBool centerRec.tick rightRec

def incGuard (M : Nat)
    (leftRec centerRec rightRec : NativeRecord) : Bool :=
  !centerRec.err && frontBool M centerRec.tick leftRec &&
    frontBool M centerRec.tick rightRec

def clockSpec (M : Nat)
    (leftRec centerRec rightRec : NativeRecord) : ClockAction :=
  if resetGuard M leftRec centerRec rightRec then .reset
  else if leastTick M leftRec centerRec rightRec < centerRec.tick then
    .propagate (leastTick M leftRec centerRec rightRec)
  else if clearGuard leftRec centerRec rightRec then .clear
  else if incGuard M leftRec centerRec rightRec then
    .inc (successor M centerRec.tick)
  else .hold

theorem nativeClock_eq_spec (M : Nat)
    (leftRec centerRec rightRec : NativeRecord) :
    nativeClock M leftRec centerRec rightRec =
      clockSpec M leftRec centerRec rightRec := by
  rfl

/-! ## Cyclic configurations and quietness -/

def replaceAt {α : Type} {m : Nat}
    (c : Fin m → α) (i : Fin m) (x : α) : Fin m → α :=
  fun j => if j = i then x else c j

@[simp] theorem replaceAt_self {α : Type} {m : Nat}
    (c : Fin m → α) (i : Fin m) (x : α) :
    replaceAt c i x i = x := by
  simp [replaceAt]

@[simp] theorem replaceAt_other {α : Type} {m : Nat}
    (c : Fin m → α) (i j : Fin m) (x : α) (h : j ≠ i) :
    replaceAt c i x j = c j := by
  simp [replaceAt, h]

/-- The literal native action at a site. -/
def actionAt {m : Nat} (M : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) (i : Fin m) : ClockAction :=
  nativeClock M (c (left hm i)) (c i) (c (right hm i))

/-- One asynchronous publication. -/
def activate {m : Nat} (B M : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) (i : Fin m) (delta : Bool) :
    Fin m → NativeRecord :=
  let L := c (left hm i)
  let C := c i
  let R := c (right hm i)
  let act := nativeClock M L C R
  replaceAt c i (finishNative B L C R act delta)

@[simp] theorem activate_other {m : Nat} (B M : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) (i j : Fin m) (delta : Bool)
    (h : j ≠ i) :
    activate B M hm c i delta j = c j := by
  simp [activate, h]

/-- The selected component is the literal `finishNative` result.  Keeping this
as a named rewrite avoids relying on `simp` to unfold the action alias. -/
@[simp] theorem activate_self_eq_finish {m : Nat}
    (B M : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) (i : Fin m) (delta : Bool) :
    activate B M hm c i delta i =
      finishNative B (c (left hm i)) (c i) (c (right hm i))
        (actionAt M hm c i) delta := by
  simp [activate, actionAt]

/-- Quietness of one literal three-record window. -/
def QuietWindow (M : Nat)
    (leftRec centerRec rightRec : NativeRecord) : Prop :=
  IsRoot M leftRec centerRec rightRec = true →
    centerRec.err = true ∧ centerRec.tick = 0

/-- Literal site quietness from the parallel Quiet round. -/
def QuietAt {m : Nat} (M : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) (i : Fin m) : Prop :=
  QuietWindow M (c (left hm i)) (c i) (c (right hm i))

def Quiet {m : Nat} (M : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) : Prop :=
  ∀ i, QuietAt M hm c i

/-- Undirected adjacency on the ring. -/
def Adjacent {m : Nat} (hm : 0 < m) (i j : Fin m) : Prop :=
  j = left hm i ∨ j = right hm i

@[simp] theorem recover_left_right {m : Nat} (hm : 0 < m) (i : Fin m) :
    left hm (right hm i) = i := by
  apply Fin.ext
  by_cases h : i.val + 1 < m
  · have hr : (i.val + 1) % m = i.val + 1 := Nat.mod_eq_of_lt h
    simp only [right, hr, left]
    have he : i.val + 1 + m - 1 = i.val + m := by omega
    rw [he, Nat.add_mod]
    simp [Nat.mod_eq_of_lt i.isLt]
  · have heq : i.val + 1 = m := by omega
    simp only [right, left]
    rw [heq, Nat.mod_self]
    simp only [Nat.zero_add]
    have hmone : m - 1 < m := by omega
    rw [Nat.mod_eq_of_lt hmone]
    omega

@[simp] theorem recover_right_left {m : Nat} (hm : 0 < m) (i : Fin m) :
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

theorem adjacent_symm {m : Nat} (hm : 0 < m) {i j : Fin m} :
    Adjacent hm i j → Adjacent hm j i := by
  intro h
  rcases h with h | h
  · subst j
    right
    exact (recover_right_left hm i).symm
  · subst j
    left
    exact (recover_left_right hm i).symm

/-! ## Frozen and Below -/

/-- The frozen condition in raw-tick form, equivalent to the paper's signed
condition. -/
def Frozen {m : Nat} (hm : 0 < m)
    (c : Fin m → NativeRecord) : Prop :=
  ∀ u, (c u).err = true → ∀ v, Adjacent hm u v →
    (c v).tick ≤ (c u).tick + 1

/-- The strict upper bound on every surviving error. -/
def Below {m : Nat} (D : Nat) (c : Fin m → NativeRecord) : Prop :=
  ∀ u, (c u).err = true → (c u).tick < D + 1

theorem frozen_signed {m : Nat} (M : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) (h : Frozen hm c)
    (u v : Fin m) (hu : (c u).err = true) (huv : Adjacent hm u v) :
    signedVal M (c v) ≤ signedVal M (c u) + 1 := by
  have ht := h u hu v huv
  have htInt0 :
      Int.ofNat (c v).tick ≤ Int.ofNat ((c u).tick + 1) :=
    Int.ofNat_le.mpr ht
  have htInt :
      Int.ofNat (c v).tick ≤ Int.ofNat (c u).tick + 1 := by
    simpa using htInt0
  unfold signedVal
  omega

theorem below_signed {m : Nat} (M D : Nat)
    (c : Fin m → NativeRecord) (h : Below D c)
    (u : Fin m) (hu : (c u).err = true) :
    signedVal M (c u) < -(Int.ofNat (M / 2)) + Int.ofNat D + 1 := by
  have ht := h u hu
  have htInt0 :
      Int.ofNat (c u).tick < Int.ofNat (D + 1) :=
    Int.ofNat_lt.mpr ht
  have htInt : Int.ofNat (c u).tick < Int.ofNat D + 1 := by
    simpa using htInt0
  unfold signedVal
  omega

/-! ## Persistent bases -/

theorem root_of_base (M : Nat)
    (leftRec centerRec rightRec : NativeRecord)
    (hbase : IsBase M centerRec) :
    IsRoot M leftRec centerRec rightRec = true := by
  unfold IsBase at hbase
  unfold IsRoot lowerErrBool
  simp [hbase.1, hbase.2]

theorem least_of_base (M : Nat)
    (leftRec centerRec rightRec : NativeRecord)
    (hbase : IsBase M centerRec) :
    leastTick M leftRec centerRec rightRec = 0 := by
  unfold IsBase at hbase
  unfold leastTick proposalTick
  simp [hbase.1, hbase.2]

/-- An erroneous base can only clear or hold.  In particular, the literal
native row cannot increment, reset, or propagate from a base. -/
theorem nativeClock_base_action (M : Nat)
    (leftRec centerRec rightRec : NativeRecord)
    (hbase : IsBase M centerRec) :
    nativeClock M leftRec centerRec rightRec = ClockAction.clear ∨
      nativeClock M leftRec centerRec rightRec = ClockAction.hold := by
  have hroot := root_of_base M leftRec centerRec rightRec hbase
  have hleast := least_of_base M leftRec centerRec rightRec hbase
  have hreset : resetGuard M leftRec centerRec rightRec = false := by
    unfold resetGuard
    simp [hroot, hbase.1, hbase.2]
  have hinc : incGuard M leftRec centerRec rightRec = false := by
    unfold incGuard
    simp [hbase.1]
  rw [nativeClock_eq_spec]
  unfold clockSpec
  rw [hreset, hleast, hbase.2]
  have hzero : ¬ 0 < 0 := Nat.lt_irrefl 0
  simp only [hzero, if_false]
  cases hc : clearGuard leftRec centerRec rightRec with
  | false =>
      right
      simp [hc, hinc]
  | true =>
      left
      simp [hc]

/-- A base remains a base after any publication, except exactly when its own
publication takes the clear branch.  The increment alternative mentioned in
the prose is impossible for an erroneous center in the literal row. -/
theorem base_persists {m : Nat} (B M : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) (a j : Fin m) (delta : Bool)
    (hbase : IsBase M (c a)) :
    IsBase M (activate B M hm c j delta a) ∨
      (j = a ∧ actionAt M hm c a = ClockAction.clear) := by
  by_cases hja : j = a
  · subst j
    have hact := nativeClock_base_action M
      (c (left hm a)) (c a) (c (right hm a)) hbase
    rcases hact with hclear | hhold
    · right
      exact ⟨rfl, by simpa [actionAt] using hclear⟩
    · left
      rw [activate_self_eq_finish]
      have hholdAt : actionAt M hm c a = ClockAction.hold := by
        simpa [actionAt] using hhold
      rw [hholdAt]
      simpa only [finishNative] using hbase
  · left
    have haj : a ≠ j := by
      intro h
      exact hja h.symm
    rw [activate_other B M hm c j a delta haj]
    exact hbase

/-- If the base itself publishes, loss of the base is equivalent to clearing. -/
theorem base_removed_exact {m : Nat} (B M : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) (a : Fin m) (delta : Bool)
    (hbase : IsBase M (c a)) :
    ¬ IsBase M (activate B M hm c a delta a) ↔
      actionAt M hm c a = ClockAction.clear := by
  have hact := nativeClock_base_action M
    (c (left hm a)) (c a) (c (right hm a)) hbase
  rcases hact with hclear | hhold
  · have hclearAt : actionAt M hm c a = ClockAction.clear := by
      simpa [actionAt] using hclear
    constructor
    · intro _
      exact hclearAt
    · intro _
      rw [activate_self_eq_finish, hclearAt]
      simp [finishNative, IsBase]
  · have hholdAt : actionAt M hm c a = ClockAction.hold := by
      simpa [actionAt] using hhold
    constructor
    · intro hnot
      exfalso
      apply hnot
      rw [activate_self_eq_finish, hholdAt]
      simpa only [finishNative] using hbase
    · intro hclearAt
      have hbad : ClockAction.hold = ClockAction.clear := by
        calc
          ClockAction.hold = actionAt M hm c a := hholdAt.symm
          _ = ClockAction.clear := hclearAt
      cases hbad

/-! ## The cap step -/

theorem frontBool_true_iff (M t : Nat) (y : NativeRecord) :
    frontBool M t y = true ↔
      y.tick = t ∨ y.tick = successor M t := by
  simp [frontBool]

theorem incGuard_front_left (M : Nat)
    (leftRec centerRec rightRec : NativeRecord)
    (h : incGuard M leftRec centerRec rightRec = true) :
    frontBool M centerRec.tick leftRec = true := by
  cases hf : frontBool M centerRec.tick leftRec with
  | false => simp [incGuard, hf] at h
  | true => rfl

theorem incGuard_front_right (M : Nat)
    (leftRec centerRec rightRec : NativeRecord)
    (h : incGuard M leftRec centerRec rightRec = true) :
    frontBool M centerRec.tick rightRec = true := by
  cases hf : frontBool M centerRec.tick rightRec with
  | false => simp [incGuard, hf] at h
  | true => rfl

theorem action_inc_info (M : Nat)
    (leftRec centerRec rightRec : NativeRecord) (q : Nat)
    (hact : nativeClock M leftRec centerRec rightRec = ClockAction.inc q) :
    q = successor M centerRec.tick ∧
      incGuard M leftRec centerRec rightRec = true := by
  rw [nativeClock_eq_spec] at hact
  unfold clockSpec at hact
  split at hact
  · cases hact
  · split at hact
    · cases hact
    · split at hact
      · cases hact
      · split at hact
        · cases hact
          constructor
          · rfl
          · assumption
        · cases hact

theorem proposal_lt_center (M : Nat)
    (centerRec y : NativeRecord)
    (h : proposalTick M centerRec y < centerRec.tick) :
    y.err = true ∧ y.tick + 1 < M / 2 ∧
      y.tick + 1 < centerRec.tick := by
  cases he : y.err with
  | false =>
      simp [proposalTick, he] at h
  | true =>
      by_cases hp : y.tick + 1 < M / 2
      · by_cases ht : y.tick + 1 < centerRec.tick
        · exact ⟨rfl, hp, ht⟩
        · simp [proposalTick, he, hp, ht] at h
      · simp [proposalTick, he, hp] at h

theorem least_lt_cases (M : Nat)
    (leftRec centerRec rightRec : NativeRecord)
    (h : leastTick M leftRec centerRec rightRec < centerRec.tick) :
    proposalTick M centerRec leftRec < centerRec.tick ∨
      proposalTick M centerRec rightRec < centerRec.tick := by
  unfold leastTick at h
  rcases Nat.le_total (proposalTick M centerRec leftRec)
      (proposalTick M centerRec rightRec) with hle | hle
  · rw [Nat.min_eq_left hle] at h
    exact Or.inl h
  · rw [Nat.min_eq_right hle] at h
    exact Or.inr h

/-- A sufficiently lower correct predecessor would itself be a forbidden
correct root, so quietness forces it to be erroneous. -/
theorem quiet_lower_forces_error_right (M : Nat)
    (farRec predRec centerRec : NativeRecord)
    (hq : QuietWindow M farRec predRec centerRec)
    (hpredP : predRec.tick < M / 2)
    (hgap : predRec.tick + 2 ≤ centerRec.tick) :
    predRec.err = true := by
  cases he : predRec.err with
  | true => rfl
  | false =>
      have hne : predRec.tick ≠ M / 2 := by omega
      have hup : upperGapBool M predRec.tick centerRec = true := by
        simp [upperGapBool, hgap, hne]
      have hroot : IsRoot M farRec predRec centerRec = true := by
        unfold IsRoot
        simp [he, hup]
      have hqbase := hq hroot
      rw [he] at hqbase
      cases hqbase.1

theorem quiet_lower_forces_error_left (M : Nat)
    (centerRec predRec farRec : NativeRecord)
    (hq : QuietWindow M centerRec predRec farRec)
    (hpredP : predRec.tick < M / 2)
    (hgap : predRec.tick + 2 ≤ centerRec.tick) :
    predRec.err = true := by
  cases he : predRec.err with
  | true => rfl
  | false =>
      have hne : predRec.tick ≠ M / 2 := by omega
      have hup : upperGapBool M predRec.tick centerRec = true := by
        simp [upperGapBool, hgap, hne]
      have hroot : IsRoot M centerRec predRec farRec = true := by
        unfold IsRoot
        simp [he, hup]
      have hqbase := hq hroot
      rw [he] at hqbase
      cases hqbase.1

theorem successor_le_cap_of_front (M k : Nat)
    (hM : ClockParams M)
    (predRec centerRec : NativeRecord)
    (hk : 1 ≤ k) (hkP : k < M / 2)
    (hpred : predRec.tick ≤ k - 1)
    (hcenter : centerRec.tick ≤ k)
    (hfront : predRec.tick = centerRec.tick ∨
      predRec.tick = successor M centerRec.tick) :
    successor M centerRec.tick ≤ k := by
  unfold ClockParams at hM
  rcases hfront with hsame | hnext
  · rw [hsame] at hpred
    have htlt : centerRec.tick < k := by omega
    have hcenterP : centerRec.tick < M / 2 := by omega
    have hnot : centerRec.tick ≠ M - 1 := by
      intro hlast
      rw [← hM.2] at hlast
      omega
    unfold successor
    rw [if_neg hnot]
    omega
  · rw [← hnext]
    omega

theorem finish_strict_lower_left (B M k : Nat)
    (leftRec centerRec rightRec : NativeRecord) (delta : Bool)
    (hleftErr : leftRec.err = true)
    (hleftP : leftRec.tick + 1 < M / 2)
    (hstrict : leftRec.tick + 1 < centerRec.tick)
    (hcap : leftRec.tick + 1 ≤ k) :
    (finishNative B leftRec centerRec rightRec
      (nativeClock M leftRec centerRec rightRec) delta).tick ≤ k := by
  have hp : proposalTick M centerRec leftRec = leftRec.tick + 1 := by
    simp [proposalTick, hleftErr, hleftP, hstrict]
  have hleastLe : leastTick M leftRec centerRec rightRec ≤
      leftRec.tick + 1 := by
    unfold leastTick
    rw [hp]
    exact Nat.min_le_left _ _
  have hleastLt : leastTick M leftRec centerRec rightRec <
      centerRec.tick := Nat.lt_of_le_of_lt hleastLe hstrict
  rw [nativeClock_eq_spec]
  cases hr : resetGuard M leftRec centerRec rightRec with
  | true =>
      have hspec : clockSpec M leftRec centerRec rightRec =
          ClockAction.reset := by
        simp [clockSpec, hr]
      rw [hspec]
      simp [finishNative]
  | false =>
      have hspec : clockSpec M leftRec centerRec rightRec =
          ClockAction.propagate
            (leastTick M leftRec centerRec rightRec) := by
        simp [clockSpec, hr, hleastLt]
      rw [hspec]
      simp [finishNative]
      exact Nat.le_trans hleastLe hcap

theorem finish_strict_lower_right (B M k : Nat)
    (leftRec centerRec rightRec : NativeRecord) (delta : Bool)
    (hrightErr : rightRec.err = true)
    (hrightP : rightRec.tick + 1 < M / 2)
    (hstrict : rightRec.tick + 1 < centerRec.tick)
    (hcap : rightRec.tick + 1 ≤ k) :
    (finishNative B leftRec centerRec rightRec
      (nativeClock M leftRec centerRec rightRec) delta).tick ≤ k := by
  have hp : proposalTick M centerRec rightRec = rightRec.tick + 1 := by
    simp [proposalTick, hrightErr, hrightP, hstrict]
  have hleastLe : leastTick M leftRec centerRec rightRec ≤
      rightRec.tick + 1 := by
    unfold leastTick
    rw [hp]
    exact Nat.min_le_right _ _
  have hleastLt : leastTick M leftRec centerRec rightRec <
      centerRec.tick := Nat.lt_of_le_of_lt hleastLe hstrict
  rw [nativeClock_eq_spec]
  cases hr : resetGuard M leftRec centerRec rightRec with
  | true =>
      have hspec : clockSpec M leftRec centerRec rightRec =
          ClockAction.reset := by
        simp [clockSpec, hr]
      rw [hspec]
      simp [finishNative]
  | false =>
      have hspec : clockSpec M leftRec centerRec rightRec =
          ClockAction.propagate
            (leastTick M leftRec centerRec rightRec) := by
        simp [clockSpec, hr, hleastLt]
      rw [hspec]
      simp [finishNative]
      exact Nat.le_trans hleastLe hcap

theorem finish_existing_cap_left (B M k : Nat)
    (hM : ClockParams M)
    (leftRec centerRec rightRec : NativeRecord) (delta : Bool)
    (hk : 1 ≤ k) (hkP : k < M / 2)
    (hleft : leftRec.tick ≤ k - 1)
    (hcenter : centerRec.tick ≤ k) :
    (finishNative B leftRec centerRec rightRec
      (nativeClock M leftRec centerRec rightRec) delta).tick ≤ k := by
  rw [nativeClock_eq_spec]
  cases hr : resetGuard M leftRec centerRec rightRec with
  | true =>
      have hspec : clockSpec M leftRec centerRec rightRec =
          ClockAction.reset := by simp [clockSpec, hr]
      rw [hspec]
      simp [finishNative]
  | false =>
      by_cases hp : leastTick M leftRec centerRec rightRec < centerRec.tick
      · have hspec : clockSpec M leftRec centerRec rightRec =
            ClockAction.propagate
              (leastTick M leftRec centerRec rightRec) := by
          simp [clockSpec, hr, hp]
        rw [hspec]
        simp [finishNative]
        omega
      · cases hc : clearGuard leftRec centerRec rightRec with
        | true =>
            have hspec : clockSpec M leftRec centerRec rightRec =
                ClockAction.clear := by
              simp [clockSpec, hr, hp, hc]
            rw [hspec]
            simp [finishNative]
            exact hcenter
        | false =>
            cases hi : incGuard M leftRec centerRec rightRec with
            | false =>
                have hspec : clockSpec M leftRec centerRec rightRec =
                    ClockAction.hold := by
                  simp [clockSpec, hr, hp, hc, hi]
                rw [hspec]
                simp [finishNative]
                exact hcenter
            | true =>
                have hfrontBool := incGuard_front_left M
                  leftRec centerRec rightRec hi
                have hfront :=
                  (frontBool_true_iff M centerRec.tick leftRec).1 hfrontBool
                have hs := successor_le_cap_of_front M k hM
                  leftRec centerRec hk hkP hleft hcenter hfront
                have hspec : clockSpec M leftRec centerRec rightRec =
                    ClockAction.inc (successor M centerRec.tick) := by
                  simp [clockSpec, hr, hp, hc, hi]
                rw [hspec]
                simp [finishNative]
                exact hs

theorem finish_existing_cap_right (B M k : Nat)
    (hM : ClockParams M)
    (leftRec centerRec rightRec : NativeRecord) (delta : Bool)
    (hk : 1 ≤ k) (hkP : k < M / 2)
    (hright : rightRec.tick ≤ k - 1)
    (hcenter : centerRec.tick ≤ k) :
    (finishNative B leftRec centerRec rightRec
      (nativeClock M leftRec centerRec rightRec) delta).tick ≤ k := by
  rw [nativeClock_eq_spec]
  cases hr : resetGuard M leftRec centerRec rightRec with
  | true =>
      have hspec : clockSpec M leftRec centerRec rightRec =
          ClockAction.reset := by simp [clockSpec, hr]
      rw [hspec]
      simp [finishNative]
  | false =>
      by_cases hp : leastTick M leftRec centerRec rightRec < centerRec.tick
      · have hspec : clockSpec M leftRec centerRec rightRec =
            ClockAction.propagate
              (leastTick M leftRec centerRec rightRec) := by
          simp [clockSpec, hr, hp]
        rw [hspec]
        simp [finishNative]
        omega
      · cases hc : clearGuard leftRec centerRec rightRec with
        | true =>
            have hspec : clockSpec M leftRec centerRec rightRec =
                ClockAction.clear := by
              simp [clockSpec, hr, hp, hc]
            rw [hspec]
            simp [finishNative]
            exact hcenter
        | false =>
            cases hi : incGuard M leftRec centerRec rightRec with
            | false =>
                have hspec : clockSpec M leftRec centerRec rightRec =
                    ClockAction.hold := by
                  simp [clockSpec, hr, hp, hc, hi]
                rw [hspec]
                simp [finishNative]
                exact hcenter
            | true =>
                have hfrontBool := incGuard_front_right M
                  leftRec centerRec rightRec hi
                have hfront :=
                  (frontBool_true_iff M centerRec.tick rightRec).1 hfrontBool
                have hs := successor_le_cap_of_front M k hM
                  rightRec centerRec hk hkP hright hcenter hfront
                have hspec : clockSpec M leftRec centerRec rightRec =
                    ClockAction.inc (successor M centerRec.tick) := by
                  simp [clockSpec, hr, hp, hc, hi]
                rw [hspec]
                simp [finishNative]
                exact hs

/-- One service of the next vertex establishes the next path cap when the
predecessor is on the left.  The natural cap `k` is the signed cap `-P+k`. -/
theorem cap_step (B M k : Nat) (hM : ClockParams M)
    (farRec predRec centerRec rightRec : NativeRecord) (delta : Bool)
    (hk : 1 ≤ k) (hkP : k < M / 2)
    (hq : QuietWindow M farRec predRec centerRec)
    (hpred : predRec.tick ≤ k - 1) :
    (finishNative B predRec centerRec rightRec
      (nativeClock M predRec centerRec rightRec) delta).tick ≤ k := by
  by_cases hcenter : centerRec.tick ≤ k
  · exact finish_existing_cap_left B M k hM predRec centerRec rightRec
      delta hk hkP hpred hcenter
  · have hgap : predRec.tick + 2 ≤ centerRec.tick := by omega
    have hpredP : predRec.tick < M / 2 := by omega
    have herr := quiet_lower_forces_error_right M
      farRec predRec centerRec hq hpredP hgap
    have hplusP : predRec.tick + 1 < M / 2 := by omega
    have hstrict : predRec.tick + 1 < centerRec.tick := by omega
    have hcap : predRec.tick + 1 ≤ k := by omega
    exact finish_strict_lower_left B M k predRec centerRec rightRec
      delta herr hplusP hstrict hcap

/-- Symmetric path-cap step for a predecessor on the right. -/
theorem cap_step_right (B M k : Nat) (hM : ClockParams M)
    (leftRec centerRec predRec farRec : NativeRecord) (delta : Bool)
    (hk : 1 ≤ k) (hkP : k < M / 2)
    (hq : QuietWindow M centerRec predRec farRec)
    (hpred : predRec.tick ≤ k - 1) :
    (finishNative B leftRec centerRec predRec
      (nativeClock M leftRec centerRec predRec) delta).tick ≤ k := by
  by_cases hcenter : centerRec.tick ≤ k
  · exact finish_existing_cap_right B M k hM leftRec centerRec predRec
      delta hk hkP hpred hcenter
  · have hgap : predRec.tick + 2 ≤ centerRec.tick := by omega
    have hpredP : predRec.tick < M / 2 := by omega
    have herr := quiet_lower_forces_error_left M
      centerRec predRec farRec hq hpredP hgap
    have hplusP : predRec.tick + 1 < M / 2 := by omega
    have hstrict : predRec.tick + 1 < centerRec.tick := by omega
    have hcap : predRec.tick + 1 ≤ k := by omega
    exact finish_strict_lower_right B M k leftRec centerRec predRec
      delta herr hplusP hstrict hcap

/-- A support condition saying that the left predecessor continues to carry
its path cap and remains quiet. -/
def LeftCapSupport {m : Nat} (M k : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) (v : Fin m) : Prop :=
  QuietAt M hm c (left hm v) ∧
    (c (left hm v)).tick ≤ k - 1

/-- One arbitrary activation preserves an already attained cap at `v`,
provided the left predecessor support holds in the pre-state. -/
theorem cap_preserved_one {m : Nat} (B M k : Nat)
    (hM : ClockParams M) (hm : 0 < m)
    (c : Fin m → NativeRecord) (v j : Fin m) (delta : Bool)
    (hk : 1 ≤ k) (hkP : k < M / 2)
    (hcap : (c v).tick ≤ k)
    (hsupport : LeftCapSupport M k hm c v) :
    (activate B M hm c j delta v).tick ≤ k := by
  by_cases hjv : j = v
  · subst j
    have hq : QuietWindow M
        (c (left hm (left hm v))) (c (left hm v)) (c v) := by
      simpa [QuietAt] using hsupport.1
    have hstep := cap_step B M k hM
      (c (left hm (left hm v))) (c (left hm v)) (c v)
      (c (right hm v)) delta hk hkP hq hsupport.2
    rw [activate_self_eq_finish]
    simpa only [actionAt] using hstep
  · have hvj : v ≠ j := by
      intro h
      exact hjv h.symm
    rw [activate_other B M hm c j v delta hvj]
    exact hcap

abbrev Activation {m : Nat} := Fin m × Bool

def runActivations {m : Nat} (B M : Nat) (hm : 0 < m) :
    List (Activation (m := m)) → (Fin m → NativeRecord) →
      (Fin m → NativeRecord)
  | [], c => c
  | e :: h, c =>
      runActivations B M hm h (activate B M hm c e.1 e.2)

/-- The support condition is assumed at every pre-state of a history.  This is
exactly what base persistence plus the already-established predecessor cap
supplies in the shortest-path induction. -/
def SupportsAlong {m : Nat} (B M k : Nat) (hm : 0 < m)
    (v : Fin m) : (Fin m → NativeRecord) →
      List (Activation (m := m)) → Prop
  | _, [] => True
  | c, e :: h =>
      LeftCapSupport M k hm c v ∧
        SupportsAlong B M k hm v
          (activate B M hm c e.1 e.2) h

/-- Once attained, a cap remains true through every later activation while
its predecessor support persists. -/
theorem cap_stays {m : Nat} (B M k : Nat)
    (hM : ClockParams M) (hm : 0 < m)
    (v : Fin m) (h : List (Activation (m := m)))
    (c : Fin m → NativeRecord)
    (hk : 1 ≤ k) (hkP : k < M / 2)
    (hcap : (c v).tick ≤ k)
    (hsupport : SupportsAlong B M k hm v c h) :
    (runActivations B M hm h c v).tick ≤ k := by
  induction h generalizing c with
  | nil => exact hcap
  | cons e h ih =>
      rcases hsupport with ⟨hs, htail⟩
      have hnext := cap_preserved_one B M k hM hm c v e.1 e.2
        hk hkP hcap hs
      exact ih (activate B M hm c e.1 e.2) hnext htail

/-! ## Frozen preservation -/

theorem resetGuard_false_of_quiet {m : Nat} (M : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) (hq : Quiet M hm c) (i : Fin m) :
    resetGuard M (c (left hm i)) (c i) (c (right hm i)) = false := by
  cases hr : IsRoot M (c (left hm i)) (c i) (c (right hm i)) with
  | false => simp [resetGuard, hr]
  | true =>
      have hb := hq i hr
      simp [resetGuard, hr, hb.1, hb.2]

theorem least_not_lt_of_frozen {m : Nat} (M : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) (hf : Frozen hm c) (i : Fin m) :
    ¬ leastTick M (c (left hm i)) (c i) (c (right hm i)) <
      (c i).tick := by
  intro hlt
  rcases least_lt_cases M (c (left hm i)) (c i) (c (right hm i)) hlt
      with hleft | hright
  · have hp := proposal_lt_center M (c i) (c (left hm i)) hleft
    have hadj : Adjacent hm (left hm i) i :=
      Or.inr (recover_right_left hm i).symm
    have hbound := hf (left hm i) hp.1 i hadj
    omega
  · have hp := proposal_lt_center M (c i) (c (right hm i)) hright
    have hadj : Adjacent hm (right hm i) i :=
      Or.inl (recover_left_right hm i).symm
    have hbound := hf (right hm i) hp.1 i hadj
    omega

/-- Under Quiet and Frozen, an erroneous center can only clear or hold. -/
theorem action_of_error {m : Nat} (M : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) (hq : Quiet M hm c)
    (hf : Frozen hm c) (i : Fin m) (hi : (c i).err = true) :
    actionAt M hm c i = ClockAction.clear ∨
      actionAt M hm c i = ClockAction.hold := by
  have hr := resetGuard_false_of_quiet M hm c hq i
  have hp := least_not_lt_of_frozen M hm c hf i
  unfold actionAt
  rw [nativeClock_eq_spec]
  cases hc : clearGuard (c (left hm i)) (c i) (c (right hm i)) with
  | true =>
      left
      simp [clockSpec, hr, hp, hc]
  | false =>
      right
      have hinc : incGuard M (c (left hm i)) (c i) (c (right hm i)) =
          false := by
        simp [incGuard, hi]
      simp [clockSpec, hr, hp, hc, hinc]

/-- Under Quiet and Frozen, a correct center can only increment or hold. -/
theorem action_of_correct {m : Nat} (M : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) (hq : Quiet M hm c)
    (hf : Frozen hm c) (i : Fin m) (hi : (c i).err = false) :
    actionAt M hm c i = ClockAction.inc (successor M (c i).tick) ∨
      actionAt M hm c i = ClockAction.hold := by
  have hr := resetGuard_false_of_quiet M hm c hq i
  have hp := least_not_lt_of_frozen M hm c hf i
  unfold actionAt
  rw [nativeClock_eq_spec]
  have hclear : clearGuard (c (left hm i)) (c i) (c (right hm i)) =
      false := by simp [clearGuard, hi]
  cases hinc : incGuard M (c (left hm i)) (c i) (c (right hm i)) with
  | true =>
      left
      simp [clockSpec, hr, hp, hclear, hinc]
  | false =>
      right
      simp [clockSpec, hr, hp, hclear, hinc]

theorem activate_of_hold {m : Nat} (B M : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) (i : Fin m) (delta : Bool)
    (hact : actionAt M hm c i = ClockAction.hold) :
    activate B M hm c i delta = c := by
  funext j
  by_cases hji : j = i
  · subst j
    rw [activate_self_eq_finish, hact]
    rfl
  · exact activate_other B M hm c i j delta hji

theorem successor_lt_modulus (M t : Nat)
    (hM : ClockParams M) (ht : t < M) :
    successor M t < M := by
  unfold successor
  by_cases hlast : t = M - 1
  · rw [if_pos hlast]
    unfold ClockParams at hM
    omega
  · rw [if_neg hlast]
    omega

/-- No activation can create an error once Quiet and Frozen hold.  A new
selected-site error is necessarily an old error taking the hold branch. -/
theorem activated_error_implies_hold {m : Nat} (B M : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) (hq : Quiet M hm c)
    (hf : Frozen hm c) (i : Fin m) (delta : Bool)
    (hnew : (activate B M hm c i delta i).err = true) :
    actionAt M hm c i = ClockAction.hold ∧ (c i).err = true := by
  cases hi : (c i).err with
  | true =>
      have ha := action_of_error M hm c hq hf i hi
      rcases ha with hclear | hhold
      · have hbad := hnew
        rw [activate_self_eq_finish, hclear] at hbad
        simp only [finishNative] at hbad
        cases hbad
      · exact ⟨hhold, rfl⟩
  | false =>
      have ha := action_of_correct M hm c hq hf i hi
      rcases ha with hinc | hhold
      · have hbad := hnew
        rw [activate_self_eq_finish, hinc] at hbad
        simp only [finishNative] at hbad
        cases hbad
      · have hbad := hnew
        rw [activate_self_eq_finish, hhold] at hbad
        simp only [finishNative, hi] at hbad
        cases hbad

theorem successor_le_error_neighbor (M : Nat) (hM : ClockParams M)
    (errorRec centerRec : NativeRecord)
    (herrP : errorRec.tick < M / 2)
    (hfront : errorRec.tick = centerRec.tick ∨
      errorRec.tick = successor M centerRec.tick) :
    successor M centerRec.tick ≤ errorRec.tick + 1 := by
  unfold ClockParams at hM
  rcases hfront with hsame | hnext
  · rw [hsame] at herrP
    have hnot : centerRec.tick ≠ M - 1 := by
      intro hlast
      rw [← hM.2] at hlast
      omega
    unfold successor
    rw [if_neg hnot]
    omega
  · rw [← hnext]
    omega

/-- The selected site's new tick still satisfies every adjacent old error's
frozen inequality. -/
theorem selected_tick_le_error_neighbor {m : Nat}
    (B M : Nat) (hM : ClockParams M) (hm : 0 < m)
    (c : Fin m → NativeRecord) (hq : Quiet M hm c)
    (hf : Frozen hm c) (hw : WellFormed M c)
    (i u : Fin m) (delta : Bool)
    (hu : (c u).err = true) (hui : Adjacent hm u i) :
    (activate B M hm c i delta i).tick ≤ (c u).tick + 1 := by
  have holdBound := hf u hu i hui
  cases hi : (c i).err with
  | true =>
      have ha := action_of_error M hm c hq hf i hi
      rcases ha with hclear | hhold
      · rw [activate_self_eq_finish, hclear]
        simpa only [finishNative] using holdBound
      · rw [activate_self_eq_finish, hhold]
        simpa only [finishNative] using holdBound
  | false =>
      have ha := action_of_correct M hm c hq hf i hi
      rcases ha with hinc | hhold
      · have hraw : nativeClock M (c (left hm i)) (c i) (c (right hm i)) =
            ClockAction.inc (successor M (c i).tick) := by
          simpa only [actionAt] using hinc
        have hinfo := action_inc_info M
          (c (left hm i)) (c i) (c (right hm i))
          (successor M (c i).tick) hraw
        have hsym := adjacent_symm hm hui
        have hfront : (c u).tick = (c i).tick ∨
            (c u).tick = successor M (c i).tick := by
          rcases hsym with hleft | hright
          · rw [hleft]
            exact (frontBool_true_iff M (c i).tick (c (left hm i))).1
              (incGuard_front_left M
                (c (left hm i)) (c i) (c (right hm i)) hinfo.2)
          · rw [hright]
            exact (frontBool_true_iff M (c i).tick (c (right hm i))).1
              (incGuard_front_right M
                (c (left hm i)) (c i) (c (right hm i)) hinfo.2)
        have herrP := (hw u).2 hu
        have hs := successor_le_error_neighbor M hM (c u) (c i)
          herrP hfront
        rw [activate_self_eq_finish, hinc]
        simpa only [finishNative] using hs
      · rw [activate_self_eq_finish, hhold]
        simpa only [finishNative] using holdBound

/-- The decoding/range invariant is preserved once Quiet and Frozen hold. -/
theorem wellFormed_preserved {m : Nat} (B M : Nat)
    (hM : ClockParams M) (hm : 0 < m)
    (c : Fin m → NativeRecord) (hq : Quiet M hm c)
    (hf : Frozen hm c) (hw : WellFormed M c)
    (i : Fin m) (delta : Bool) :
    WellFormed M (activate B M hm c i delta) := by
  intro j
  by_cases hji : j = i
  · subst j
    cases hi : (c i).err with
    | true =>
        have ha := action_of_error M hm c hq hf i hi
        rcases ha with hclear | hhold
        · rw [activate_self_eq_finish, hclear]
          change (c i).tick < M ∧
            (false = true → (c i).tick < M / 2)
          constructor
          · exact (hw i).1
          · intro hbad
            cases hbad
        · rw [activate_self_eq_finish, hhold]
          simpa only [finishNative] using hw i
    | false =>
        have ha := action_of_correct M hm c hq hf i hi
        rcases ha with hinc | hhold
        · have hs := successor_lt_modulus M (c i).tick hM (hw i).1
          rw [activate_self_eq_finish, hinc]
          change successor M (c i).tick < M ∧
            (false = true → successor M (c i).tick < M / 2)
          constructor
          · exact hs
          · intro hbad
            cases hbad
        · rw [activate_self_eq_finish, hhold]
          simpa only [finishNative] using hw i
  · rw [activate_other B M hm c i j delta hji]
    exact hw j

/-- Quiet (supplied by the parallel Quiet invariant), Frozen, and Below are
closed under one activation.  This theorem proves the non-Quiet two-thirds of
that conjunction and also carries the decoded range invariant. -/
theorem frozen_preserved {m : Nat} (B M D : Nat)
    (hM : ClockParams M) (hm : 0 < m)
    (c : Fin m → NativeRecord) (hq : Quiet M hm c)
    (hf : Frozen hm c) (hb : Below D c) (hw : WellFormed M c)
    (i : Fin m) (delta : Bool) :
    Frozen hm (activate B M hm c i delta) ∧
      Below D (activate B M hm c i delta) ∧
      WellFormed M (activate B M hm c i delta) := by
  constructor
  · intro u hu v huv
    by_cases hui : u = i
    · subst u
      have hs := activated_error_implies_hold B M hm c hq hf i delta hu
      have heq := activate_of_hold B M hm c i delta hs.1
      rw [heq] at hu ⊢
      exact hf i hs.2 v huv
    · have huold : (c u).err = true := by
        rw [activate_other B M hm c i u delta hui] at hu
        exact hu
      by_cases hvi : v = i
      · subst v
        rw [activate_other B M hm c i u delta hui]
        exact selected_tick_le_error_neighbor B M hM hm c hq hf hw
          i u delta huold huv
      · rw [activate_other B M hm c i u delta hui,
          activate_other B M hm c i v delta hvi]
        exact hf u huold v huv
  · constructor
    · intro u hu
      by_cases hui : u = i
      · subst u
        have hs := activated_error_implies_hold B M hm c hq hf i delta hu
        have heq := activate_of_hold B M hm c i delta hs.1
        rw [heq] at hu ⊢
        exact hb i hs.2
      · rw [activate_other B M hm c i u delta hui] at hu ⊢
        exact hb u hu
    · exact wellFormed_preserved B M hM hm c hq hf hw i delta

/-! ## Establishing Frozen at the common endpoint -/

/-- Numerical witness delivered by a strictly descending error chain to a
base together with the shortest-path caps.  `j ≤ tick_u` is the chain lower
bound, `tick_u ≤ D` is the base-to-site cap, and the last clause is the cap at
each neighbour. -/
def ChainCapWitness {m : Nat} (M D : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) : Prop :=
  ∀ u, (c u).err = true →
    ∃ a j,
      IsBase M (c a) ∧
      j ≤ (c u).tick ∧
      (c u).tick ≤ D ∧
      (∀ v, Adjacent hm u v → (c v).tick ≤ j + 1)

/-- The chain lower bound and all-base shortest-path caps imply Frozen and
Below.  This is the deterministic endpoint implication used after the
all-pairs path comparison. -/
theorem frozen_established {m : Nat} (M D : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord)
    (hcap : ChainCapWitness M D hm c) :
    Frozen hm c ∧ Below D c := by
  constructor
  · intro u hu v huv
    obtain ⟨a, j, hbase, hj, huD, hneigh⟩ := hcap u hu
    have hv := hneigh v huv
    omega
  · intro u hu
    obtain ⟨a, j, hbase, hj, huD, hneigh⟩ := hcap u hu
    omega

end L4.Height.Recover.StageTwo

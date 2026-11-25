import Leader.L4.Height.Core

/-!
# Lifted asynchronous clock and synchronous-level simulation

The literal modulus-four clause in the informal statement is false: at
modulus four, predecessor and successor coincide inside the two-tick upper
window.  Accordingly the invariant below assumes an even modulus whose
half-period is at least three.  This is the regime used by the native
compiler, whose clock modulus is a power of sixteen.
-/

namespace L4.Height

open L4.Compiler.Native

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

variable {m : Nat}

/-- A native configuration together with an unwrapped advance count at every
site. -/
structure WordState (m : Nat) where
  cfg : Fin m → NativeRecord
  lift : Fin m → Nat

/-- Extensionality for lifted word states. -/
theorem wordState_ext {m : Nat} {s t : WordState m}
    (hcfg : s.cfg = t.cfg) (hlift : s.lift = t.lift) : s = t := by
  cases s with
  | mk sc sl =>
    cases t with
    | mk tc tl =>
      cases hcfg
      cases hlift
      rfl

/-- One selected site and the bit offered on that activation. -/
abbrev Activation (m : Nat) := Fin m × Bool

/-- Functional replacement at one site. -/
def setAt {α : Type} {m : Nat} (f : Fin m → α) (i : Fin m) (x : α) :
    Fin m → α :=
  fun j => if j = i then x else f j

@[simp] theorem setAt_self {α : Type} {m : Nat} (f : Fin m → α)
    (i : Fin m) (x : α) :
    setAt f i x i = x := by
  simp [setAt]

@[simp] theorem setAt_other {α : Type} {m : Nat} (f : Fin m → α)
    (i j : Fin m) (x : α) (h : j ≠ i) :
    setAt f i x j = f j := by
  simp [setAt, h]

/-- The physical readout attached to an unwrapped lifted level. -/
def clockOf (M ell : Nat) : Nat :=
  M / 2 + ell % (M / 2)

/-- Exact clock assumptions: an even modulus and a half-period of at least
three. -/
def ClockParams (M : Nat) : Prop :=
  3 ≤ M / 2 ∧ 2 * (M / 2) = M

/-- Literal obstruction to using only `4 ≤ M` and evenness.  Both neighbours
lag the center by one lifted level, but the modulus-four row increments. -/
theorem clock_four_lagging_counterexample :
    nativeClock 4
      ({ tick := 2, err := false, prior := {}, curr := {} } : NativeRecord)
      ({ tick := 3, err := false, prior := {}, curr := {} } : NativeRecord)
      ({ tick := 2, err := false, prior := {}, curr := {} } : NativeRecord) =
        ClockAction.inc 2 := by
  decide

/-- Two natural levels differ by at most one. -/
def Near (a b : Nat) : Prop :=
  a ≤ b + 1 ∧ b ≤ a + 1

/-- Undirected adjacency in the cyclic geometry. -/
def Adjacent {m : Nat} (hm : 0 < m) (i j : Fin m) : Prop :=
  j = left hm i ∨ j = right hm i

@[simp] theorem sync_left_right (hm : 0 < m) (i : Fin m) :
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

@[simp] theorem sync_right_left (hm : 0 < m) (i : Fin m) :
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

theorem adjacent_symm (hm : 0 < m) {i j : Fin m} :
    Adjacent hm i j → Adjacent hm j i := by
  intro h
  rcases h with h | h
  · subst j
    right
    exact (sync_right_left hm i).symm
  · subst j
    left
    exact (sync_left_right hm i).symm

theorem near_symm {a b : Nat} : Near a b → Near b a := by
  intro h
  exact ⟨h.2, h.1⟩

theorem near_cases {a b : Nat} (h : Near a b) :
    b + 1 = a ∨ b = a ∨ b = a + 1 := by
  unfold Near at h
  omega

theorem clockOf_window {M ell : Nat} (hM : ClockParams M) :
    M / 2 ≤ clockOf M ell ∧ clockOf M ell < M := by
  unfold ClockParams at hM
  unfold clockOf
  have hp : 0 < M / 2 := by omega
  have hr := Nat.mod_lt ell hp
  constructor <;> omega

theorem clockOf_succ {M ell : Nat} (hM : ClockParams M) :
    clockOf M (ell + 1) = successor M (clockOf M ell) := by
  unfold ClockParams at hM
  let p := M / 2
  have hp : 3 ≤ p := hM.1
  have hpzero : 0 < p := by omega
  have hpone : 1 < p := by omega
  have hdouble : 2 * p = M := hM.2
  have hr : ell % p < p := Nat.mod_lt _ hpzero
  unfold clockOf
  change p + ((ell + 1) % p) = successor M (p + ell % p)
  rw [Nat.add_mod]
  have hone : 1 % p = 1 := Nat.mod_eq_of_lt hpone
  rw [hone]
  by_cases hlast : ell % p = p - 1
  · have hsum : ell % p + 1 = p := by omega
    rw [hsum, Nat.mod_self]
    have hclock : p + ell % p = M - 1 := by omega
    simp [successor, hclock, p]
  · have hnext : ell % p + 1 < p := by omega
    rw [Nat.mod_eq_of_lt hnext]
    have hnotclock : p + ell % p ≠ M - 1 := by
      intro he
      apply hlast
      omega
    simp [successor, hnotclock, Nat.add_assoc]

theorem successor_ne_self {M t : Nat} (hM : ClockParams M)
    (_ht : M / 2 ≤ t ∧ t < M) :
    successor M t ≠ t := by
  unfold ClockParams at hM
  unfold successor
  by_cases hlast : t = M - 1
  · rw [if_pos hlast]
    intro he
    omega
  · rw [if_neg hlast]
    intro he
    omega

theorem successor_twice_ne_self {M t : Nat} (hM : ClockParams M)
    (_ht : M / 2 ≤ t ∧ t < M) :
    successor M (successor M t) ≠ t := by
  unfold ClockParams at hM
  unfold successor
  by_cases hlast : t = M - 1
  · have hpnot : M / 2 ≠ M - 1 := by
      intro he
      omega
    simp only [if_pos hlast, if_neg hpnot]
    intro he
    omega
  · simp only [if_neg hlast]
    by_cases hnext : t + 1 = M - 1
    · rw [if_pos hnext]
      intro he
      omega
    · rw [if_neg hnext]
      intro he
      omega

/-- The Boolean `atFront` test expressed through lifted levels. -/
def frontBool (M a b : Nat) : Bool :=
  decide (clockOf M b = clockOf M a) ||
    decide (clockOf M b = successor M (clockOf M a))

theorem clock_front_iff {M a b : Nat} (hM : ClockParams M)
    (hne : Near a b) :
    (clockOf M b = clockOf M a ∨
      clockOf M b = successor M (clockOf M a)) ↔
      (b = a ∨ b = a + 1) := by
  rcases near_cases hne with hprev | hsame | hnext
  · have ha : a = b + 1 := by omega
    subst a
    rw [clockOf_succ hM]
    have hw := clockOf_window (M := M) (ell := b) hM
    constructor
    · intro h
      rcases h with h | h
      · exact False.elim ((successor_ne_self hM hw) h.symm)
      · exact False.elim ((successor_twice_ne_self hM hw) h.symm)
    · intro h
      omega
  · subst b
    simp
  · subst b
    rw [clockOf_succ hM]
    simp

theorem frontBool_eq {M a b : Nat} (hM : ClockParams M)
    (hne : Near a b) :
    frontBool M a b = decide (b = a ∨ b = a + 1) := by
  by_cases hgood : b = a ∨ b = a + 1
  · have hfront := (clock_front_iff hM hne).2 hgood
    rcases hfront with h | h
    · simp [frontBool, h, hgood]
    · simp [frontBool, h, hgood]
  · have hnotfront :
        ¬ (clockOf M b = clockOf M a ∨
          clockOf M b = successor M (clockOf M a)) := by
      intro h
      exact hgood ((clock_front_iff hM hne).1 h)
    have hone : clockOf M b ≠ clockOf M a := by
      intro h
      exact hnotfront (Or.inl h)
    have htwo : clockOf M b ≠ successor M (clockOf M a) := by
      intro h
      exact hnotfront (Or.inr h)
    simp [frontBool, hgood, hone, htwo]

/-- The native reset guard is false for two correct lifted ticks within one
level, including the wrap exception. -/
def upperGapBool (M t u : Nat) : Bool :=
  decide (t + 2 ≤ u) &&
    !(decide (t = M / 2) && decide (u = M - 1))

theorem upperGap_near {M a b : Nat} (hM : ClockParams M)
    (hne : Near a b) :
    upperGapBool M (clockOf M a) (clockOf M b) = false := by
  have hparams := hM
  unfold ClockParams at hparams
  rcases near_cases hne with hprev | hsame | hnext
  · have ha : a = b + 1 := by omega
    subst a
    rw [clockOf_succ hM]
    by_cases hlast : clockOf M b = M - 1
    · simp [upperGapBool, successor, hlast]
    · have hgap : ¬ (clockOf M b + 1 + 2 ≤ clockOf M b) := by omega
      simp [upperGapBool, successor, hlast, hgap]
  · subst b
    have hgap : ¬ (clockOf M a + 2 ≤ clockOf M a) := by omega
    simp [upperGapBool, hgap]
  · subst b
    rw [clockOf_succ hM]
    by_cases hlast : clockOf M a = M - 1
    · have hgap : ¬ (M - 1 + 2 ≤ M / 2) := by omega
      simp [upperGapBool, successor, hlast, hgap]
    · have hgap : ¬ (clockOf M a + 2 ≤ clockOf M a + 1) := by omega
      simp [upperGapBool, successor, hlast, hgap]

/-- A legitimate lifted state has no errors, exact clock readouts, and
one-level agreement across every physical edge. -/
def Legit {m : Nat} (M : Nat) (hm : 0 < m) (s : WordState m) : Prop :=
  (∀ i, (s.cfg i).err = false) ∧
  (∀ i, (s.cfg i).tick = clockOf M (s.lift i)) ∧
  (∀ {i j}, Adjacent hm i j → Near (s.lift i) (s.lift j))

/-- Both neighbours lie at the center's present level or its next level. -/
def CanAdvance {m : Nat} (hm : 0 < m) (lift : Fin m → Nat)
    (i : Fin m) : Prop :=
  (lift (left hm i) = lift i ∨ lift (left hm i) = lift i + 1) ∧
  (lift (right hm i) = lift i ∨ lift (right hm i) = lift i + 1)

/-- Boolean classifier for the same two front conditions.  Keeping this
classifier opaque prevents dependent-`ite` elaboration from changing when the
propositional definition is unfolded. -/
def canAdvanceBool {m : Nat} (hm : 0 < m) (lift : Fin m → Nat)
    (i : Fin m) : Bool :=
  decide (lift (left hm i) = lift i ∨ lift (left hm i) = lift i + 1) &&
  decide (lift (right hm i) = lift i ∨ lift (right hm i) = lift i + 1)

theorem canAdvanceBool_eq_true {m : Nat} (hm : 0 < m)
    (lift : Fin m → Nat) (i : Fin m) :
    canAdvanceBool hm lift i = true ↔ CanAdvance hm lift i := by
  unfold canAdvanceBool CanAdvance
  simp

/-- Tick-level form of the native `atFront` guard. -/
def tickFrontBool (M t u : Nat) : Bool :=
  decide (u = t) || decide (u = successor M t)

/-- With clean records and no upper-gap root, the literal native row reduces
to the conjunction of its two front guards. -/
theorem nativeClock_clean (M : Nat)
    (leftRec centerRec rightRec : NativeRecord)
    (hleftErr : leftRec.err = false)
    (hcenterErr : centerRec.err = false)
    (hrightErr : rightRec.err = false)
    (hleftGap : upperGapBool M centerRec.tick leftRec.tick = false)
    (hrightGap : upperGapBool M centerRec.tick rightRec.tick = false) :
    nativeClock M leftRec centerRec rightRec =
      if (tickFrontBool M centerRec.tick leftRec.tick &&
          tickFrontBool M centerRec.tick rightRec.tick) = true then
        ClockAction.inc (successor M centerRec.tick)
      else ClockAction.hold := by
  have hleftNo :
      ¬ (centerRec.tick + 2 ≤ leftRec.tick ∧
        (centerRec.tick ≠ M / 2 ∨ leftRec.tick ≠ M - 1)) := by
    intro hroot
    have htrue : upperGapBool M centerRec.tick leftRec.tick = true := by
      rcases hroot with ⟨hgap, hcenter | hleft⟩
      · simp [upperGapBool, hgap, hcenter]
      · simp [upperGapBool, hgap, hleft]
    rw [hleftGap] at htrue
    cases htrue
  have hrightNo :
      ¬ (centerRec.tick + 2 ≤ rightRec.tick ∧
        (centerRec.tick ≠ M / 2 ∨ rightRec.tick ≠ M - 1)) := by
    intro hroot
    have htrue : upperGapBool M centerRec.tick rightRec.tick = true := by
      rcases hroot with ⟨hgap, hcenter | hright⟩
      · simp [upperGapBool, hgap, hcenter]
      · simp [upperGapBool, hgap, hright]
    rw [hrightGap] at htrue
    cases htrue
  unfold nativeClock tickFrontBool
  simp [hleftErr, hcenterErr, hrightErr, hleftNo, hrightNo]

/-- The native action seen at one selected site. -/
def clockAction {m : Nat} (M : Nat) (hm : 0 < m)
    (s : WordState m) (i : Fin m) : ClockAction :=
  nativeClock M (s.cfg (left hm i)) (s.cfg i) (s.cfg (right hm i))

/-- Increment the lifted counter exactly on a native increment. -/
def advanceLift (act : ClockAction) (ell : Nat) : Nat :=
  match act with
  | .inc _ => ell + 1
  | _ => ell

/-- One asynchronous activation. -/
def activate {m : Nat} (B M : Nat) (hm : 0 < m)
    (s : WordState m) (i : Fin m) (delta : Bool) : WordState m :=
  let act := clockAction M hm s i
  let next := finishNative B (s.cfg (left hm i)) (s.cfg i)
    (s.cfg (right hm i)) act delta
  { cfg := setAt s.cfg i next
    lift := setAt s.lift i (advanceLift act (s.lift i)) }

/-- On a legitimate state the literal native row is exactly the Boolean
front classifier. -/
theorem nativeClock_normal {M : Nat} (hM : ClockParams M)
    (hm : 0 < m) (s : WordState m) (hleg : Legit M hm s) (i : Fin m) :
    clockAction M hm s i =
      if canAdvanceBool hm s.lift i = true then
        ClockAction.inc (clockOf M (s.lift i + 1))
      else ClockAction.hold := by
  rcases hleg with ⟨herr, htick, hnear⟩
  have hnleft : Near (s.lift i) (s.lift (left hm i)) :=
    hnear (i := i) (j := left hm i) (Or.inl rfl)
  have hnright : Near (s.lift i) (s.lift (right hm i)) :=
    hnear (i := i) (j := right hm i) (Or.inr rfl)
  have hupperleft :
      upperGapBool M (s.cfg i).tick (s.cfg (left hm i)).tick = false := by
    rw [htick i, htick (left hm i)]
    exact upperGap_near hM hnleft
  have hupperright :
      upperGapBool M (s.cfg i).tick (s.cfg (right hm i)).tick = false := by
    rw [htick i, htick (right hm i)]
    exact upperGap_near hM hnright
  have hclean := nativeClock_clean M
    (s.cfg (left hm i)) (s.cfg i) (s.cfg (right hm i))
    (herr (left hm i)) (herr i) (herr (right hm i))
    hupperleft hupperright
  change nativeClock M (s.cfg (left hm i)) (s.cfg i)
    (s.cfg (right hm i)) = _
  rw [hclean]
  rw [htick i, htick (left hm i), htick (right hm i)]
  change
    (if (frontBool M (s.lift i) (s.lift (left hm i)) &&
        frontBool M (s.lift i) (s.lift (right hm i))) = true then
      ClockAction.inc (successor M (clockOf M (s.lift i)))
    else ClockAction.hold) =
      (if canAdvanceBool hm s.lift i = true then
        ClockAction.inc (clockOf M (s.lift i + 1))
      else ClockAction.hold)
  rw [frontBool_eq hM hnleft, frontBool_eq hM hnright]
  unfold canAdvanceBool
  rw [← clockOf_succ hM]

/-- Every legitimate activation is either the prescribed increment or a
hold. -/
theorem action_inc_or_hold {M : Nat} (hM : ClockParams M)
    (hm : 0 < m) (s : WordState m) (hleg : Legit M hm s) (i : Fin m) :
    clockAction M hm s i = ClockAction.inc (clockOf M (s.lift i + 1)) ∨
      clockAction M hm s i = ClockAction.hold := by
  rw [nativeClock_normal hM hm s hleg i]
  cases hval : canAdvanceBool hm s.lift i <;> simp [hval]

/-- A legitimate site increments exactly when both neighbours are at its
current or next lifted level. -/
theorem action_inc_iff {M : Nat} (hM : ClockParams M)
    (hm : 0 < m) (s : WordState m) (hleg : Legit M hm s) (i : Fin m) :
    clockAction M hm s i = ClockAction.inc (clockOf M (s.lift i + 1)) ↔
      CanAdvance hm s.lift i := by
  rw [nativeClock_normal hM hm s hleg i]
  cases hval : canAdvanceBool hm s.lift i with
  | false =>
      have hnot : ¬ CanAdvance hm s.lift i := by
        intro hcan
        have hb := (canAdvanceBool_eq_true hm s.lift i).2 hcan
        rw [hval] at hb
        cases hb
      simp [hval, hnot]
  | true =>
      have hyes : CanAdvance hm s.lift i :=
        (canAdvanceBool_eq_true hm s.lift i).1 hval
      simp [hval, hyes]

theorem activate_of_hold {B M : Nat} (hm : 0 < m)
    (s : WordState m) (i : Fin m) (delta : Bool)
    (hact : clockAction M hm s i = ClockAction.hold) :
    activate B M hm s i delta = s := by
  apply wordState_ext
  · funext j
    by_cases hji : j = i
    · subst j
      simp [activate, hact, advanceLift, finishNative]
    · simp [activate, hact, advanceLift, finishNative, hji]
  · funext j
    by_cases hji : j = i
    · subst j
      simp [activate, hact, advanceLift]
    · simp [activate, hact, advanceLift, hji]

/-- Legitimacy is invariant under one asynchronous activation. -/
theorem legit_activate {B M : Nat} (hM : ClockParams M)
    (hm : 0 < m) (s : WordState m) (hleg : Legit M hm s)
    (i : Fin m) (delta : Bool) :
    Legit M hm (activate B M hm s i delta) := by
  have hnormal := nativeClock_normal hM hm s hleg i
  cases hval : canAdvanceBool hm s.lift i with
  | false =>
      have hact : clockAction M hm s i = ClockAction.hold := by
        simpa [hval] using hnormal
      rw [activate_of_hold hm s i delta hact]
      exact hleg
  | true =>
      have hcan : CanAdvance hm s.lift i :=
        (canAdvanceBool_eq_true hm s.lift i).1 hval
      have hact :
          clockAction M hm s i =
            ClockAction.inc (clockOf M (s.lift i + 1)) := by
        simpa [hval] using hnormal
      rcases hleg with ⟨herr, htick, hnear⟩
      have hself :
          (activate B M hm s i delta).lift i = s.lift i + 1 := by
        simp [activate, hact, advanceLift]
      have hother : ∀ j, j ≠ i →
          (activate B M hm s i delta).lift j = s.lift j := by
        intro j hji
        simp [activate, hact, advanceLift, hji]
      have hfront : ∀ {j}, Adjacent hm i j →
          s.lift j = s.lift i ∨ s.lift j = s.lift i + 1 := by
        intro j hj
        rcases hj with hj | hj
        · subst j
          exact hcan.1
        · subst j
          exact hcan.2
      refine ⟨?_, ?_, ?_⟩
      · intro j
        by_cases hji : j = i
        · subst j
          simp [activate, hact, finishNative]
        · simp [activate, hact, finishNative, hji, herr j]
      · intro j
        by_cases hji : j = i
        · subst j
          simp [activate, hact, finishNative, advanceLift]
        · simp [activate, hact, finishNative, advanceLift, hji, htick j]
      · intro a b hab
        by_cases hai : a = i
        · subst a
          by_cases hbi : b = i
          · subst b
            rw [hself]
            unfold Near
            omega
          · rw [hself, hother b hbi]
            rcases hfront hab with h | h
            · unfold Near
              omega
            · unfold Near
              omega
        · by_cases hbi : b = i
          · subst b
            rw [hother a hai, hself]
            have hs := adjacent_symm hm hab
            rcases hfront hs with h | h
            · unfold Near
              omega
            · unfold Near
              omega
          · rw [hother a hai, hother b hbi]
            exact hnear hab

/-- Execute a finite activation history, first list element first. -/
def syncRun {m : Nat} (B M : Nat) (hm : 0 < m) :
    List (Activation m) → WordState m → WordState m
  | [], s => s
  | e :: h, s => syncRun B M hm h (activate B M hm s e.1 e.2)

theorem syncRun_legit {B M : Nat} (hM : ClockParams M)
    (hm : 0 < m) (h : List (Activation m)) (s : WordState m)
    (hleg : Legit M hm s) :
    Legit M hm (syncRun B M hm h s) := by
  induction h generalizing s with
  | nil => exact hleg
  | cons e h ih =>
      exact ih (activate B M hm s e.1 e.2)
        (legit_activate hM hm s hleg e.1 e.2)

/-- Only phase one can inspect the activation bit. -/
theorem phaseUpdate_delta_irrelevant (B phase : Nat)
    (leftSnap centerSnap rightSnap : Snapshot) (delta delta' : Bool)
    (hphase : phase ≠ 1) :
    phaseUpdate B phase leftSnap centerSnap rightSnap delta =
      phaseUpdate B phase leftSnap centerSnap rightSnap delta' := by
  cases phase with
  | zero => rfl
  | succ phase =>
    cases phase with
    | zero => exact False.elim (hphase rfl)
    | succ phase =>
      cases phase with
      | zero => rfl
      | succ phase =>
        cases phase with
        | zero => rfl
        | succ phase =>
          cases phase with
          | zero => rfl
          | succ phase =>
            cases phase with
            | zero => rfl
            | succ phase => rfl

/-- Synchronous snapshots indexed by the unwrapped level offset. -/
def syncLevels {m : Nat} (B M ellzero : Nat) (hm : 0 < m)
    (choices : Nat → Fin m → Bool) (start : Fin m → Snapshot) :
    Nat → Fin m → Snapshot
  | 0 => start
  | n + 1 =>
      phaseStep B (clockOf M (ellzero + n) % 32) hm
        (choices (ellzero + n))
        (syncLevels B M ellzero hm choices start n)

/-- A physical state represents the synchronous table at each site's current
lift.  Its prior snapshot represents the immediately preceding level whenever
that preceding level is at or above the common starting level. -/
def Represents {m : Nat} (B M ellzero : Nat) (hm : 0 < m)
    (choices : Nat → Fin m → Bool) (start : Fin m → Snapshot)
    (s : WordState m) : Prop :=
  (∀ i, ellzero ≤ s.lift i) ∧
  (∀ i, (s.cfg i).curr =
    syncLevels B M ellzero hm choices start (s.lift i - ellzero) i) ∧
  (∀ i, ellzero < s.lift i →
    (s.cfg i).prior =
      syncLevels B M ellzero hm choices start
        (s.lift i - ellzero - 1) i)

/-- The warm start condition allowed by the level comparison. -/
def StartConsistent {m : Nat} (B M ellzero : Nat) (hm : 0 < m)
    (choices : Nat → Fin m → Bool) (start : Fin m → Snapshot)
    (s : WordState m) : Prop :=
  ∀ i,
    (s.lift i = ellzero ∧ (s.cfg i).curr = start i) ∨
    (s.lift i = ellzero + 1 ∧ (s.cfg i).prior = start i ∧
      (s.cfg i).curr =
        syncLevels B M ellzero hm choices start 1 i)

theorem startConsistent_represents {B M ellzero : Nat} (hm : 0 < m)
    (choices : Nat → Fin m → Bool) (start : Fin m → Snapshot)
    (s : WordState m)
    (hstart : StartConsistent B M ellzero hm choices start s) :
    Represents B M ellzero hm choices start s := by
  unfold Represents
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rcases hstart i with h | h
    · omega
    · omega
  · intro i
    rcases hstart i with h | h
    · rcases h with ⟨hlift, hcurr⟩
      have hoff : s.lift i - ellzero = 0 := by omega
      rw [hoff]
      simpa [syncLevels] using hcurr
    · rcases h with ⟨hlift, hprior, hcurr⟩
      have hoff : s.lift i - ellzero = 1 := by omega
      rw [hoff]
      exact hcurr
  · intro i hpos
    rcases hstart i with h | h
    · omega
    · rcases h with ⟨hlift, hprior, hcurr⟩
      have hoff : s.lift i - ellzero - 1 = 0 := by omega
      rw [hoff]
      simpa [syncLevels] using hprior

/-- A history supplies the indexed bit at every phase-one increment.  Bits on
all other phases are intentionally unconstrained. -/
def Honors {m : Nat} (B M : Nat) (hm : 0 < m)
    (choices : Nat → Fin m → Bool) :
    WordState m → List (Activation m) → Prop
  | _, [] => True
  | s, e :: h =>
      (match clockAction M hm s e.1 with
       | .inc _ =>
           clockOf M (s.lift e.1) % 32 ≠ 1 ∨
             e.2 = choices (s.lift e.1) e.1
       | _ => True) ∧
      Honors B M hm choices (activate B M hm s e.1 e.2) h

/-- At an increment, `neighborView` returns the synchronous snapshot at the
center's predecessor level, whether the neighbor is at that level (`curr`) or
one level ahead (`prior`). -/
theorem neighborView_level {B M ellzero : Nat} (hM : ClockParams M)
    (hm : 0 < m) (choices : Nat → Fin m → Bool)
    (start : Fin m → Snapshot) (s : WordState m)
    (hleg : Legit M hm s)
    (hrep : Represents B M ellzero hm choices start s)
    (i j : Fin m) (n : Nat)
    (hilevel : s.lift i = ellzero + n)
    (hfront : s.lift j = s.lift i ∨ s.lift j = s.lift i + 1) :
    neighborView (s.cfg i).tick (s.cfg j) =
      syncLevels B M ellzero hm choices start n j := by
  rcases hleg with ⟨herr, htick, hnear⟩
  rcases hrep with ⟨hlower, hcurr, hprior⟩
  rcases hfront with hsame | hahead
  · have hticksame : (s.cfg j).tick = (s.cfg i).tick := by
      rw [htick j, htick i, hsame]
    have hoff : s.lift j - ellzero = n := by omega
    simp [neighborView, hticksame, hcurr j, hoff]
  · have htickahead :
        (s.cfg j).tick = successor M (s.cfg i).tick := by
      rw [htick j, htick i, hahead, clockOf_succ hM]
    have hwindowTick :
        M / 2 ≤ (s.cfg i).tick ∧ (s.cfg i).tick < M := by
      rw [htick i]
      exact clockOf_window (M := M) (ell := s.lift i) hM
    have hne : (s.cfg j).tick ≠ (s.cfg i).tick := by
      rw [htickahead]
      exact successor_ne_self hM hwindowTick
    have hbasej : ellzero ≤ s.lift j := hlower j
    have hpos : ellzero < s.lift j := by omega
    have hoff : s.lift j - ellzero - 1 = n := by omega
    simp [neighborView, hne, hprior j hpos, hoff]

/-- One legitimate activation preserves the synchronous representation. -/
theorem represents_activate {B M ellzero : Nat} (hM : ClockParams M)
    (hm : 0 < m) (choices : Nat → Fin m → Bool)
    (start : Fin m → Snapshot) (s : WordState m)
    (hleg : Legit M hm s)
    (hrep : Represents B M ellzero hm choices start s)
    (i : Fin m) (delta : Bool)
    (hchoice :
      match clockAction M hm s i with
      | .inc _ =>
          clockOf M (s.lift i) % 32 ≠ 1 ∨
            delta = choices (s.lift i) i
      | _ => True) :
    Represents B M ellzero hm choices start
      (activate B M hm s i delta) := by
  have hnormal := nativeClock_normal hM hm s hleg i
  cases hval : canAdvanceBool hm s.lift i with
  | false =>
      have hact : clockAction M hm s i = ClockAction.hold := by
        simpa [hval] using hnormal
      rw [activate_of_hold hm s i delta hact]
      exact hrep
  | true =>
      have hcan : CanAdvance hm s.lift i :=
        (canAdvanceBool_eq_true hm s.lift i).1 hval
      have hact :
          clockAction M hm s i =
            ClockAction.inc (clockOf M (s.lift i + 1)) := by
        simpa [hval] using hnormal
      have hchoiceInc :
          clockOf M (s.lift i) % 32 ≠ 1 ∨
            delta = choices (s.lift i) i := by
        simpa [hact] using hchoice
      rcases hrep with ⟨hlower, hcurr, hprior⟩
      let n := s.lift i - ellzero
      have hbase : ellzero ≤ s.lift i := hlower i
      have hilevel : s.lift i = ellzero + n := by
        dsimp [n]
        omega
      have hcenter :
          (s.cfg i).curr =
            syncLevels B M ellzero hm choices start n i := by
        have hoff : s.lift i - ellzero = n := rfl
        simpa [hoff] using hcurr i
      have hleft := neighborView_level hM hm choices start s hleg
        ⟨hlower, hcurr, hprior⟩ i (left hm i) n hilevel hcan.1
      have hright := neighborView_level hM hm choices start s hleg
        ⟨hlower, hcurr, hprior⟩ i (right hm i) n hilevel hcan.2
      have hphaseChoice :
          phaseUpdate B ((s.cfg i).tick % 32)
              (neighborView (s.cfg i).tick (s.cfg (left hm i)))
              (s.cfg i).curr
              (neighborView (s.cfg i).tick (s.cfg (right hm i))) delta =
          phaseUpdate B ((s.cfg i).tick % 32)
              (neighborView (s.cfg i).tick (s.cfg (left hm i)))
              (s.cfg i).curr
              (neighborView (s.cfg i).tick (s.cfg (right hm i)))
              (choices (s.lift i) i) := by
        rcases hchoiceInc with hphase | hdelta
        · apply phaseUpdate_delta_irrelevant
          rw [hleg.2.1 i]
          exact hphase
        · rw [hdelta]
      have hnewcurr :
          ((activate B M hm s i delta).cfg i).curr =
            syncLevels B M ellzero hm choices start (n + 1) i := by
        calc
          ((activate B M hm s i delta).cfg i).curr =
              phaseUpdate B ((s.cfg i).tick % 32)
                (neighborView (s.cfg i).tick (s.cfg (left hm i)))
                (s.cfg i).curr
                (neighborView (s.cfg i).tick (s.cfg (right hm i))) delta := by
                  simp [activate, hact, finishNative]
          _ = phaseUpdate B ((s.cfg i).tick % 32)
                (neighborView (s.cfg i).tick (s.cfg (left hm i)))
                (s.cfg i).curr
                (neighborView (s.cfg i).tick (s.cfg (right hm i)))
                (choices (s.lift i) i) := hphaseChoice
          _ = syncLevels B M ellzero hm choices start (n + 1) i := by
                rw [hleft, hcenter, hright, hleg.2.1 i, hilevel]
                simp [syncLevels, phaseStep]
      have hnewprior :
          ((activate B M hm s i delta).cfg i).prior =
            syncLevels B M ellzero hm choices start n i := by
        calc
          ((activate B M hm s i delta).cfg i).prior = (s.cfg i).curr := by
            simp [activate, hact, finishNative]
          _ = syncLevels B M ellzero hm choices start n i := hcenter
      have hnewlift :
          (activate B M hm s i delta).lift i = s.lift i + 1 := by
        simp [activate, hact, advanceLift]
      unfold Represents
      refine ⟨?_, ?_, ?_⟩
      · intro j
        by_cases hji : j = i
        · subst j
          rw [hnewlift]
          omega
        · simp [activate, hact, advanceLift, hji]
          exact hlower j
      · intro j
        by_cases hji : j = i
        · subst j
          rw [hnewlift]
          have hoff : s.lift i + 1 - ellzero = n + 1 := by omega
          rw [hoff]
          exact hnewcurr
        · simp [activate, hact, advanceLift, hji]
          exact hcurr j
      · intro j hpos
        by_cases hji : j = i
        · subst j
          rw [hnewlift] at hpos ⊢
          have hoff : s.lift i + 1 - ellzero - 1 = n := by omega
          rw [hoff]
          exact hnewprior
        · simp [activate, hact, advanceLift, hji] at hpos ⊢
          exact hprior j hpos

/-- Representation is preserved through a whole honored history. -/
theorem syncRun_represents {B M ellzero : Nat} (hM : ClockParams M)
    (hm : 0 < m) (choices : Nat → Fin m → Bool)
    (start : Fin m → Snapshot) (h : List (Activation m))
    (s : WordState m) (hleg : Legit M hm s)
    (hrep : Represents B M ellzero hm choices start s)
    (hhonor : Honors B M hm choices s h) :
    Represents B M ellzero hm choices start (syncRun B M hm h s) := by
  induction h generalizing s with
  | nil => exact hrep
  | cons e h ih =>
      change
        (match clockAction M hm s e.1 with
         | .inc _ =>
             clockOf M (s.lift e.1) % 32 ≠ 1 ∨
               e.2 = choices (s.lift e.1) e.1
         | _ => True) ∧
        Honors B M hm choices (activate B M hm s e.1 e.2) h at hhonor
      rcases hhonor with ⟨hhead, htail⟩
      exact ih (activate B M hm s e.1 e.2)
        (legit_activate hM hm s hleg e.1 e.2)
        (represents_activate hM hm choices start s hleg hrep e.1 e.2 hhead)
        htail

/-- The first current snapshot observed at a requested lifted level.  The
final state is inspected as well. -/
def levelCurr {m : Nat} (B M : Nat) (hm : 0 < m) :
    List (Activation m) → WordState m → Fin m → Nat → Option Snapshot
  | [], s, i, ell =>
      if s.lift i = ell then some (s.cfg i).curr else none
  | e :: h, s, i, ell =>
      if s.lift i = ell then some (s.cfg i).curr
      else levelCurr B M hm h (activate B M hm s e.1 e.2) i ell

/-- The bit on the first actual increment of `i` out of level `ell`. -/
def levelBit {m : Nat} (B M : Nat) (hm : 0 < m) :
    List (Activation m) → WordState m → Fin m → Nat → Option Bool
  | [], _, _, _ => none
  | e :: h, s, i, ell =>
      if e.1 = i then
        if s.lift i = ell then
          match clockAction M hm s e.1 with
          | .inc _ => some e.2
          | _ => levelBit B M hm h
              (activate B M hm s e.1 e.2) i ell
        else levelBit B M hm h
          (activate B M hm s e.1 e.2) i ell
      else levelBit B M hm h
        (activate B M hm s e.1 e.2) i ell

/-- Every observed level snapshot equals its synchronous table entry. -/
theorem levelCurr_eq_sync {B M ellzero : Nat} (hM : ClockParams M)
    (hm : 0 < m) (choices : Nat → Fin m → Bool)
    (start : Fin m → Snapshot) (h : List (Activation m))
    (s : WordState m) (hleg : Legit M hm s)
    (hrep : Represents B M ellzero hm choices start s)
    (hhonor : Honors B M hm choices s h)
    (i : Fin m) (n : Nat) (value : Snapshot)
    (hvalue : levelCurr B M hm h s i (ellzero + n) = some value) :
    value = syncLevels B M ellzero hm choices start n i := by
  induction h generalizing s with
  | nil =>
      by_cases heq : s.lift i = ellzero + n
      · have hsome : some (s.cfg i).curr = some value := by
          simpa [levelCurr, heq] using hvalue
        cases hsome
        have hoff : s.lift i - ellzero = n := by omega
        simpa [hoff] using hrep.2.1 i
      · simp [levelCurr, heq] at hvalue
  | cons e h ih =>
      by_cases heq : s.lift i = ellzero + n
      · have hsome : some (s.cfg i).curr = some value := by
          simpa [levelCurr, heq] using hvalue
        cases hsome
        have hoff : s.lift i - ellzero = n := by omega
        simpa [hoff] using hrep.2.1 i
      · change
          (match clockAction M hm s e.1 with
           | .inc _ =>
               clockOf M (s.lift e.1) % 32 ≠ 1 ∨
                 e.2 = choices (s.lift e.1) e.1
           | _ => True) ∧
          Honors B M hm choices (activate B M hm s e.1 e.2) h at hhonor
        rcases hhonor with ⟨hhead, htail⟩
        have hnext :
            levelCurr B M hm h (activate B M hm s e.1 e.2) i
              (ellzero + n) = some value := by
          simpa [levelCurr, heq] using hvalue
        exact ih (activate B M hm s e.1 e.2)
          (legit_activate hM hm s hleg e.1 e.2)
          (represents_activate hM hm choices start s hleg hrep e.1 e.2 hhead)
          htail hnext

/-- At phase one the first increment bit is exactly the indexed choice. -/
theorem levelBit_choice_at_phase_one {B M : Nat} (hm : 0 < m)
    (choices : Nat → Fin m → Bool) (h : List (Activation m))
    (s : WordState m) (hhonor : Honors B M hm choices s h)
    (i : Fin m) (ell : Nat) (delta : Bool)
    (hphase : clockOf M ell % 32 = 1)
    (hbit : levelBit B M hm h s i ell = some delta) :
    delta = choices ell i := by
  induction h generalizing s with
  | nil => simp [levelBit] at hbit
  | cons e h ih =>
      rcases e with ⟨j, bit⟩
      change
        (match clockAction M hm s j with
         | .inc _ =>
             clockOf M (s.lift j) % 32 ≠ 1 ∨
               bit = choices (s.lift j) j
         | _ => True) ∧
        Honors B M hm choices (activate B M hm s j bit) h at hhonor
      rcases hhonor with ⟨hhead, htail⟩
      by_cases hji : j = i
      · subst j
        by_cases hlift : s.lift i = ell
        · cases hact : clockAction M hm s i with
          | inc tick =>
              have hchoice :
                  clockOf M (s.lift i) % 32 ≠ 1 ∨
                    bit = choices (s.lift i) i := by
                simpa [hact] using hhead
              have hbitchoice : bit = choices ell i := by
                rcases hchoice with hne | heq
                · exfalso
                  apply hne
                  simpa [hlift] using hphase
                · simpa [hlift] using heq
              have hsome : some bit = some delta := by
                simpa [levelBit, hlift, hact] using hbit
              cases hsome
              exact hbitchoice
          | reset =>
              have hnext :
                  levelBit B M hm h (activate B M hm s i bit) i ell =
                    some delta := by
                simpa [levelBit, hlift, hact] using hbit
              exact ih (activate B M hm s i bit) htail hnext
          | propagate tick =>
              have hnext :
                  levelBit B M hm h (activate B M hm s i bit) i ell =
                    some delta := by
                simpa [levelBit, hlift, hact] using hbit
              exact ih (activate B M hm s i bit) htail hnext
          | clear =>
              have hnext :
                  levelBit B M hm h (activate B M hm s i bit) i ell =
                    some delta := by
                simpa [levelBit, hlift, hact] using hbit
              exact ih (activate B M hm s i bit) htail hnext
          | hold =>
              have hnext :
                  levelBit B M hm h (activate B M hm s i bit) i ell =
                    some delta := by
                simpa [levelBit, hlift, hact] using hbit
              exact ih (activate B M hm s i bit) htail hnext
        · have hnext :
              levelBit B M hm h (activate B M hm s i bit) i ell =
                some delta := by
            simpa [levelBit, hlift] using hbit
          exact ih (activate B M hm s i bit) htail hnext
      · have hnext :
            levelBit B M hm h (activate B M hm s j bit) i ell =
              some delta := by
          simpa [levelBit, hji] using hbit
        exact ih (activate B M hm s j bit) htail hnext

/-- Every actually observed successor-level snapshot is the synchronous
phase update of the three predecessor-level snapshots, using the bit on that
site's actual advance. -/
theorem levelCurr_successor_simulation {B M ellzero : Nat}
    (hM : ClockParams M) (hm : 0 < m)
    (choices : Nat → Fin m → Bool) (start : Fin m → Snapshot)
    (h : List (Activation m)) (s : WordState m)
    (hleg : Legit M hm s)
    (hrep : Represents B M ellzero hm choices start s)
    (hhonor : Honors B M hm choices s h)
    (i : Fin m) (n : Nat)
    (leftValue centerValue rightValue nextValue : Snapshot)
    (delta : Bool)
    (hleft : levelCurr B M hm h s (left hm i) (ellzero + n) =
      some leftValue)
    (hcenter : levelCurr B M hm h s i (ellzero + n) =
      some centerValue)
    (hright : levelCurr B M hm h s (right hm i) (ellzero + n) =
      some rightValue)
    (hnext : levelCurr B M hm h s i (ellzero + n + 1) =
      some nextValue)
    (hbit : levelBit B M hm h s i (ellzero + n) = some delta) :
    nextValue =
      phaseUpdate B (clockOf M (ellzero + n) % 32)
        leftValue centerValue rightValue delta := by
  have hleftEq := levelCurr_eq_sync hM hm choices start h s hleg hrep
    hhonor (left hm i) n leftValue hleft
  have hcenterEq := levelCurr_eq_sync hM hm choices start h s hleg hrep
    hhonor i n centerValue hcenter
  have hrightEq := levelCurr_eq_sync hM hm choices start h s hleg hrep
    hhonor (right hm i) n rightValue hright
  have hnextEq := levelCurr_eq_sync hM hm choices start h s hleg hrep
    hhonor i (n + 1) nextValue (by simpa [Nat.add_assoc] using hnext)
  rw [hnextEq, hleftEq, hcenterEq, hrightEq]
  simp only [syncLevels, phaseStep]
  by_cases hphase : clockOf M (ellzero + n) % 32 = 1
  · have hdelta := levelBit_choice_at_phase_one hm choices h s hhonor i
      (ellzero + n) delta hphase hbit
    rw [hdelta]
  · exact phaseUpdate_delta_irrelevant B
      (clockOf M (ellzero + n) % 32)
      (syncLevels B M ellzero hm choices start n (left hm i))
      (syncLevels B M ellzero hm choices start n i)
      (syncLevels B M ellzero hm choices start n (right hm i))
      (choices (ellzero + n) i) delta hphase

#print axioms L4.Height.clock_four_lagging_counterexample
#print axioms L4.Height.nativeClock_normal
#print axioms L4.Height.legit_activate
#print axioms L4.Height.levelCurr_successor_simulation

end L4.Height

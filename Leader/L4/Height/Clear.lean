import Leader.L4.Compiler.NativeSpec
import Leader.L4.Height.Core

namespace L4.Height.Recover.StageThree

open L4.Compiler.Native
open L4.Height

set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

/-- A native clock configuration on the cyclic set of sites. -/
abbrev ClockConfig (m : Nat) := Fin m → NativeRecord

/-- The paper's signed clock value. Both correct and erroneous native ticks
use the same affine decoding; the error bit affects guards, not this value. -/
def signedVal (M : Nat) (r : NativeRecord) : Int :=
  Int.ofNat r.tick - Int.ofNat (M / 2)

/-- The native decoded range used by the paper proof: the modulus is even,
all ticks are native residues, and erroneous ticks lie below `P = M/2`. -/
def ClockDomain {m : Nat} (M : Nat) (s : ClockConfig m) : Prop :=
  4 ≤ M ∧ M % 2 = 0 ∧
    ∀ i, (s i).tick < M ∧
      ((s i).err = true → (s i).tick < M / 2)

/-- Literal Boolean abbreviations from `nativeClock`. -/
def lowerErrB (t : Nat) (y : NativeRecord) : Bool :=
  y.err && decide (y.tick < t)

def upperGapB (M t : Nat) (y : NativeRecord) : Bool :=
  decide (t + 2 ≤ y.tick) &&
    (!(decide (t = M / 2) && decide (y.tick = M - 1)))

def rootB (M : Nat) (left center right : NativeRecord) : Bool :=
  if center.err then
    (!(lowerErrB center.tick left || lowerErrB center.tick right))
  else
    upperGapB M center.tick left || upperGapB M center.tick right

def proposalTick (M t : Nat) (y : NativeRecord) : Nat :=
  if y.err && decide (y.tick + 1 < M / 2) &&
      decide (y.tick + 1 < t) then
    y.tick + 1
  else t

def nearB (t : Nat) (y : NativeRecord) : Bool :=
  decide (y.tick ≤ t + 1) && decide (t ≤ y.tick + 1) &&
    (decide (y.tick ≤ t) || (!(y.err)))

def atFrontB (M t : Nat) (y : NativeRecord) : Bool :=
  decide (y.tick = t) || decide (y.tick = successor M t)

/-- Literal round-QUIET predicate: every current root is an erroneous base
record, equivalently an error at signed value `-P`. -/
def Quiet {m : Nat} (M : Nat) (hm : 0 < m)
    (s : ClockConfig m) : Prop :=
  ∀ i,
    rootB M (s (left hm i)) (s i) (s (right hm i)) = true →
      (s i).err = true ∧
        signedVal M (s i) = -(Int.ofNat (M / 2))

/-- Literal round-FROZEN predicate. Every erroneous site upper-bounds both
neighbours by one signed unit, and lies strictly below `-P + D + 1`. -/
def Frozen {m : Nat} (M D : Nat) (hm : 0 < m)
    (s : ClockConfig m) : Prop :=
  ∀ i, (s i).err = true →
    signedVal M (s (left hm i)) ≤ signedVal M (s i) + 1 ∧
    signedVal M (s (right hm i)) ≤ signedVal M (s i) + 1 ∧
    signedVal M (s i) <
      -(Int.ofNat (M / 2)) + Int.ofNat D + 1

/-! ## Elementary cycle identities -/

private theorem left_right_cycle {m : Nat} (hm : 0 < m) (i : Fin m) :
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

private theorem right_left_cycle {m : Nat} (hm : 0 < m) (i : Fin m) :
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

/-! ## The native action after the quiet/frozen cut -/

private theorem nativeClock_helpers (M : Nat)
    (l c r : NativeRecord) :
    nativeClock M l c r =
      if rootB M l c r &&
          (!(c.err && decide (c.tick = 0))) then
        .reset
      else if min (proposalTick M c.tick l)
          (proposalTick M c.tick r) < c.tick then
        .propagate
          (min (proposalTick M c.tick l)
            (proposalTick M c.tick r))
      else if c.err && nearB c.tick l && nearB c.tick r then
        .clear
      else if (!(c.err)) && atFrontB M c.tick l &&
          atFrontB M c.tick r then
        .inc (successor M c.tick)
      else .hold := by
  rfl

private theorem reset_guard_false {m M : Nat} (hm : 0 < m)
    (s : ClockConfig m) (i : Fin m)
    (hquiet : Quiet M hm s) :
    (rootB M (s (left hm i)) (s i) (s (right hm i)) &&
      (!((s i).err && decide ((s i).tick = 0)))) = false := by
  by_cases hroot :
      rootB M (s (left hm i)) (s i) (s (right hm i)) = true
  · have hq := hquiet i hroot
    have hv := hq.2
    simp only [signedVal, Int.ofNat_eq_natCast] at hv
    have htick : (s i).tick = 0 := by omega
    simp [hroot, hq.1, htick]
  · have hrootFalse :
        rootB M (s (left hm i)) (s i) (s (right hm i)) = false := by
      cases hval :
          rootB M (s (left hm i)) (s i) (s (right hm i)) with
      | false => rfl
      | true => exact False.elim (hroot hval)
    rw [hrootFalse]
    rfl

private theorem proposal_left_eq {m M D : Nat} (hm : 0 < m)
    (s : ClockConfig m) (i : Fin m)
    (hfrozen : Frozen M D hm s) :
    proposalTick M (s i).tick (s (left hm i)) = (s i).tick := by
  unfold proposalTick
  split
  next hcond =>
    have hout := Bool.and_eq_true_iff.mp hcond
    have hin := Bool.and_eq_true_iff.mp hout.1
    have herr : (s (left hm i)).err = true := hin.1
    have hp : (s (left hm i)).tick + 1 < M / 2 :=
      of_decide_eq_true hin.2
    have hstrict : (s (left hm i)).tick + 1 < (s i).tick :=
      of_decide_eq_true hout.2
    have hb := (hfrozen (left hm i) herr).2.1
    rw [right_left_cycle hm i] at hb
    simp only [signedVal, Int.ofNat_eq_natCast] at hb
    omega
  next _ => rfl

private theorem proposal_right_eq {m M D : Nat} (hm : 0 < m)
    (s : ClockConfig m) (i : Fin m)
    (hfrozen : Frozen M D hm s) :
    proposalTick M (s i).tick (s (right hm i)) = (s i).tick := by
  unfold proposalTick
  split
  next hcond =>
    have hout := Bool.and_eq_true_iff.mp hcond
    have hin := Bool.and_eq_true_iff.mp hout.1
    have herr : (s (right hm i)).err = true := hin.1
    have hp : (s (right hm i)).tick + 1 < M / 2 :=
      of_decide_eq_true hin.2
    have hstrict : (s (right hm i)).tick + 1 < (s i).tick :=
      of_decide_eq_true hout.2
    have hb := (hfrozen (right hm i) herr).1
    rw [left_right_cycle hm i] at hb
    simp only [signedVal, Int.ofNat_eq_natCast] at hb
    omega
  next _ => rfl

/-- Quietness removes reset and Frozen removes every strict proposal. -/
private theorem native_action_reduced {m M D : Nat} (hm : 0 < m)
    (s : ClockConfig m) (i : Fin m)
    (hquiet : Quiet M hm s) (hfrozen : Frozen M D hm s) :
    nativeClock M (s (left hm i)) (s i) (s (right hm i)) =
      if (s i).err && nearB (s i).tick (s (left hm i)) &&
          nearB (s i).tick (s (right hm i)) then
        .clear
      else if (!((s i).err)) &&
          atFrontB M (s i).tick (s (left hm i)) &&
          atFrontB M (s i).tick (s (right hm i)) then
        .inc (successor M (s i).tick)
      else .hold := by
  rw [nativeClock_helpers]
  have hg := reset_guard_false hm s i hquiet
  have hl := proposal_left_eq hm s i hfrozen
  have hr := proposal_right_eq hm s i hfrozen
  rw [hg, hl, hr]
  simp

/-! ## One activation and activation sequences -/

/-- One asynchronous activation of one native clock record. -/
def activate {m : Nat} (B M : Nat) (hm : 0 < m)
    (s : ClockConfig m) (owner : Fin m) (delta : Bool) :
    ClockConfig m :=
  fun j =>
    if j = owner then
      finishNative B (s (left hm owner)) (s owner) (s (right hm owner))
        (nativeClock M (s (left hm owner)) (s owner)
          (s (right hm owner))) delta
    else s j

@[simp] theorem activate_owner {m : Nat} (B M : Nat) (hm : 0 < m)
    (s : ClockConfig m) (owner : Fin m) (delta : Bool) :
    activate B M hm s owner delta owner =
      finishNative B (s (left hm owner)) (s owner) (s (right hm owner))
        (nativeClock M (s (left hm owner)) (s owner)
          (s (right hm owner))) delta := by
  simp [activate]

theorem activate_other {m : Nat} (B M : Nat) (hm : 0 < m)
    (s : ClockConfig m) (owner j : Fin m) (delta : Bool)
    (hne : j ≠ owner) :
    activate B M hm s owner delta j = s j := by
  simp [activate, hne]

private theorem center_error_monotone {m M D B : Nat} (hm : 0 < m)
    (s : ClockConfig m) (i : Fin m) (delta : Bool)
    (hquiet : Quiet M hm s) (hfrozen : Frozen M D hm s)
    (hpost :
      (finishNative B (s (left hm i)) (s i) (s (right hm i))
        (nativeClock M (s (left hm i)) (s i) (s (right hm i)))
        delta).err = true) :
    (s i).err = true ∧
      signedVal M
          (finishNative B (s (left hm i)) (s i) (s (right hm i))
            (nativeClock M (s (left hm i)) (s i) (s (right hm i)))
            delta) =
        signedVal M (s i) := by
  have ha := native_action_reduced hm s i hquiet hfrozen
  by_cases hclear :
      ((s i).err && nearB (s i).tick (s (left hm i)) &&
        nearB (s i).tick (s (right hm i))) = true
  · have hact :
        nativeClock M (s (left hm i)) (s i) (s (right hm i)) =
          .clear := by
      rw [ha]
      simp [hclear]
    rw [hact] at hpost
    simp [finishNative] at hpost
  · by_cases hinc :
      ((!((s i).err)) && atFrontB M (s i).tick (s (left hm i)) &&
        atFrontB M (s i).tick (s (right hm i))) = true
    · have hact :
          nativeClock M (s (left hm i)) (s i) (s (right hm i)) =
            .inc (successor M (s i).tick) := by
        rw [ha]
        simp [hclear, hinc]
      rw [hact] at hpost
      simp [finishNative] at hpost
    · have hact :
          nativeClock M (s (left hm i)) (s i) (s (right hm i)) =
            .hold := by
        rw [ha]
        simp [hclear, hinc]
      rw [hact] at hpost ⊢
      have herr : (s i).err = true := by
        simpa [finishNative] using hpost
      exact ⟨herr, rfl⟩

/-- Errors only disappear. Every error surviving one activation was already
an error and has exactly its old signed value. -/
theorem error_monotone {m M D B : Nat} (hm : 0 < m)
    (s : ClockConfig m) (owner : Fin m) (delta : Bool)
    (hquiet : Quiet M hm s) (hfrozen : Frozen M D hm s)
    (j : Fin m)
    (hpost : (activate B M hm s owner delta j).err = true) :
    (s j).err = true ∧
      signedVal M (activate B M hm s owner delta j) =
        signedVal M (s j) := by
  by_cases hjo : j = owner
  · subst j
    rw [activate_owner] at hpost ⊢
    exact center_error_monotone hm s owner delta hquiet hfrozen hpost
  · rw [activate_other B M hm s owner j delta hjo] at hpost ⊢
    exact ⟨hpost, rfl⟩

abbrev Activation (m : Nat) := Fin m × Bool

/-- Execute a finite asynchronous activation sequence. -/
def runActivations {m : Nat} (B M : Nat) (hm : 0 < m) :
    ClockConfig m → List (Activation m) → ClockConfig m
  | s, [] => s
  | s, a :: rest =>
      runActivations B M hm (activate B M hm s a.1 a.2) rest

/-- Quiet and Frozen are assumed at every pre-activation state, exactly as
in the post-cut induction of the paper. -/
def StableTrace {m : Nat} (B M D : Nat) (hm : 0 < m) :
    ClockConfig m → List (Activation m) → Prop
  | _, [] => True
  | s, a :: rest =>
      Quiet M hm s ∧ Frozen M D hm s ∧
        StableTrace B M D hm
          (activate B M hm s a.1 a.2) rest

/-- Sequence form of `error_monotone`. -/
theorem error_monotone_run {m M D B : Nat} (hm : 0 < m) :
    ∀ (s : ClockConfig m) (acts : List (Activation m)),
      StableTrace B M D hm s acts →
      ∀ j,
        (runActivations B M hm s acts j).err = true →
        (s j).err = true ∧
          signedVal M (runActivations B M hm s acts j) =
            signedVal M (s j) := by
  intro s acts
  induction acts generalizing s with
  | nil =>
      intro htrace j hpost
      change (s j).err = true at hpost
      change (s j).err = true ∧
        signedVal M (s j) = signedVal M (s j)
      exact ⟨hpost, rfl⟩
  | cons a rest ih =>
      intro htrace j hpost
      change Quiet M hm s ∧ Frozen M D hm s ∧
        StableTrace B M D hm
          (activate B M hm s a.1 a.2) rest at htrace
      change
        (runActivations B M hm
          (activate B M hm s a.1 a.2) rest j).err = true at hpost
      have htail := ih (activate B M hm s a.1 a.2)
        htrace.2.2 j hpost
      have hone := error_monotone hm s a.1 a.2
        htrace.1 htrace.2.1 j htail.1
      change (s j).err = true ∧
        signedVal M
            (runActivations B M hm
              (activate B M hm s a.1 a.2) rest j) =
          signedVal M (s j)
      exact ⟨hone.1, htail.2.trans hone.2⟩

/-! ## The fixed dependency DAG -/

/-- The two cyclic neighbours of a site. -/
def Neighbor {m : Nat} (hm : 0 < m) (u v : Fin m) : Prop :=
  v = left hm u ∨ v = right hm u

/-- Static dependency edge: the target is an erroneous, strictly higher
neighbour of the erroneous source. -/
def DepEdge {m : Nat} (M : Nat) (hm : 0 < m)
    (s : ClockConfig m) (u v : Fin m) : Prop :=
  Neighbor hm u v ∧
    (s u).err = true ∧ (s v).err = true ∧
      signedVal M (s u) < signedVal M (s v)

instance neighborDecidable {m : Nat} (hm : 0 < m)
    (u v : Fin m) : Decidable (Neighbor hm u v) := by
  unfold Neighbor
  exact inferInstance

instance depEdgeDecidable {m M : Nat} (hm : 0 < m)
    (s : ClockConfig m) (u v : Fin m) :
    Decidable (DepEdge M hm s u v) := by
  unfold DepEdge
  exact inferInstance

/-- A dependency path; the empty path is harmless, while every nonempty
path consists of initial errors joined by dependency edges. -/
def DepPath {m : Nat} (M : Nat) (hm : 0 < m)
    (s : ClockConfig m) : List (Fin m) → Prop
  | [] => True
  | [u] => (s u).err = true
  | u :: v :: rest =>
      DepEdge M hm s u v ∧ DepPath M hm s (v :: rest)

/-- A nonempty dependency path whose first vertex is `u`. -/
def DepPathFrom {m : Nat} (M : Nat) (hm : 0 < m)
    (s : ClockConfig m) (u : Fin m) (path : List (Fin m)) : Prop :=
  ∃ rest, path = u :: rest ∧ DepPath M hm s path

private theorem dep_path_singleton {m M : Nat} (hm : 0 < m)
    (s : ClockConfig m) (u : Fin m) (herr : (s u).err = true) :
    DepPathFrom M hm s u [u] := by
  refine ⟨[], rfl, ?_⟩
  simpa [DepPath] using herr

private theorem dep_path_prefix {m M : Nat} (hm : 0 < m)
    (s : ClockConfig m) (u v : Fin m) (path : List (Fin m))
    (hedge : DepEdge M hm s u v)
    (hpath : DepPathFrom M hm s v path) :
    DepPathFrom M hm s u (u :: path) := by
  rcases hpath with ⟨rest, heq, hp⟩
  subst path
  refine ⟨v :: rest, rfl, ?_⟩
  change DepEdge M hm s u v ∧ DepPath M hm s (v :: rest)
  exact ⟨hedge, hp⟩

private theorem dep_path_tick_bound {m M D : Nat} (hm : 0 < m)
    (s : ClockConfig m) (hfrozen : Frozen M D hm s) :
    ∀ (u : Fin m) (rest : List (Fin m)),
      DepPath M hm s (u :: rest) →
      (u :: rest).length + (s u).tick ≤ D + 1 := by
  intro u rest
  induction rest generalizing u with
  | nil =>
      intro hp
      change (s u).err = true at hp
      have hb := (hfrozen u hp).2.2
      simp only [signedVal, Int.ofNat_eq_natCast] at hb
      simp only [List.length_cons, List.length_nil]
      omega
  | cons v rest ih =>
      intro hp
      change DepEdge M hm s u v ∧
        DepPath M hm s (v :: rest) at hp
      have htail := ih v hp.2
      have hstrict := hp.1.2.2.2
      simp only [signedVal, Int.ofNat_eq_natCast] at hstrict
      simp only [List.length_cons] at htail ⊢
      omega

/-- Along a dependency path ticks strictly increase from a value at least
zero to a value at most `D`; hence there are at most `D+1` vertices. -/
theorem dep_path_bound {m M D : Nat} (hm : 0 < m)
    (s : ClockConfig m) (hfrozen : Frozen M D hm s)
    (path : List (Fin m)) (hpath : DepPath M hm s path) :
    path.length ≤ D + 1 := by
  cases path with
  | nil => simp
  | cons u rest =>
      have h := dep_path_tick_bound hm s hfrozen u rest hpath
      omega

/-! ## A maximal surviving error clears on its poll -/

private theorem upperGap_true_of_far (M : Nat)
    (center upper : NativeRecord) (hM : 4 ≤ M)
    (hfar : center.tick + 2 ≤ upper.tick)
    (hupper : upper.tick < M / 2) :
    upperGapB M center.tick upper = true := by
  by_cases hc : center.tick = M / 2
  · rw [hc] at hfar
    omega
  · simp [upperGapB, hfar, hc]

private theorem lower_close_left {m M D : Nat} (hm : 0 < m)
    (s : ClockConfig m) (i : Fin m)
    (hdomain : ClockDomain M s)
    (hquiet : Quiet M hm s) (hfrozen : Frozen M D hm s)
    (herr : (s i).err = true) :
    (s i).tick ≤ (s (left hm i)).tick + 1 := by
  by_cases hle : (s i).tick ≤ (s (left hm i)).tick + 1
  · exact hle
  · have hfar : (s (left hm i)).tick + 2 ≤ (s i).tick := by omega
    by_cases hleft : (s (left hm i)).err = true
    · have hb := (hfrozen (left hm i) hleft).2.1
      rw [right_left_cycle hm i] at hb
      simp only [signedVal, Int.ofNat_eq_natCast] at hb
      omega
    · have hleftFalse : (s (left hm i)).err = false := by
        cases h : (s (left hm i)).err <;> simp_all
      have hirange := (hdomain.2.2 i).2 herr
      have hgap := upperGap_true_of_far M
        (s (left hm i)) (s i) hdomain.1 hfar hirange
      have hroot :
          rootB M (s (left hm (left hm i))) (s (left hm i))
            (s (right hm (left hm i))) = true := by
        rw [right_left_cycle hm i]
        simp [rootB, hleftFalse, hgap]
      have hq := hquiet (left hm i) hroot
      rw [hleftFalse] at hq
      cases hq.1

private theorem lower_close_right {m M D : Nat} (hm : 0 < m)
    (s : ClockConfig m) (i : Fin m)
    (hdomain : ClockDomain M s)
    (hquiet : Quiet M hm s) (hfrozen : Frozen M D hm s)
    (herr : (s i).err = true) :
    (s i).tick ≤ (s (right hm i)).tick + 1 := by
  by_cases hle : (s i).tick ≤ (s (right hm i)).tick + 1
  · exact hle
  · have hfar : (s (right hm i)).tick + 2 ≤ (s i).tick := by omega
    by_cases hright : (s (right hm i)).err = true
    · have hb := (hfrozen (right hm i) hright).1
      rw [left_right_cycle hm i] at hb
      simp only [signedVal, Int.ofNat_eq_natCast] at hb
      omega
    · have hrightFalse : (s (right hm i)).err = false := by
        cases h : (s (right hm i)).err <;> simp_all
      have hirange := (hdomain.2.2 i).2 herr
      have hgap := upperGap_true_of_far M
        (s (right hm i)) (s i) hdomain.1 hfar hirange
      have hroot :
          rootB M (s (left hm (right hm i))) (s (right hm i))
            (s (right hm (right hm i))) = true := by
        rw [left_right_cycle hm i]
        simp [rootB, hrightFalse, hgap]
      have hq := hquiet (right hm i) hroot
      rw [hrightFalse] at hq
      cases hq.1

private theorem near_left_true {m M D : Nat} (hm : 0 < m)
    (s : ClockConfig m) (i : Fin m)
    (hdomain : ClockDomain M s)
    (hquiet : Quiet M hm s) (hfrozen : Frozen M D hm s)
    (herr : (s i).err = true)
    (hhigher : ∀ v, Neighbor hm i v →
      signedVal M (s i) < signedVal M (s v) →
      (s v).err = false) :
    nearB (s i).tick (s (left hm i)) = true := by
  have huInt := (hfrozen i herr).1
  have hu : (s (left hm i)).tick ≤ (s i).tick + 1 := by
    simp only [signedVal, Int.ofNat_eq_natCast] at huInt
    omega
  have hl := lower_close_left hm s i hdomain hquiet hfrozen herr
  by_cases hle : (s (left hm i)).tick ≤ (s i).tick
  · simp [nearB, hu, hl, hle]
  · have hstrict :
        signedVal M (s i) < signedVal M (s (left hm i)) := by
      simp only [signedVal, Int.ofNat_eq_natCast]
      omega
    have hc := hhigher (left hm i) (Or.inl rfl) hstrict
    simp [nearB, hu, hl, hc]

private theorem near_right_true {m M D : Nat} (hm : 0 < m)
    (s : ClockConfig m) (i : Fin m)
    (hdomain : ClockDomain M s)
    (hquiet : Quiet M hm s) (hfrozen : Frozen M D hm s)
    (herr : (s i).err = true)
    (hhigher : ∀ v, Neighbor hm i v →
      signedVal M (s i) < signedVal M (s v) →
      (s v).err = false) :
    nearB (s i).tick (s (right hm i)) = true := by
  have huInt := (hfrozen i herr).2.1
  have hu : (s (right hm i)).tick ≤ (s i).tick + 1 := by
    simp only [signedVal, Int.ofNat_eq_natCast] at huInt
    omega
  have hl := lower_close_right hm s i hdomain hquiet hfrozen herr
  by_cases hle : (s (right hm i)).tick ≤ (s i).tick
  · simp [nearB, hu, hl, hle]
  · have hstrict :
        signedVal M (s i) < signedVal M (s (right hm i)) := by
      simp only [signedVal, Int.ofNat_eq_natCast]
      omega
    have hc := hhigher (right hm i) (Or.inr rfl) hstrict
    simp [nearB, hu, hl, hc]

/-- If an erroneous site's strictly higher erroneous dependencies have all
cleared, its own activation takes the native `clear` branch. -/
theorem clears_on_poll {m M D B : Nat} (hm : 0 < m)
    (s : ClockConfig m) (u : Fin m) (delta : Bool)
    (hdomain : ClockDomain M s)
    (hquiet : Quiet M hm s) (hfrozen : Frozen M D hm s)
    (herr : (s u).err = true)
    (hhigher : ∀ v, Neighbor hm u v →
      signedVal M (s u) < signedVal M (s v) →
      (s v).err = false) :
    (activate B M hm s u delta u).err = false := by
  have hl := near_left_true hm s u hdomain hquiet hfrozen herr hhigher
  have hr := near_right_true hm s u hdomain hquiet hfrozen herr hhigher
  rw [activate_owner]
  rw [native_action_reduced hm s u hquiet hfrozen]
  simp [herr, hl, hr, finishNative]

/-! ## All-correct plus quiet is legitimate -/

/-- Literal native-edge legitimacy: equality, an ordinary difference of one,
or the native wrap pair `(M-1, M/2)` in either orientation. -/
def LegitimateEdge (M : Nat) (a b : NativeRecord) : Prop :=
  a.tick = b.tick ∨
  a.tick + 1 = b.tick ∨
  b.tick + 1 = a.tick ∨
  (a.tick = M - 1 ∧ b.tick = M / 2) ∨
  (b.tick = M - 1 ∧ a.tick = M / 2)

/-- Every directed cycle edge is legitimate. -/
def Legitimate {m : Nat} (M : Nat) (hm : 0 < m)
    (s : ClockConfig m) : Prop :=
  ∀ i, LegitimateEdge M (s i) (s (right hm i))

private theorem root_false_of_correct {m M : Nat} (hm : 0 < m)
    (s : ClockConfig m) (i : Fin m)
    (hquiet : Quiet M hm s) (hcorrect : (s i).err = false) :
    rootB M (s (left hm i)) (s i) (s (right hm i)) = false := by
  cases hroot : rootB M (s (left hm i)) (s i) (s (right hm i)) with
  | false => rfl
  | true =>
      have hq := hquiet i hroot
      rw [hcorrect] at hq
      cases hq.1

private theorem upperGap_right_false {m M : Nat} (hm : 0 < m)
    (s : ClockConfig m) (i : Fin m)
    (hquiet : Quiet M hm s) (hcorrect : (s i).err = false) :
    upperGapB M (s i).tick (s (right hm i)) = false := by
  have hroot := root_false_of_correct hm s i hquiet hcorrect
  cases hr : upperGapB M (s i).tick (s (right hm i)) with
  | false => rfl
  | true =>
      have hrootTrue :
          rootB M (s (left hm i)) (s i) (s (right hm i)) = true := by
        simp [rootB, hcorrect, hr]
      rw [hrootTrue] at hroot
      cases hroot

private theorem upperGap_left_false {m M : Nat} (hm : 0 < m)
    (s : ClockConfig m) (i : Fin m)
    (hquiet : Quiet M hm s) (hcorrect : (s i).err = false) :
    upperGapB M (s i).tick (s (left hm i)) = false := by
  have hroot := root_false_of_correct hm s i hquiet hcorrect
  cases hl : upperGapB M (s i).tick (s (left hm i)) with
  | false => rfl
  | true =>
      have hrootTrue :
          rootB M (s (left hm i)) (s i) (s (right hm i)) = true := by
        simp [rootB, hcorrect, hl]
      rw [hrootTrue] at hroot
      cases hroot

private theorem upperGap_false_cases (M t : Nat) (y : NativeRecord)
    (hfalse : upperGapB M t y = false) :
    y.tick ≤ t + 1 ∨ (t = M / 2 ∧ y.tick = M - 1) := by
  by_cases hle : y.tick ≤ t + 1
  · exact Or.inl hle
  · have hgap : t + 2 ≤ y.tick := by omega
    by_cases ht : t = M / 2
    · by_cases hy : y.tick = M - 1
      · exact Or.inr ⟨ht, hy⟩
      · have hgap' : M / 2 + 2 ≤ y.tick := by omega
        have htrue : upperGapB M t y = true := by
          simp [upperGapB, ht, hy, hgap']
        rw [htrue] at hfalse
        cases hfalse
    · have htrue : upperGapB M t y = true := by
        simp [upperGapB, hgap, ht]
      rw [htrue] at hfalse
      cases hfalse

private theorem legitimate_of_close (M : Nat) (a b : NativeRecord)
    (hab : b.tick ≤ a.tick + 1) (hba : a.tick ≤ b.tick + 1) :
    LegitimateEdge M a b := by
  by_cases heq : a.tick = b.tick
  · exact Or.inl heq
  · by_cases hlt : a.tick < b.tick
    · have hone : a.tick + 1 = b.tick := by omega
      exact Or.inr (Or.inl hone)
    · have hone : b.tick + 1 = a.tick := by omega
      exact Or.inr (Or.inr (Or.inl hone))

/-- With no errors, quietness says that no correct site has a forbidden upper
gap. Applying this in both directions gives exactly the legitimate edges. -/
theorem legitimate_of_correct_quiet {m M : Nat} (hm : 0 < m)
    (s : ClockConfig m)
    (hcorrect : ∀ i, (s i).err = false)
    (hquiet : Quiet M hm s) :
    Legitimate M hm s := by
  intro i
  have hforwardFalse :=
    upperGap_right_false hm s i hquiet (hcorrect i)
  have hforward := upperGap_false_cases M (s i).tick
    (s (right hm i)) hforwardFalse
  have hbackFalse :=
    upperGap_left_false hm s (right hm i) hquiet
      (hcorrect (right hm i))
  rw [left_right_cycle hm i] at hbackFalse
  have hback := upperGap_false_cases M (s (right hm i)).tick
    (s i) hbackFalse
  rcases hforward with hforward | hforward
  · rcases hback with hback | hback
    · exact legitimate_of_close M (s i) (s (right hm i))
        hforward hback
    · exact Or.inr (Or.inr (Or.inr
        (Or.inl ⟨hback.2, hback.1⟩)))
  · exact Or.inr (Or.inr (Or.inr
      (Or.inr ⟨hforward.2, hforward.1⟩)))

/-! ## Clearance levels and deterministic service paths -/

/-- Fuelled numerical realization of `1 + max` over the two higher erroneous
neighbours. The global path bound makes fuel `D+1` sufficient. -/
def clearanceLevelFuel {m : Nat} (M : Nat) (hm : 0 < m)
    (s : ClockConfig m) : Nat → Fin m → Nat
  | 0, _ => 0
  | fuel + 1, u =>
      if (s u).err = true then
        1 + max
          (if DepEdge M hm s u (left hm u) then
            clearanceLevelFuel M hm s fuel (left hm u)
           else 0)
          (if DepEdge M hm s u (right hm u) then
            clearanceLevelFuel M hm s fuel (right hm u)
           else 0)
      else 0

/-- The numerical clearance level at the proved global depth cap. -/
def clearanceLevel {m : Nat} (M D : Nat) (hm : 0 < m)
    (s : ClockConfig m) (u : Fin m) : Nat :=
  clearanceLevelFuel M hm s (D + 1) u

theorem clearanceLevel_error {m M D : Nat} (hm : 0 < m)
    (s : ClockConfig m) (u : Fin m) (herr : (s u).err = true) :
    clearanceLevel M D hm s u =
      1 + max
        (if DepEdge M hm s u (left hm u) then
          clearanceLevelFuel M hm s D (left hm u)
         else 0)
        (if DepEdge M hm s u (right hm u) then
          clearanceLevelFuel M hm s D (right hm u)
         else 0) := by
  simp [clearanceLevel, clearanceLevelFuel, herr]

/-- Recursive `at most k` form of the same `1 + max` definition. -/
def ClearanceBound {m : Nat} (M : Nat) (hm : 0 < m)
    (s : ClockConfig m) : Nat → Fin m → Prop
  | 0, u => (s u).err = false
  | k + 1, u =>
      (s u).err = true ∧
        ∀ v, DepEdge M hm s u v → ClearanceBound M hm s k v

/-- Exact clearance level: the least recursive upper bound. -/
def ClearanceLevel {m : Nat} (M : Nat) (hm : 0 < m)
    (s : ClockConfig m) (u : Fin m) (k : Nat) : Prop :=
  ClearanceBound M hm s k u ∧
    ∀ j, j < k → ¬ ClearanceBound M hm s j u

/-- Apply the service functions from the highest dependency back toward the
starting error. Thus a path `[u,v,...]` first clears its tail and queries
`u` last. -/
def clearSeqTime {m : Nat} (S : Fin m → Nat → Nat) (tzero : Nat) :
    List (Fin m) → Nat
  | [] => tzero
  | u :: path => S u (clearSeqTime S tzero path)

theorem clearSeqTime_cons {m : Nat} (S : Fin m → Nat → Nat)
    (tzero : Nat) (u : Fin m) (path : List (Fin m)) :
    clearSeqTime S tzero (u :: path) =
      S u (clearSeqTime S tzero path) := rfl

theorem clearSeqTime_strict {m : Nat} (S : Fin m → Nat → Nat)
    (tzero : Nat) (hafter : ∀ i t, t < S i t)
    (u : Fin m) (path : List (Fin m)) :
    clearSeqTime S tzero path <
      clearSeqTime S tzero (u :: path) := by
  exact hafter u _

theorem clearSeqTime_mono {m : Nat} (S : Fin m → Nat → Nat)
    (hmono : ∀ i t t', t ≤ t' → S i t ≤ S i t') :
    ∀ (path : List (Fin m)) (t t' : Nat),
      t ≤ t' → clearSeqTime S t path ≤ clearSeqTime S t' path := by
  intro path
  induction path with
  | nil =>
      intro t t' h
      exact h
  | cons u path ih =>
      intro t t' h
      exact hmono u _ _ (ih t t' h)

/-- Temporal interface at the frozen cut. `ClearedBy i t` means that the
initial error at `i` is correct by raw time `t`. The `poll` field is the
sequence-level bridge supplied by `error_monotone` and `clears_on_poll`. -/
structure ClearProcess {m : Nat} (M : Nat) (hm : 0 < m)
    (s : ClockConfig m) (S : Fin m → Nat → Nat)
    (ClearedBy : Fin m → Nat → Prop) : Prop where
  service_after : ∀ i t, t < S i t
  service_mono : ∀ i t t', t ≤ t' → S i t ≤ S i t'
  correct_mono : ∀ i t t', t ≤ t' →
    ClearedBy i t → ClearedBy i t'
  poll : ∀ u t, (s u).err = true →
    (∀ v, DepEdge M hm s u v → ClearedBy v t) →
      ClearedBy u (S u t)

private theorem clearanceBound_of_path_bound {m M : Nat} (hm : 0 < m)
    (s : ClockConfig m) :
    ∀ (k : Nat) (u : Fin m),
      (s u).err = true →
      (∀ path, DepPathFrom M hm s u path → path.length ≤ k) →
      ClearanceBound M hm s k u := by
  intro k
  induction k with
  | zero =>
      intro u herr hcap
      have hshort := hcap [u] (dep_path_singleton hm s u herr)
      simp only [List.length_cons, List.length_nil] at hshort
      omega
  | succ k ih =>
      intro u herr hcap
      change (s u).err = true ∧
        ∀ v, DepEdge M hm s u v → ClearanceBound M hm s k v
      refine ⟨herr, ?_⟩
      intro v hedge
      apply ih v hedge.2.2.1
      intro path hpath
      have hpref := dep_path_prefix hm s u v path hedge hpath
      have hb := hcap (u :: path) hpref
      simp only [List.length_cons] at hb
      omega

private theorem clear_time_bound
    {m M : Nat} (hm : 0 < m) (s : ClockConfig m)
    (S : Fin m → Nat → Nat) (tzero : Nat)
    (ClearedBy : Fin m → Nat → Prop)
    (proc : ClearProcess M hm s S ClearedBy) :
    ∀ (k : Nat) (u : Fin m),
      ClearanceBound M hm s k u →
      (s u).err = true →
      ∃ path,
        DepPathFrom M hm s u path ∧ path.length ≤ k ∧
          ClearedBy u (clearSeqTime S tzero path) := by
  intro k
  induction k with
  | zero =>
      intro u hbound herr
      change (s u).err = false at hbound
      rw [herr] at hbound
      cases hbound
  | succ k ih =>
      intro u hbound herr
      change (s u).err = true ∧
        ∀ v, DepEdge M hm s u v →
          ClearanceBound M hm s k v at hbound
      by_cases hleft : DepEdge M hm s u (left hm u)
      · obtain ⟨pathLeft, hpLeft, hlenLeft, hclearLeft⟩ :=
          ih (left hm u) (hbound.2 (left hm u) hleft)
            hleft.2.2.1
        by_cases hright : DepEdge M hm s u (right hm u)
        · obtain ⟨pathRight, hpRight, hlenRight, hclearRight⟩ :=
            ih (right hm u) (hbound.2 (right hm u) hright)
              hright.2.2.1
          by_cases htime :
              clearSeqTime S tzero pathLeft ≤
                clearSeqTime S tzero pathRight
          · refine ⟨u :: pathRight,
              dep_path_prefix hm s u (right hm u) pathRight
                hright hpRight, ?_, ?_⟩
            · simp only [List.length_cons]
              omega
            · change ClearedBy u
                (S u (clearSeqTime S tzero pathRight))
              apply proc.poll u (clearSeqTime S tzero pathRight) herr
              intro v hedge
              rcases hedge.1 with hv | hv
              · subst v
                exact proc.correct_mono (left hm u) _ _
                  htime hclearLeft
              · subst v
                exact hclearRight
          · have htime' :
                clearSeqTime S tzero pathRight ≤
                  clearSeqTime S tzero pathLeft :=
              Nat.le_of_not_ge htime
            refine ⟨u :: pathLeft,
              dep_path_prefix hm s u (left hm u) pathLeft
                hleft hpLeft, ?_, ?_⟩
            · simp only [List.length_cons]
              omega
            · change ClearedBy u
                (S u (clearSeqTime S tzero pathLeft))
              apply proc.poll u (clearSeqTime S tzero pathLeft) herr
              intro v hedge
              rcases hedge.1 with hv | hv
              · subst v
                exact hclearLeft
              · subst v
                exact proc.correct_mono (right hm u) _ _
                  htime' hclearRight
        · refine ⟨u :: pathLeft,
            dep_path_prefix hm s u (left hm u) pathLeft
              hleft hpLeft, ?_, ?_⟩
          · simp only [List.length_cons]
            omega
          · change ClearedBy u
              (S u (clearSeqTime S tzero pathLeft))
            apply proc.poll u (clearSeqTime S tzero pathLeft) herr
            intro v hedge
            rcases hedge.1 with hv | hv
            · subst v
              exact hclearLeft
            · subst v
              exact False.elim (hright hedge)
      · by_cases hright : DepEdge M hm s u (right hm u)
        · obtain ⟨pathRight, hpRight, hlenRight, hclearRight⟩ :=
            ih (right hm u) (hbound.2 (right hm u) hright)
              hright.2.2.1
          refine ⟨u :: pathRight,
            dep_path_prefix hm s u (right hm u) pathRight
              hright hpRight, ?_, ?_⟩
          · simp only [List.length_cons]
            omega
          · change ClearedBy u
              (S u (clearSeqTime S tzero pathRight))
            apply proc.poll u (clearSeqTime S tzero pathRight) herr
            intro v hedge
            rcases hedge.1 with hv | hv
            · subst v
              exact False.elim (hleft hedge)
            · subst v
              exact hclearRight
        · refine ⟨[u], dep_path_singleton hm s u herr, by simp, ?_⟩
          change ClearedBy u (S u tzero)
          apply proc.poll u tzero herr
          intro v hedge
          rcases hedge.1 with hv | hv
          · subst v
            exact False.elim (hleft hedge)
          · subst v
            exact False.elim (hright hedge)

/-- An error whose exact recursive clearance level is `k` clears by a
successive service query along one dependency path of length at most `k`. -/
theorem clear_time_at_level
    {m M : Nat} (hm : 0 < m) (s : ClockConfig m)
    (S : Fin m → Nat → Nat) (tzero : Nat)
    (ClearedBy : Fin m → Nat → Prop)
    (proc : ClearProcess M hm s S ClearedBy)
    (u : Fin m) (k : Nat)
    (herr : (s u).err = true)
    (hlevel : ClearanceLevel M hm s u k) :
    ∃ path,
      DepPathFrom M hm s u path ∧ path.length ≤ k ∧
        ClearedBy u (clearSeqTime S tzero path) := by
  exact clear_time_bound hm s S tzero ClearedBy proc
    k u hlevel.1 herr

/-- Frozen supplies the recursive clearance bound `D+1` for every error. -/
theorem clearance_bound {m M D : Nat} (hm : 0 < m)
    (s : ClockConfig m) (hfrozen : Frozen M D hm s)
    (u : Fin m) (herr : (s u).err = true) :
    ClearanceBound M hm s (D + 1) u := by
  apply clearanceBound_of_path_bound hm s (D + 1) u herr
  intro path hpath
  rcases hpath with ⟨rest, heq, hp⟩
  subst path
  exact dep_path_bound hm s hfrozen (u :: rest) hp

/-- Global deterministic clearance-time statement used by the stopping-time
argument: each initial error clears by a service sequence of at most `D+1`
queries along one fixed dependency path. -/
theorem clear_time
    {m M D : Nat} (hm : 0 < m) (s : ClockConfig m)
    (hfrozen : Frozen M D hm s)
    (S : Fin m → Nat → Nat) (tzero : Nat)
    (ClearedBy : Fin m → Nat → Prop)
    (proc : ClearProcess M hm s S ClearedBy)
    (u : Fin m) (herr : (s u).err = true) :
    ∃ path,
      DepPathFrom M hm s u path ∧ path.length ≤ D + 1 ∧
        ClearedBy u (clearSeqTime S tzero path) := by
  have hbound := clearance_bound hm s hfrozen u herr
  exact clear_time_bound hm s S tzero ClearedBy proc
    (D + 1) u hbound herr

#print axioms error_monotone
#print axioms error_monotone_run
#print axioms dep_path_bound
#print axioms clears_on_poll
#print axioms legitimate_of_correct_quiet
#print axioms clear_time_at_level
#print axioms clear_time

end L4.Height.Recover.StageThree

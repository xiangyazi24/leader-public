import Leader.Core.Basic
import Init.Data.List.Lemmas
import Init.Data.List.Perm
import Init.Grind

/-!
# Abstract paired-defect matching and gap contraction

This module isolates the deterministic combinatorics required by a future
literal-state compiler.  Defects are arranged in their cyclic physical order.
Each defect carries one of three roles:

* `U`: unmatched;
* `S`: the source (clockwise-left endpoint) of a matched pair;
* `T`: the target (clockwise-right endpoint) of a matched pair.

On a selected directed gap, two unmatched endpoints form `S,T`.  Otherwise an
invalid `S` on the left or invalid `T` on the right is reset to `U`.  The two
repair guards are mutually exclusive.  This is an abstract protocol contract,
not yet a claim that acknowledgements can be compiled into the literal
directed-ring agent state.

The deterministic results below prove persistence of valid pairs, characterize
terminal states as maximal cyclic matchings, give the sharp elementary bound
`3 * |M| >= m`, and formalize the one-unit gap-potential decrease used by the
contraction phase.  Probability and scheduler-time conversion deliberately do
not occur here: a later consumer must prove that its literal message protocol
implements these abstract steps and supplies the iid waiting-time argument.
-/

namespace PairedDefectMatching

/-! ## Three-role local transition -/

/-- Abstract role of one currently supported defect. -/
inductive Role where
  | U
  | S
  | T
  deriving DecidableEq, Repr

/-- The exact selected-gap transition.  The nine cases are written out so the
priority of `U,U -> S,T` over repair is part of the definition. -/
def pairStep : Role → Role → Role × Role
  | .U, .U => (.S, .T)
  | .U, .S => (.U, .S)
  | .U, .T => (.U, .U)
  | .S, .U => (.U, .U)
  | .S, .S => (.U, .S)
  | .S, .T => (.S, .T)
  | .T, .U => (.T, .U)
  | .T, .S => (.T, .S)
  | .T, .T => (.T, .U)

/-- Semantic classification of a selected abstract gap. -/
inductive Action where
  | stutter
  | match
  | repair
  deriving DecidableEq, Repr

/-- `U,U` is a match, the four one-sided invalid cases are repairs, and all
remaining cases stutter. -/
def action : Role → Role → Action
  | .U, .U => .match
  | .U, .T => .repair
  | .S, .U => .repair
  | .S, .S => .repair
  | .T, .T => .repair
  | _, _ => .stutter

@[simp] theorem pairStep_ST : pairStep .S .T = (.S, .T) := rfl

/-- A target used as the left endpoint is never overwritten. -/
@[simp] theorem pairStep_left_T (b : Role) : (pairStep .T b).1 = .T := by
  cases b <;> rfl

/-- A source used as the right endpoint is never overwritten. -/
@[simp] theorem pairStep_right_S (a : Role) : (pairStep a .S).2 = .S := by
  cases a <;> rfl

/-- Local fixed points are exactly valid `S,T`, the two harmless unmatched-role
orders, and hence precisely the local clauses of a maximal matching. -/
def LocallyMaximal (a b : Role) : Prop :=
  (a = .S ↔ b = .T) ∧ ¬(a = .U ∧ b = .U)

theorem pairStep_eq_iff_locallyMaximal (a b : Role) :
    pairStep a b = (a, b) ↔ LocallyMaximal a b := by
  cases a <;> cases b <;> simp [pairStep, LocallyMaximal]

/-! ## Finite directed defect ring -/

/-- A role configuration on the cyclically ordered current defects. -/
abbrev Configuration (m : Nat) := Fin m → Role

/-- Apply the abstract role transition to the endpoints of selected gap `e`.
The nontrivial-ring hypothesis used by the theorems below ensures the two
endpoints are distinct; the definition itself remains total for every `m`. -/
def step (ring : DirectedRing m) (C : Configuration m) (e : Fin m) :
    Configuration m :=
  let r := ring.rightNeighbor e
  let out := pairStep (C e) (C r)
  fun i => if i = e then out.1 else if i = r then out.2 else C i

/-- Clockwise successor is injective on every nonempty ring. -/
theorem rightNeighbor_injective (ring : DirectedRing m) :
    Function.Injective ring.rightNeighbor := by
  intro a b hab
  apply Fin.ext
  have hv := congrArg Fin.val hab
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases ha : a.val + 1 < m
  · rw [Nat.mod_eq_of_lt ha] at hv
    by_cases hb : b.val + 1 < m
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = m := by omega
      rw [hbeq, Nat.mod_self] at hv
      omega
  · have haeq : a.val + 1 = m := by omega
    rw [haeq, Nat.mod_self] at hv
    by_cases hb : b.val + 1 < m
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = m := by omega
      omega

/-- On a ring with at least two defects, an edge has two distinct endpoints. -/
theorem rightNeighbor_ne (ring : DirectedRing m) (hm : 1 < m) (i : Fin m) :
    ring.rightNeighbor i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases hi : i.val + 1 < m
  · rw [Nat.mod_eq_of_lt hi] at hv
    omega
  · have hieq : i.val + 1 = m := by omega
    rw [hieq, Nat.mod_self] at hv
    omega

@[simp] theorem step_at_left (ring : DirectedRing m) (C : Configuration m)
    (e : Fin m) :
    step ring C e e = (pairStep (C e) (C (ring.rightNeighbor e))).1 := by
  simp [step]

@[simp] theorem step_at_right (ring : DirectedRing m) (hm : 1 < m)
    (C : Configuration m) (e : Fin m) :
    step ring C e (ring.rightNeighbor e) =
      (pairStep (C e) (C (ring.rightNeighbor e))).2 := by
  simp [step, rightNeighbor_ne ring hm e]

theorem step_at_other (ring : DirectedRing m) (C : Configuration m)
    (e i : Fin m) (hil : i ≠ e) (hir : i ≠ ring.rightNeighbor e) :
    step ring C e i = C i := by
  simp [step, hil, hir]

/-- A valid matching edge is an adjacent `S,T` pair. -/
def ValidPair (ring : DirectedRing m) (C : Configuration m) (e : Fin m) : Prop :=
  C e = .S ∧ C (ring.rightNeighbor e) = .T

/-- Once an `S,T` edge exists it survives every abstract interaction, including
interactions on either neighboring gap. -/
theorem validPair_step (ring : DirectedRing m) (hm : 1 < m)
    (C : Configuration m) (pairEdge selected : Fin m)
    (hpair : ValidPair ring C pairEdge) :
    ValidPair ring (step ring C selected) pairEdge := by
  constructor
  · by_cases hleft : selected = pairEdge
    · subst selected
      rw [step_at_left]
      simp [hpair.1, hpair.2]
    · by_cases hresp : ring.rightNeighbor selected = pairEdge
      · subst pairEdge
        rw [step_at_right ring hm]
        simpa [hpair.1] using pairStep_right_S (C selected)
      · rw [step_at_other ring C selected pairEdge (Ne.symm hleft) (Ne.symm hresp)]
        exact hpair.1
  · by_cases hinit : selected = ring.rightNeighbor pairEdge
    · subst selected
      rw [step_at_left]
      simpa [hpair.2] using
        pairStep_left_T (C (ring.rightNeighbor (ring.rightNeighbor pairEdge)))
    · by_cases hleft : selected = pairEdge
      · subst selected
        rw [step_at_right ring hm]
        simp [hpair.1, hpair.2]
      · have hresp : ring.rightNeighbor pairEdge ≠
            ring.rightNeighbor selected := by
          intro h
          exact hleft (rightNeighbor_injective ring h).symm
        rw [step_at_other ring C selected (ring.rightNeighbor pairEdge)
          (Ne.symm hinit) hresp]
        exact hpair.2

/-- A terminal role state has no changing selected gap. -/
def Terminal (ring : DirectedRing m) (C : Configuration m) : Prop :=
  ∀ e, step ring C e = C

/-- Edge-local representation of a maximal matching: sources and targets occur
exactly as adjacent `S,T` pairs, and no two unmatched defects are adjacent. -/
def MaximalMatching (ring : DirectedRing m) (C : Configuration m) : Prop :=
  ∀ e, LocallyMaximal (C e) (C (ring.rightNeighbor e))

/-- The abstract transition has exactly the maximal cyclic matchings as its
terminal configurations. -/
theorem terminal_iff_maximalMatching (ring : DirectedRing m) (hm : 1 < m)
    (C : Configuration m) :
    Terminal ring C ↔ MaximalMatching ring C := by
  constructor
  · intro hterm e
    apply (pairStep_eq_iff_locallyMaximal _ _).mp
    apply Prod.ext
    · have h := congrFun (hterm e) e
      simpa using h
    · have h := congrFun (hterm e) (ring.rightNeighbor e)
      rw [step_at_right ring hm C e] at h
      exact h
  · intro hmax e
    have hpair := (pairStep_eq_iff_locallyMaximal _ _).mpr (hmax e)
    funext i
    unfold step
    by_cases hil : i = e
    · subst i
      simpa using congrArg Prod.fst hpair
    · rw [if_neg hil]
      by_cases hir : i = ring.rightNeighbor e
      · subst i
        simpa using congrArg Prod.snd hpair
      · simp [hir]

/-! ## Global counts `I`, `Z`, and `F` -/

/-- Indicator that a role is unmatched. -/
def uBit : Role → Nat
  | .U => 1
  | _ => 0

/-- Indicator that a role is a source. -/
def sBit : Role → Nat
  | .S => 1
  | _ => 0

/-- Indicator that a role is a target. -/
def tBit : Role → Nat
  | .T => 1
  | _ => 0

/-- Number of invalid endpoint roles represented by a directed gap.  A bad
left `S` and bad right `T` cannot occur simultaneously. -/
def invalidGap : Role → Role → Nat
  | .S, .T => 0
  | .S, _ => 1
  | _, .T => 1
  | _, _ => 0

/-- Indicator that a selected gap is a repair opportunity. -/
def repairBit (a b : Role) : Nat :=
  if action a b = .repair then 1 else 0

/-- Indicator that both endpoints of a gap are unmatched. -/
def uuGap : Role → Role → Nat
  | .U, .U => 1
  | _, _ => 0

/-- Indicator that selecting a gap changes the abstract configuration. -/
def changingBit (a b : Role) : Nat :=
  if action a b = .stutter then 0 else 1

theorem repairBit_eq_invalidGap (a b : Role) :
    repairBit a b = invalidGap a b := by
  cases a <;> cases b <;> rfl

theorem action_eq_match_iff (a b : Role) :
    action a b = .match ↔ a = .U ∧ b = .U := by
  cases a <;> cases b <;> simp [action]

theorem changingBit_eq_uuGap_of_invalid_zero (a b : Role)
    (hzero : invalidGap a b = 0) :
    changingBit a b = uuGap a b := by
  cases a <;> cases b <;> simp_all [invalidGap, changingBit, uuGap, action]

/-- No endpoint becoming less unmatched can create a `U,U` gap. -/
theorem uuGap_mono {a a' b b' : Role}
    (ha : uBit a' ≤ uBit a) (hb : uBit b' ≤ uBit b) :
    uuGap a' b' ≤ uuGap a b := by
  cases a <;> cases a' <;> cases b <;> cases b' <;>
    simp_all [uBit, uuGap]

/-- Updating the responder never changes whether it is a source. -/
theorem sBit_pairStep_right (a b : Role) :
    sBit (pairStep a b).2 = sBit b := by
  cases a <;> cases b <;> rfl

/-- Updating the initiator never changes whether it is a target. -/
theorem tBit_pairStep_left (a b : Role) :
    tBit (pairStep a b).1 = tBit a := by
  cases a <;> cases b <;> rfl

/-- `invalidGap` depends only on the source-bit of its left endpoint and the
target-bit of its right endpoint. -/
theorem invalidGap_congr {a a' b b' : Role}
    (hs : sBit a = sBit a') (ht : tBit b = tBit b') :
    invalidGap a b = invalidGap a' b' := by
  cases a <;> cases a' <;> cases b <;> cases b' <;>
    simp_all [sBit, tBit, invalidGap]

/-- A repair clears exactly one invalid endpoint on the selected gap. -/
theorem invalidGap_repair (a b : Role) (h : action a b = .repair) :
    invalidGap (pairStep a b).1 (pairStep a b).2 = 0 ∧
      invalidGap a b = 1 := by
  cases a <;> cases b <;> simp_all [action, pairStep, invalidGap]

/-- Matching and stuttering preserve selected-gap invalidity (which is zero in
both cases). -/
theorem invalidGap_nonrepair (a b : Role) (h : action a b ≠ .repair) :
    invalidGap (pairStep a b).1 (pairStep a b).2 = invalidGap a b := by
  cases a <;> cases b <;> simp_all [action, pairStep, invalidGap]

/-- A match consumes exactly two unmatched roles. -/
theorem uBit_match (a b : Role) (h : action a b = .match) :
    uBit (pairStep a b).1 + uBit (pairStep a b).2 + 2 =
      uBit a + uBit b := by
  cases a <;> cases b <;> simp_all [action, pairStep, uBit]

/-- A repair creates exactly one additional unmatched role. -/
theorem uBit_repair (a b : Role) (h : action a b = .repair) :
    uBit a + uBit b + 1 =
      uBit (pairStep a b).1 + uBit (pairStep a b).2 := by
  cases a <;> cases b <;> simp_all [action, pairStep, uBit]

/-- Stuttering preserves both endpoint roles literally. -/
theorem pairStep_eq_of_action_stutter (a b : Role)
    (h : action a b = .stutter) : pairStep a b = (a, b) := by
  cases a <;> cases b <;> simp_all [action, pairStep]

/-- `I`: number of invalid `S`/`T` roles.  Each source is inspected on its
outgoing gap and each target on its incoming gap, so every bad role is counted
exactly once. -/
def invalidCount (ring : DirectedRing m) (C : Configuration m) : Nat :=
  (List.ofFn fun e => invalidGap (C e) (C (ring.rightNeighbor e))).sum

/-- Number of currently enabled repair gaps. -/
def repairEdgeCount (ring : DirectedRing m) (C : Configuration m) : Nat :=
  (List.ofFn fun e => repairBit (C e) (C (ring.rightNeighbor e))).sum

/-- Number of `U,U` gaps.  Once `I=0`, these are exactly the changing gaps. -/
def unmatchedEdgeCount (ring : DirectedRing m) (C : Configuration m) : Nat :=
  (List.ofFn fun e => uuGap (C e) (C (ring.rightNeighbor e))).sum

/-- Number of nonstuttering selected gaps. -/
def changingEdgeCount (ring : DirectedRing m) (C : Configuration m) : Nat :=
  (List.ofFn fun e => changingBit (C e) (C (ring.rightNeighbor e))).sum

/-- `Z`: number of unmatched roles. -/
def unmatchedCount (C : Configuration m) : Nat :=
  (List.ofFn fun i => uBit (C i)).sum

/-- Number of `S` roles; in a terminal configuration this is `|M|`. -/
def pairCount (C : Configuration m) : Nat :=
  (List.ofFn fun i => sBit (C i)).sum

/-- Number of target roles, used internally for the role partition. -/
def targetCount (C : Configuration m) : Nat :=
  (List.ofFn fun i => tBit (C i)).sum

/-- Lexicographic potential encoded in `Nat`: invalidity dominates every
possible change in `Z`. -/
def fuel (ring : DirectedRing m) (C : Configuration m) : Nat :=
  (m + 1) * invalidCount ring C + unmatchedCount C

private theorem sum_ofFn_eq
    (f g : Fin m → Nat) (hfg : ∀ i, f i = g i) :
    (List.ofFn f).sum = (List.ofFn g).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons, hfg 0]
      exact congrArg (g 0 + ·)
        (ih (fun i => f i.succ) (fun i => g i.succ) (fun i => hfg i.succ))

private theorem sum_ofFn_le
    (f g : Fin m → Nat) (hfg : ∀ i, f i ≤ g i) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ) (fun i => hfg i.succ))

private theorem sum_ofFn_add (f g : Fin m → Nat) :
    (List.ofFn (fun i => f i + g i)).sum =
      (List.ofFn f).sum + (List.ofFn g).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih]
      omega

private theorem sum_ofFn_const (size value : Nat) :
    (List.ofFn (fun _ : Fin size => value)).sum = size * value := by
  induction size with
  | zero => simp
  | succ size ih =>
      rw [List.ofFn_succ, List.sum_cons, ih, Nat.succ_mul]
      exact Nat.add_comm _ _

/-- Replacing one entry gives a subtraction-free balance identity for the
complete finite sum. -/
private theorem sum_ofFn_balance_one
    (f g : Fin m → Nat) (j : Fin m)
    (hother : ∀ i, i ≠ j → f i = g i) :
    (List.ofFn f).sum + g j = (List.ofFn g).sum + f j := by
  induction m with
  | zero => exact Fin.elim0 j
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      by_cases hj0 : j = 0
      · subst j
        have htail :
            (List.ofFn (fun i : Fin m => f i.succ)).sum =
              (List.ofFn (fun i : Fin m => g i.succ)).sum := by
          apply sum_ofFn_eq
          intro i
          apply hother i.succ
          intro hbad
          have hv := congrArg Fin.val hbad
          simp at hv
        rw [htail]
        omega
      · have hjpos : 0 < j.val := by
          have hjne : j.val ≠ 0 := by
            intro h
            apply hj0
            apply Fin.ext
            simpa using h
          omega
        let j' : Fin m := ⟨j.val - 1, by omega⟩
        have hjsucc : j'.succ = j := by
          apply Fin.ext
          change j.val - 1 + 1 = j.val
          omega
        have hhead : f 0 = g 0 := hother 0 (Ne.symm hj0)
        have htail := ih
          (fun i : Fin m => f i.succ)
          (fun i : Fin m => g i.succ) j'
          (by
            intro i hij
            apply hother i.succ
            intro hbad
            apply hij
            apply Fin.ext
            have hv := congrArg Fin.val hbad
            change i.val + 1 = j.val at hv
            change i.val = j.val - 1
            omega)
        rw [hjsucc] at htail
        omega

/-- Two distinguished entries can be replaced without integer subtraction. -/
private theorem sum_ofFn_balance_two
    (f g : Fin m → Nat) (a b : Fin m) (hab : a ≠ b)
    (hother : ∀ i, i ≠ a → i ≠ b → f i = g i) :
    (List.ofFn f).sum + g a + g b =
      (List.ofFn g).sum + f a + f b := by
  let mid : Fin m → Nat := fun i => if i = a then f i else g i
  have hga : (List.ofFn mid).sum + g a =
      (List.ofFn g).sum + mid a := by
    apply sum_ofFn_balance_one mid g a
    intro i hia
    simp [mid, hia]
  have hfb : (List.ofFn f).sum + mid b =
      (List.ofFn mid).sum + f b := by
    apply sum_ofFn_balance_one f mid b
    intro i hib
    by_cases hia : i = a
    · subst i
      simp [mid]
    · simp [mid, hia, hother i hia hib]
  have hma : mid a = f a := by simp [mid]
  have hmb : mid b = g b := by simp [mid, Ne.symm hab]
  rw [hma] at hga
  rw [hmb] at hfb
  omega

private theorem sum_ofFn_rightNeighbor
    (ring : DirectedRing m) (f : Fin m → Nat) :
    (List.ofFn (fun e => f (ring.rightNeighbor e))).sum =
      (List.ofFn f).sum := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt ring.hn)
  subst m
  rw [show List.ofFn
      (fun e : Fin (k + 1) => f (ring.rightNeighbor e)) =
    (List.ofFn (fun i : Fin k =>
      f (ring.rightNeighbor i.castSucc))) ++
      [f (ring.rightNeighbor (Fin.last k))] from List.ofFn_succ_last]
  rw [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero,
    List.ofFn_succ, List.sum_cons]
  have hlast : ring.rightNeighbor (Fin.last k) = 0 := by
    apply Fin.ext
    simp [DirectedRing.rightNeighbor]
  have hsucc : ∀ i : Fin k,
      ring.rightNeighbor i.castSucc = i.succ := by
    intro i
    apply Fin.ext
    simp [DirectedRing.rightNeighbor,
      Nat.mod_eq_of_lt (by omega : i.val + 1 < k + 1)]
  rw [hlast]
  have hfun :
      (fun i : Fin k => f (ring.rightNeighbor i.castSucc)) =
        (fun i : Fin k => f i.succ) := by
    funext i
    rw [hsucc]
  rw [hfun]
  omega

/-! ### Exact global drift of `I`, `Z`, and `F` -/

/-- Away from the selected left endpoint, source-status is unchanged.  At the
selected responder this is the local `sBit_pairStep_right` invariant. -/
theorem sBit_step_of_ne_left (ring : DirectedRing m) (C : Configuration m)
    (e i : Fin m) (hne : i ≠ e) :
    sBit (step ring C e i) = sBit (C i) := by
  unfold step
  rw [if_neg hne]
  by_cases hir : i = ring.rightNeighbor e
  · subst i
    simp only [if_pos]
    exact sBit_pairStep_right _ _
  · simp [hir]

/-- Away from the selected right endpoint, target-status is unchanged.  At the
selected initiator this is the local `tBit_pairStep_left` invariant. -/
theorem tBit_step_of_ne_right (ring : DirectedRing m) (C : Configuration m)
    (e i : Fin m) (hne : i ≠ ring.rightNeighbor e) :
    tBit (step ring C e i) = tBit (C i) := by
  unfold step
  by_cases hil : i = e
  · subst i
    simp only [if_pos]
    exact tBit_pairStep_left _ _
  · simp [hil, hne]

/-- Every nonselected gap keeps its invalidity contribution.  Although its
endpoint role may be touched by the neighboring selected gap, exactly the bit
read by `invalidGap` is protected. -/
theorem invalidGap_step_of_ne (ring : DirectedRing m) (C : Configuration m)
    (selected other : Fin m) (hne : other ≠ selected) :
    invalidGap (step ring C selected other)
        (step ring C selected (ring.rightNeighbor other)) =
      invalidGap (C other) (C (ring.rightNeighbor other)) := by
  apply invalidGap_congr
  · exact sBit_step_of_ne_left ring C selected other hne
  · apply tBit_step_of_ne_right
    intro h
    exact hne (rightNeighbor_injective ring h)

/-- A matching step can only turn unmatched endpoints into matched endpoints;
it never creates a new unmatched role at any site. -/
theorem uBit_step_match_le (ring : DirectedRing m) (hm : 1 < m)
    (C : Configuration m) (e i : Fin m)
    (hmatch : action (C e) (C (ring.rightNeighbor e)) = .match) :
    uBit (step ring C e i) ≤ uBit (C i) := by
  have hroles := (action_eq_match_iff _ _).mp hmatch
  by_cases hil : i = e
  · subst i
    rw [step_at_left]
    simp [hroles.1, hroles.2, pairStep, uBit]
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      rw [step_at_right ring hm]
      simp [hroles.1, hroles.2, pairStep, uBit]
    · rw [step_at_other ring C e i hil hir]
      exact Nat.le_refl _

/-- A match cannot create a new `U,U` gap anywhere. -/
theorem uuGap_step_match_le (ring : DirectedRing m) (hm : 1 < m)
    (C : Configuration m) (e i : Fin m)
    (hmatch : action (C e) (C (ring.rightNeighbor e)) = .match) :
    uuGap (step ring C e i)
        (step ring C e (ring.rightNeighbor i)) ≤
      uuGap (C i) (C (ring.rightNeighbor i)) :=
  uuGap_mono
    (uBit_step_match_le ring hm C e i hmatch)
    (uBit_step_match_le ring hm C e (ring.rightNeighbor i) hmatch)

/-- On a repair step the global invalid count falls by exactly one. -/
theorem invalidCount_step_repair (ring : DirectedRing m) (hm : 1 < m)
    (C : Configuration m) (e : Fin m)
    (hrepair : action (C e) (C (ring.rightNeighbor e)) = .repair) :
    invalidCount ring (step ring C e) + 1 = invalidCount ring C := by
  let before : Fin m → Nat := fun i =>
    invalidGap (C i) (C (ring.rightNeighbor i))
  let after : Fin m → Nat := fun i =>
    invalidGap (step ring C e i)
      (step ring C e (ring.rightNeighbor i))
  have hbalance := sum_ofFn_balance_one before after e (by
    intro i hie
    exact (invalidGap_step_of_ne ring C e i hie).symm)
  have hlocal := invalidGap_repair
    (C e) (C (ring.rightNeighbor e)) hrepair
  have hbefore : before e = 1 := hlocal.2
  have hafter : after e = 0 := by
    simp only [after, step_at_left, step_at_right ring hm]
    exact hlocal.1
  unfold invalidCount
  change (List.ofFn after).sum + 1 = (List.ofFn before).sum
  omega

/-- Matching and stuttering preserve the global invalid count. -/
theorem invalidCount_step_nonrepair (ring : DirectedRing m) (hm : 1 < m)
    (C : Configuration m) (e : Fin m)
    (hnrepair : action (C e) (C (ring.rightNeighbor e)) ≠ .repair) :
    invalidCount ring (step ring C e) = invalidCount ring C := by
  let before : Fin m → Nat := fun i =>
    invalidGap (C i) (C (ring.rightNeighbor i))
  let after : Fin m → Nat := fun i =>
    invalidGap (step ring C e i)
      (step ring C e (ring.rightNeighbor i))
  have hbalance := sum_ofFn_balance_one before after e (by
    intro i hie
    exact (invalidGap_step_of_ne ring C e i hie).symm)
  have hlocal := invalidGap_nonrepair
    (C e) (C (ring.rightNeighbor e)) hnrepair
  have heq : after e = before e := by
    simp only [after, before, step_at_left, step_at_right ring hm]
    exact hlocal
  unfold invalidCount
  change (List.ofFn after).sum = (List.ofFn before).sum
  omega

/-- On a match step the global unmatched count falls by exactly two. -/
theorem unmatchedCount_step_match (ring : DirectedRing m) (hm : 1 < m)
    (C : Configuration m) (e : Fin m)
    (hmatch : action (C e) (C (ring.rightNeighbor e)) = .match) :
    unmatchedCount (step ring C e) + 2 = unmatchedCount C := by
  let before : Fin m → Nat := fun i => uBit (C i)
  let after : Fin m → Nat := fun i => uBit (step ring C e i)
  have hne : e ≠ ring.rightNeighbor e :=
    Ne.symm (rightNeighbor_ne ring hm e)
  have hbalance := sum_ofFn_balance_two before after e
    (ring.rightNeighbor e) hne (by
      intro i hie hir
      simp [before, after, step_at_other ring C e i hie hir])
  have hlocal := uBit_match
    (C e) (C (ring.rightNeighbor e)) hmatch
  have hends : after e + after (ring.rightNeighbor e) + 2 =
      before e + before (ring.rightNeighbor e) := by
    simp only [after, before, step_at_left, step_at_right ring hm]
    exact hlocal
  unfold unmatchedCount
  change (List.ofFn after).sum + 2 = (List.ofFn before).sum
  omega

/-- On a repair step the global unmatched count rises by exactly one. -/
theorem unmatchedCount_step_repair (ring : DirectedRing m) (hm : 1 < m)
    (C : Configuration m) (e : Fin m)
    (hrepair : action (C e) (C (ring.rightNeighbor e)) = .repair) :
    unmatchedCount C + 1 = unmatchedCount (step ring C e) := by
  let before : Fin m → Nat := fun i => uBit (C i)
  let after : Fin m → Nat := fun i => uBit (step ring C e i)
  have hne : e ≠ ring.rightNeighbor e :=
    Ne.symm (rightNeighbor_ne ring hm e)
  have hbalance := sum_ofFn_balance_two before after e
    (ring.rightNeighbor e) hne (by
      intro i hie hir
      simp [before, after, step_at_other ring C e i hie hir])
  have hlocal := uBit_repair
    (C e) (C (ring.rightNeighbor e)) hrepair
  have hends : before e + before (ring.rightNeighbor e) + 1 =
      after e + after (ring.rightNeighbor e) := by
    simp only [after, before, step_at_left, step_at_right ring hm]
    exact hlocal
  unfold unmatchedCount
  change (List.ofFn before).sum + 1 = (List.ofFn after).sum
  omega

/-- A stutter action is a literal configuration self-loop. -/
theorem step_eq_of_action_stutter (ring : DirectedRing m)
    (C : Configuration m) (e : Fin m)
    (hstutter : action (C e) (C (ring.rightNeighbor e)) = .stutter) :
    step ring C e = C := by
  have hpair := pairStep_eq_of_action_stutter
    (C e) (C (ring.rightNeighbor e)) hstutter
  funext i
  unfold step
  by_cases hil : i = e
  · subst i
    simpa using congrArg Prod.fst hpair
  · rw [if_neg hil]
    by_cases hir : i = ring.rightNeighbor e
    · subst i
      simpa using congrArg Prod.snd hpair
    · simp [hir]

/-- Repair decreases the encoded lexicographic potential by exactly `m`. -/
theorem fuel_step_repair (ring : DirectedRing m) (hm : 1 < m)
    (C : Configuration m) (e : Fin m)
    (hrepair : action (C e) (C (ring.rightNeighbor e)) = .repair) :
    fuel ring (step ring C e) + m = fuel ring C := by
  have hI := invalidCount_step_repair ring hm C e hrepair
  have hZ := unmatchedCount_step_repair ring hm C e hrepair
  unfold fuel
  rw [hI.symm, ← hZ, Nat.mul_add]
  omega

/-- Matching decreases the encoded lexicographic potential by exactly two. -/
theorem fuel_step_match (ring : DirectedRing m) (hm : 1 < m)
    (C : Configuration m) (e : Fin m)
    (hmatch : action (C e) (C (ring.rightNeighbor e)) = .match) :
    fuel ring (step ring C e) + 2 = fuel ring C := by
  have hI := invalidCount_step_nonrepair ring hm C e (by
    rw [hmatch]
    decide)
  have hZ := unmatchedCount_step_match ring hm C e hmatch
  unfold fuel
  rw [← hI, hZ.symm]
  omega

/-- Every nonstuttering selected abstract gap strictly lowers `F`. -/
theorem fuel_step_strict_of_nonstutter (ring : DirectedRing m) (hm : 1 < m)
    (C : Configuration m) (e : Fin m)
    (hprogress : action (C e) (C (ring.rightNeighbor e)) ≠ .stutter) :
    fuel ring (step ring C e) < fuel ring C := by
  have hor :
      action (C e) (C (ring.rightNeighbor e)) = .match ∨
        action (C e) (C (ring.rightNeighbor e)) = .repair := by
    cases haction : action (C e) (C (ring.rightNeighbor e)) <;>
      simp_all
  rcases hor with hmatch | hrepair
  · have h := fuel_step_match ring hm C e hmatch
    omega
  · have h := fuel_step_repair ring hm C e hrepair
    omega

/-- Every role belongs to exactly one of `U,S,T`. -/
theorem role_count_partition (C : Configuration m) :
    unmatchedCount C + pairCount C + targetCount C = m := by
  unfold unmatchedCount pairCount targetCount
  rw [← sum_ofFn_add]
  rw [← sum_ofFn_add]
  calc
    (List.ofFn fun i => uBit (C i) + sBit (C i) + tBit (C i)).sum =
        (List.ofFn fun _ : Fin m => 1).sum := by
      apply sum_ofFn_eq
      intro i
      cases C i <;> rfl
    _ = m := by simpa using sum_ofFn_const m 1

/-- In a maximal role matching, sources and targets have equal cardinality. -/
theorem pairCount_eq_targetCount_of_maximal
    (ring : DirectedRing m) (C : Configuration m)
    (hmax : MaximalMatching ring C) :
    pairCount C = targetCount C := by
  unfold pairCount targetCount
  calc
    (List.ofFn fun i => sBit (C i)).sum =
        (List.ofFn fun i => tBit (C (ring.rightNeighbor i))).sum := by
      apply sum_ofFn_eq
      intro i
      have hiff := (hmax i).1
      cases hi : C i <;> cases hj : C (ring.rightNeighbor i) <;>
        simp_all [sBit, tBit]
    _ = (List.ofFn fun i => tBit (C i)).sum :=
      sum_ofFn_rightNeighbor ring (fun i => tBit (C i))

/-- Every unmatched defect in a maximal matching is followed injectively by a
source defect. -/
theorem unmatchedCount_le_pairCount_of_maximal
    (ring : DirectedRing m) (C : Configuration m)
    (hmax : MaximalMatching ring C) :
    unmatchedCount C ≤ pairCount C := by
  unfold unmatchedCount pairCount
  calc
    (List.ofFn fun i => uBit (C i)).sum ≤
        (List.ofFn fun i => sBit (C (ring.rightNeighbor i))).sum := by
      apply sum_ofFn_le
      intro i
      have hloc := hmax i
      cases hi : C i <;> cases hj : C (ring.rightNeighbor i) <;>
        simp_all [LocallyMaximal, uBit, sBit]
    _ = (List.ofFn fun i => sBit (C i)).sum :=
      sum_ofFn_rightNeighbor ring (fun i => sBit (C i))

/-- Every terminal abstract state matches at least one third of its defects:
`3 * |M| >= m`. -/
theorem three_mul_pairCount_ge
    (ring : DirectedRing m) (hm : 1 < m) (C : Configuration m)
    (hterm : Terminal ring C) :
    m ≤ 3 * pairCount C := by
  have hmax := (terminal_iff_maximalMatching ring hm C).mp hterm
  have hpart := role_count_partition C
  have heq := pairCount_eq_targetCount_of_maximal ring C hmax
  have hle := unmatchedCount_le_pairCount_of_maximal ring C hmax
  omega

private theorem term_le_sum_ofFn (f : Fin m → Nat) (j : Fin m) :
    f j ≤ (List.ofFn f).sum := by
  induction m with
  | zero => exact Fin.elim0 j
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons]
      by_cases hj0 : j = 0
      · subst j
        omega
      · have hjpos : 0 < j.val := by
          have hjne : j.val ≠ 0 := by
            intro h
            apply hj0
            apply Fin.ext
            simpa using h
          omega
        let j' : Fin m := ⟨j.val - 1, by omega⟩
        have hjsucc : j'.succ = j := by
          apply Fin.ext
          change j.val - 1 + 1 = j.val
          omega
        have ht := ih (fun i : Fin m => f i.succ) j'
        rw [hjsucc] at ht
        omega

theorem invalidGap_eq_zero_iff (a b : Role) :
    invalidGap a b = 0 ↔ (a = .S ↔ b = .T) := by
  cases a <;> cases b <;> simp [invalidGap]

/-- `I=0` is exactly the condition that every `S` and `T` belongs to a valid
adjacent pair. -/
theorem invalidCount_eq_zero_iff (ring : DirectedRing m) (C : Configuration m) :
    invalidCount ring C = 0 ↔
      ∀ e, C e = .S ↔ C (ring.rightNeighbor e) = .T := by
  constructor
  · intro hzero e
    apply (invalidGap_eq_zero_iff _ _).mp
    have hle := term_le_sum_ofFn
      (fun j => invalidGap (C j) (C (ring.rightNeighbor j))) e
    unfold invalidCount at hzero
    omega
  · intro hall
    unfold invalidCount
    calc
      (List.ofFn fun e =>
          invalidGap (C e) (C (ring.rightNeighbor e))).sum =
          (List.ofFn fun _ : Fin m => 0).sum := by
        apply sum_ofFn_eq
        intro e
        exact (invalidGap_eq_zero_iff _ _).mpr (hall e)
      _ = 0 := by simpa using sum_ofFn_const m 0

/-- The number of enabled repair edges is literally `I`.  Under a uniform
`m`-edge scheduler, a state with `I=r` therefore has repair probability `r/m`.
The probabilistic coupon calculation is intentionally left to the consumer. -/
theorem repairEdgeCount_eq_invalidCount
    (ring : DirectedRing m) (C : Configuration m) :
    repairEdgeCount ring C = invalidCount ring C := by
  unfold repairEdgeCount invalidCount
  apply sum_ofFn_eq
  intro e
  exact repairBit_eq_invalidGap _ _

/-- Once `I=0`, the changing selected gaps are exactly the `U,U` gaps. -/
theorem changingEdgeCount_eq_unmatchedEdgeCount_of_invalid_zero
    (ring : DirectedRing m) (C : Configuration m)
    (hzero : invalidCount ring C = 0) :
    changingEdgeCount ring C = unmatchedEdgeCount ring C := by
  unfold changingEdgeCount unmatchedEdgeCount
  apply sum_ofFn_eq
  intro e
  apply changingBit_eq_uuGap_of_invalid_zero
  have hle := term_le_sum_ofFn
    (fun j => invalidGap (C j) (C (ring.rightNeighbor j))) e
  unfold invalidCount at hzero
  omega

/-- Selecting any `U,U` gap lowers the total number of `U,U` gaps by at least
one.  Neighboring `U,U` gaps may disappear at the same time, so equality is not
claimed. -/
theorem unmatchedEdgeCount_step_match (ring : DirectedRing m) (hm : 1 < m)
    (C : Configuration m) (e : Fin m)
    (hmatch : action (C e) (C (ring.rightNeighbor e)) = .match) :
    unmatchedEdgeCount ring (step ring C e) + 1 ≤
      unmatchedEdgeCount ring C := by
  let before : Fin m → Nat := fun i =>
    uuGap (C i) (C (ring.rightNeighbor i))
  let after : Fin m → Nat := fun i =>
    uuGap (step ring C e i)
      (step ring C e (ring.rightNeighbor i))
  let removed : Fin m → Nat := fun i => if i = e then 0 else before i
  have hroles := (action_eq_match_iff _ _).mp hmatch
  have hbefore : before e = 1 := by
    simp [before, hroles.1, hroles.2, uuGap]
  have hafter : after e = 0 := by
    simp [after, step_at_left, step_at_right ring hm,
      hroles.1, hroles.2, pairStep, uuGap]
  have hremoved : removed e = 0 := by simp [removed]
  have hbalance := sum_ofFn_balance_one before removed e (by
    intro i hie
    simp [removed, hie])
  have hsumle : (List.ofFn after).sum ≤ (List.ofFn removed).sum := by
    apply sum_ofFn_le
    intro i
    by_cases hie : i = e
    · subst i
      simp [hafter, hremoved]
    · rw [show removed i = before i by simp [removed, hie]]
      exact uuGap_step_match_le ring hm C e i hmatch
  unfold unmatchedEdgeCount
  change (List.ofFn after).sum + 1 ≤ (List.ofFn before).sum
  omega

/-- The zero-invalid phase is closed under every abstract step. -/
theorem invalidCount_step_eq_zero (ring : DirectedRing m) (hm : 1 < m)
    (C : Configuration m) (e : Fin m)
    (hzero : invalidCount ring C = 0) :
    invalidCount ring (step ring C e) = 0 := by
  by_cases hrepair : action (C e) (C (ring.rightNeighbor e)) = .repair
  · have hdrop := invalidCount_step_repair ring hm C e hrepair
    omega
  · rw [invalidCount_step_nonrepair ring hm C e hrepair, hzero]

/-- Terminality decomposes into zero invalid roles and absence of an unmatched
adjacent pair.  This is the operational meaning of the two terms of `F`. -/
theorem terminal_iff_invalid_zero_and_no_UU
    (ring : DirectedRing m) (hm : 1 < m) (C : Configuration m) :
    Terminal ring C ↔
      invalidCount ring C = 0 ∧
        ∀ e, ¬(C e = .U ∧ C (ring.rightNeighbor e) = .U) := by
  rw [terminal_iff_maximalMatching ring hm C]
  constructor
  · intro hmax
    constructor
    · apply (invalidCount_eq_zero_iff ring C).mpr
      exact fun e => (hmax e).1
    · exact fun e => (hmax e).2
  · rintro ⟨hzero, hUU⟩ e
    exact ⟨(invalidCount_eq_zero_iff ring C).mp hzero e, hUU e⟩

/-! ## Abstract matched-gap contraction -/

/-- Sum of the currently assigned matched gaps.  Matched gaps are disjoint in
the intended consumer, so their initial sum is at most the physical ring size. -/
def gapPotential (gaps : List Nat) : Nat := gaps.sum

/-- One useful service contracts exactly one positive matched gap by one.  A
`1 -> 0` step is the charged merge event for that pair. -/
inductive GapStep : List Nat → List Nat → Prop where
  | contract (pre post : List Nat) (d : Nat) (hd : 0 < d) :
      GapStep (pre ++ d :: post) (pre ++ (d - 1) :: post)

/-- Every useful service lowers `Psi` by exactly one, stated without truncated
subtraction. -/
theorem GapStep.potential_balance {before after : List Nat}
    (h : GapStep before after) :
    gapPotential after + 1 = gapPotential before := by
  cases h with
  | contract pre post d hd =>
      simp [gapPotential, List.sum_append]
      omega

theorem GapStep.potential_strict {before after : List Nat}
    (h : GapStep before after) :
    gapPotential after < gapPotential before := by
  have := h.potential_balance
  omega

/-- A length-indexed sequence of useful gap services. -/
inductive GapRun : Nat → List Nat → List Nat → Prop where
  | nil (gaps : List Nat) : GapRun 0 gaps gaps
  | cons {k : Nat} {a b c : List Nat} :
      GapStep a b → GapRun k b c → GapRun (k + 1) a c

/-- After `k` useful services, `Psi` has fallen by exactly `k`. -/
theorem GapRun.potential_balance {k : Nat} {before after : List Nat}
    (h : GapRun k before after) :
    gapPotential after + k = gapPotential before := by
  induction h with
  | nil => simp
  | @cons k a b c hab hbc ih =>
      have hstep := hab.potential_balance
      omega

/-- Disjoint matched gaps of total length at most `n` can receive at most `n`
useful services before all charged merges. -/
theorem GapRun.length_le_physical_size {k n : Nat}
    {before after : List Nat} (h : GapRun k before after)
    (hbudget : gapPotential before ≤ n) : k ≤ n := by
  have hbal := h.potential_balance
  omega

/-- Converting at most `n` useful services, each costing at most `n` raw edge
selections, costs at most `n^2`.  Scheduler waiting-time hypotheses belong to
the consumer that establishes the per-service bound. -/
theorem raw_cost_le_square {services n : Nat} (h : services ≤ n) :
    n * services ≤ n * n := Nat.mul_le_mul_left n h

/-- Removing `p` disjoint adjacent matched pairs from support `m`, when
`p >= m/3`, leaves support at most two thirds in subtraction-free form. -/
theorem support_contracts_by_third {m p : Nat}
    (hp : p ≤ m) (hthird : m ≤ 3 * p) :
    3 * (m - p) ≤ 2 * m := by
  omega

/-- Deterministic interface consumed by the future literal trail compiler.
It records only facts that must be supplied for one contraction epoch; it does
not assume or manufacture an implementation. -/
structure ContractionEpochCertificate (physicalSize support pairs services : Nat) : Prop where
  pairs_le_support : pairs ≤ support
  maximal_density : support ≤ 3 * pairs
  assigned_gap_budget : services ≤ physicalSize

theorem ContractionEpochCertificate.support_after_bound
    {physicalSize support pairs services : Nat}
    (cert : ContractionEpochCertificate physicalSize support pairs services) :
    3 * (support - pairs) ≤ 2 * support :=
  support_contracts_by_third cert.pairs_le_support cert.maximal_density

theorem ContractionEpochCertificate.raw_service_cost_bound
    {physicalSize support pairs services : Nat}
    (cert : ContractionEpochCertificate physicalSize support pairs services) :
    physicalSize * services ≤ physicalSize * physicalSize :=
  raw_cost_le_square cert.assigned_gap_budget

end PairedDefectMatching

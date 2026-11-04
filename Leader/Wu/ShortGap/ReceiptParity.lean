import Leader.Wu.ShortGap.DenialTransport

/-!
# Receipt currentness across a gap: one-bit parity tags on the token walk

This file is the **currentness quotient for one round** of the short-gap
rearm service.  It refines the stop-and-wait token walk of
`Leader/Wu/ShortGap/DenialTransport.lean` by tagging the single in-flight carrier
of a gap with a one-bit round parity and letting the two roots of the gap
authenticate what arrives at them.

**Model.**  A gap is a directed physical path of length `h ≥ 1` between a left
root at position `0` and a right root at position `h`, with physical edges
`edgeAt 0, …, edgeAt (h-1)` exactly as in the transport file.  Both roots hold
the same round bit `round : Bool`, fixed for the whole duration of the rearm
service (the round bit changes only when both roots rearm, outside this file).
The carrier is a `GapDenialState h` together with a `tag : Bool`:

* `declareRight k` with tag `t`: the left root's declaration, stamped `t`, at
  position `k < h`, moving clockwise.
* `denyLeft k` with tag `t` (`1 ≤ k ≤ h`): a leftward token stamped `t`.  If
  `t = round` it is the current denial receipt; if `t ≠ round` it is a stale
  denial left over from the previous round or the reject echo described below.
* `denyLeft 0`: the gap is discharged; the tag is irrelevant there.

A token is *stale* when its tag differs from `round`.  Staleness enters only
through the initial state: the service may start with one stale token
per gap, of either kind, at any position.  The root rules are:

* **Right root** (arrival of `declareRight (h-1)` across `edgeAt (h-1)`): if
  the tag is current, the comparison returns the denial `denyLeft h` with the
  current tag.  If the tag is stale the declaration is discarded and *echoed
  back* as a reject token `denyLeft h` carrying the same stale tag.  This is
  the design choice made here (rather than silently dropping the token or
  teleporting the gap back to `declareRight 0`), because it keeps every
  transition radius one: the left root learns about the rejection only when
  the echo physically reaches it.  Both outcomes preserve the tag, so the
  right root's rule is "answer with the tag you received".
* **Left root** (arrival of `denyLeft 1` across `edgeAt 0`): the receipt is
  **accepted** and the gap discharged iff the tag equals `round`; otherwise
  the token is **discarded** and the left root re-emits its current
  declaration `declareRight 0` with tag `round`.

Exactly one scheduler edge advances the carrier of an active gap; all other
edges leave it unchanged.  `m` gaps run together on `n` scheduler edges through
the injective `GapLayout` of the transport file, each with its own round bit.

**Results.**

* `TaggedGapState.accepted_receipt_current`: a root never accepts a stale
  denial — every accepted receipt carries the current tag.  The statement is
  not vacuous: `TaggedGapState.accepts_denyLeft_one` exhibits an accepting
  transition, and `TaggedGapState.not_accepts_of_stale` is the contrapositive.
* `TaggedGapState.wasted_advance_le`: no transition creates a stale token, so
  a stale token wastes at most one extra round trip (`2*h` hops).
* The potential `n * Σ_g (hops + 2*h*wasted)` is a scale-one
  `NatBellmanSuperSolution`; every gap has work at most `4*h`, the worst case
  being a stale declaration at position `0` (`2*h` wasted plus `2*h` fresh).
  A clean start costs `n*(m*(2*h))`, the all-stale start `n*(m*(4*h))`, and
  every admissible start is at most `n*(m*(4*h))`.
* Through `CandidateRearmSpec` the complete candidate process with parity
  authenticated rearm has truncated expected-work numerator at most
  `n^T * (2*(n*m)*(1+2*h))` from any admissible rearm start, and
  `n^T * (2*(n*m)*(1+h))` from the clean start.

**Relation to the tag-free design.**  The tag is not the only way to get
currentness, and this file does not claim it is the right one.  The companion
paper design (`TWO_DENIAL_LITERAL_CARRIER.md` §1.4) argues that currentness is
already structural: the owner cannot change its choice while its port is
blocked waiting, and the right root cannot compare a new declaration while its
port still holds the previous result, so no epoch tag is needed at all — and a
1-bit parity buys nothing against *forgery*, since an adversary picks the
parity of a forged token freely.  An independent analysis of the same
question argues the other way for a different failure mode: if the left root
may rearm into a new round before the right root does, a mixed-round
comparison becomes possible and one generation bit is what separates the
rounds.  The two arguments are about different hypotheses (port blocking held
versus roots rearming out of step), and this file settles neither: it
formalizes the tagged variant only, and the tag-free variant is a separate
obligation.  Note in particular that `round : Fin m → Bool` gives *both* roots
of a gap the one bit `round g`, so a mixed-round comparison is not
representable in this model at all: the tag is formalized here, but it is not
shown to solve the failure mode that motivates it.

**Abstraction boundary.**  This file models one stale token per gap of either
kind, one-bit parity tags, and round bits that are fixed during the service.
It does **not** model arbitrary forged residue (more than one garbage token
per gap, or garbage sitting in interior slots alongside the live carrier), the
round bit flipping while a token is in flight, serializer or abort debt, or
the shared-root two-receipt join of `Leader/Wu/ShortGap/TwoDenialRearm.lean`.  The
two roots of a gap are assumed to hold equal round bits; the comparison
outcome is fixed to a denial as in the transport file.  Nothing here claims
complete leader stabilization or a final complexity bound.
-/

namespace ShortGapReceiptParity

open FiniteUniformStoppingTree
open PeriodHIncidenceChoice
open ShortGapChoiceStopping
open ShortGapDenialTransport

set_option autoImplicit false

private theorem ofFn_sum_lt_of_single_lt
    {n : Nat} (f g : Fin n → Nat) (chosen : Fin n)
    (hle : ∀ i, f i ≤ g i) (hlt : f chosen < g chosen) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction n with
  | zero => exact Fin.elim0 chosen
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      by_cases hzero : chosen = 0
      · subst chosen
        have htail := ofFn_sum_le
          (fun i : Fin n => f i.succ) (fun i => g i.succ)
          (fun i => hle i.succ)
        omega
      · have hpos : 0 < chosen.val := by
          have hne : chosen.val ≠ 0 :=
            fun h => hzero (Fin.ext (by simpa using h))
          omega
        let previous : Fin n := ⟨chosen.val - 1, by omega⟩
        have hsucc : previous.succ = chosen :=
          Fin.ext (by simp [previous]; omega)
        have htail := ih
          (fun i : Fin n => f i.succ) (fun i => g i.succ) previous
          (fun i => hle i.succ) (by simpa only [hsucc] using hlt)
        have hhead := hle 0
        omega

/-! ## One gap with a tagged carrier -/

/-- Carrier phase/position together with the parity tag stamped on the
in-flight token.  At `denyLeft 0` (discharged) the tag is irrelevant. -/
structure TaggedGapState (h : Nat) where
  carrier : GapDenialState h
  tag : Bool

namespace TaggedGapState

variable {h : Nat}

/-- Remaining carrier hops of the token currently in flight. -/
def hops (s : TaggedGapState h) : Nat := s.carrier.hops

/-- `1` iff an in-flight token is stale (tag differs from the round bit). -/
def wasted (round : Bool) (s : TaggedGapState h) : Nat :=
  if s.carrier.hops = 0 then 0 else if s.tag = round then 0 else 1

/-- Remaining work: the hops of the token in flight plus, if that token is
stale, the `2*h` hops of the fresh declaration/denial round trip that will
follow its rejection. -/
def work (round : Bool) (s : TaggedGapState h) : Nat :=
  s.carrier.hops + 2 * h * wasted round s

/-! ### Closed forms of `wasted` and `work` on each carrier shape

Unfolding `wasted` at a state whose carrier is a concrete constructor rewrites
the `if`-condition `s.carrier.hops = 0` but leaves its `Decidable` instance
phrased in the unreduced form, which blocks later `rw`s.  The following closed
forms discharge that condition once, with freshly elaborated instances, so
every case analysis below is pure arithmetic in `if tag = round then 0 else 1`.
-/

private theorem wasted_declareRight (round tag : Bool) (k : Nat) (hk : k < h) :
    wasted round (⟨.declareRight k hk, tag⟩ : TaggedGapState h) =
      if tag = round then 0 else 1 := by
  have hne : h - k + h ≠ 0 := by omega
  show (if h - k + h = 0 then 0 else if tag = round then 0 else 1) =
    if tag = round then 0 else 1
  rw [if_neg hne]

private theorem wasted_denyLeft (round tag : Bool) (j : Nat) (hk : j ≤ h)
    (hj : j ≠ 0) :
    wasted round (⟨.denyLeft j hk, tag⟩ : TaggedGapState h) =
      if tag = round then 0 else 1 := by
  show (if j = 0 then 0 else if tag = round then 0 else 1) =
    if tag = round then 0 else 1
  rw [if_neg hj]

private theorem wasted_denyLeft_zero (round tag : Bool) (hk : (0 : Nat) ≤ h) :
    wasted round (⟨.denyLeft 0 hk, tag⟩ : TaggedGapState h) = 0 := by
  show (if (0 : Nat) = 0 then 0 else if tag = round then 0 else 1) = 0
  simp

private theorem work_declareRight (round tag : Bool) (k : Nat) (hk : k < h) :
    work round (⟨.declareRight k hk, tag⟩ : TaggedGapState h) =
      h - k + h + 2 * h * (if tag = round then 0 else 1) := by
  have hne : h - k + h ≠ 0 := by omega
  show h - k + h +
      2 * h * (if h - k + h = 0 then 0 else if tag = round then 0 else 1) =
    h - k + h + 2 * h * (if tag = round then 0 else 1)
  rw [if_neg hne]

private theorem work_denyLeft (round tag : Bool) (j : Nat) (hk : j ≤ h)
    (hj : j ≠ 0) :
    work round (⟨.denyLeft j hk, tag⟩ : TaggedGapState h) =
      j + 2 * h * (if tag = round then 0 else 1) := by
  show j + 2 * h * (if j = 0 then 0 else if tag = round then 0 else 1) =
    j + 2 * h * (if tag = round then 0 else 1)
  rw [if_neg hj]

private theorem work_denyLeft_zero (round tag : Bool) (hk : (0 : Nat) ≤ h) :
    work round (⟨.denyLeft 0 hk, tag⟩ : TaggedGapState h) = 0 := by
  show (0 : Nat) +
    2 * h * (if (0 : Nat) = 0 then 0 else if tag = round then 0 else 1) = 0
  simp

/-- The unique gap edge whose scheduling advances the carrier, if any. -/
def advanceEdge (s : TaggedGapState h) : Option (Fin h) :=
  s.carrier.advanceEdge

/-- Effect of scheduling the advancing edge.  The right root answers a
declaration with a leftward token of the same tag (current: denial; stale:
reject echo).  The left root accepts a leftward token iff its tag is current;
otherwise it discards the token and re-declares with the current tag. -/
def advance (round : Bool) : TaggedGapState h → TaggedGapState h
  | ⟨.declareRight k hk, tag⟩ =>
      if hk' : k + 1 < h then ⟨.declareRight (k + 1) hk', tag⟩
      else ⟨.denyLeft h (Nat.le_refl h), tag⟩
  | ⟨.denyLeft 0 hk, tag⟩ => ⟨.denyLeft 0 hk, tag⟩
  | ⟨.denyLeft (k + 1) hk, tag⟩ =>
      if hk0 : k = 0 then
        (if tag = round then ⟨.denyLeft 0 (Nat.zero_le h), tag⟩
          else ⟨.declareRight 0 (by omega), round⟩)
      else ⟨.denyLeft k (by omega), tag⟩

theorem hops_le (s : TaggedGapState h) : s.carrier.hops ≤ 2 * h := by
  cases s.carrier with
  | declareRight k hk => simp only [GapDenialState.hops]; omega
  | denyLeft k hk => simp only [GapDenialState.hops]; omega

theorem wasted_le_one (round : Bool) (s : TaggedGapState h) :
    wasted round s ≤ 1 := by
  unfold wasted
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · exact Nat.le_refl _

/-- Every admissible gap state has at most `4*h` remaining work: one wasted
traversal of at most `2*h` hops plus one fresh round trip of `2*h` hops. -/
theorem work_le (round : Bool) (s : TaggedGapState h) :
    work round s ≤ 4 * h := by
  have h1 := hops_le s
  have h2 : 2 * h * wasted round s ≤ 2 * h := by
    have := Nat.mul_le_mul_left (2 * h) (wasted_le_one round s)
    simpa using this
  unfold work
  omega

theorem advanceEdge_of_hops_pos (s : TaggedGapState h)
    (hpos : 0 < s.carrier.hops) : ∃ a, s.advanceEdge = some a :=
  GapDenialState.advanceEdge_of_hops_pos s.carrier hpos

/-- **Safety.**  Acceptance event: an in-flight token is absorbed into the
discharged state by one advance of the carrier. -/
def accepts (round : Bool) (s : TaggedGapState h) : Prop :=
  0 < s.carrier.hops ∧ (advance round s).carrier.hops = 0

/-- A root never accepts a stale denial receipt: whenever one advance
discharges the gap, the absorbed token carries the current round tag. -/
theorem accepted_receipt_current (round : Bool) (s : TaggedGapState h)
    (hacc : accepts round s) : s.tag = round := by
  obtain ⟨hpos, hzero⟩ := hacc
  obtain ⟨c, tag⟩ := s
  cases c with
  | declareRight k hk =>
      exfalso
      simp only [advance] at hzero
      split at hzero
      · simp only [GapDenialState.hops] at hzero
        omega
      · simp only [GapDenialState.hops] at hzero
        omega
  | denyLeft k hk =>
      cases k with
      | zero => simp [GapDenialState.hops] at hpos
      | succ k =>
          simp only [advance] at hzero
          by_cases hk0 : k = 0
          · rw [dif_pos hk0] at hzero
            by_cases ht : tag = round
            · exact ht
            · rw [if_neg ht] at hzero
              simp only [GapDenialState.hops] at hzero
              omega
          · rw [dif_neg hk0] at hzero
            simp only [GapDenialState.hops] at hzero
            omega

/-- A stale token is never accepted; contrapositive of the safety lemma. -/
theorem not_accepts_of_stale (round : Bool) (s : TaggedGapState h)
    (ht : s.tag ≠ round) : ¬ accepts round s :=
  fun hacc => ht (accepted_receipt_current round s hacc)

/-- The safety statement is not vacuous: the current denial one hop from the
left root really is accepted. -/
theorem accepts_denyLeft_one (round : Bool) (hk : 1 ≤ h) :
    accepts round (⟨.denyLeft 1 hk, round⟩ : TaggedGapState h) := by
  refine ⟨by show 0 < 1; omega, ?_⟩
  cases round <;> rfl

/-- No transition creates a stale token: the waste indicator never
increases, so a stale token costs at most one wasted round trip (`2*h` hops). -/
theorem wasted_advance_le (round : Bool) (s : TaggedGapState h) :
    wasted round (advance round s) ≤ wasted round s := by
  obtain ⟨c, tag⟩ := s
  cases c with
  | declareRight k hk =>
      have hh : h ≠ 0 := by omega
      simp only [advance]
      split
      · apply Nat.le_of_eq
        rw [wasted_declareRight, wasted_declareRight]
      · apply Nat.le_of_eq
        rw [wasted_denyLeft round tag h (Nat.le_refl h) hh, wasted_declareRight]
  | denyLeft k hk =>
      cases k with
      | zero =>
          simp only [advance]
          exact Nat.le_refl _
      | succ k =>
          simp only [advance]
          by_cases hk0 : k = 0
          · rw [dif_pos hk0]
            by_cases ht : tag = round
            · rw [if_pos ht, wasted_denyLeft_zero]
              exact Nat.zero_le _
            · rw [if_neg ht, wasted_declareRight,
                if_pos (rfl : round = round)]
              exact Nat.zero_le _
          · rw [dif_neg hk0]
            apply Nat.le_of_eq
            rw [wasted_denyLeft round tag k (by omega) hk0,
              wasted_denyLeft round tag (k + 1) hk (by omega)]

/-- The advancing edge lowers the remaining work by exactly one.  In the
reject case at the left root, `1 + 2*h` (last stale hop plus the reserved
fresh round trip) becomes `2*h` (the fresh declaration at position `0`). -/
theorem work_advance_of_some (round : Bool) (s : TaggedGapState h)
    (a : Fin h) (ha : s.advanceEdge = some a) :
    (advance round s).work round + 1 = s.work round := by
  obtain ⟨c, tag⟩ := s
  cases c with
  | declareRight k hk =>
      have hh : h ≠ 0 := by omega
      simp only [advance]
      split
      · rename_i hk'
        rw [work_declareRight, work_declareRight]
        split <;> omega
      · rename_i hk'
        rw [work_denyLeft round tag h (Nat.le_refl h) hh, work_declareRight]
        split <;> omega
  | denyLeft k hk =>
      cases k with
      | zero => simp [advanceEdge, GapDenialState.advanceEdge] at ha
      | succ k =>
          simp only [advance]
          by_cases hk0 : k = 0
          · rw [dif_pos hk0]
            by_cases ht : tag = round
            · rw [if_pos ht, work_denyLeft_zero,
                work_denyLeft round tag (k + 1) hk (by omega), if_pos ht]
              omega
            · rw [if_neg ht, work_declareRight,
                work_denyLeft round tag (k + 1) hk (by omega),
                if_pos (rfl : round = round), if_neg ht]
              omega
          · rw [dif_neg hk0, work_denyLeft round tag k (by omega) hk0,
              work_denyLeft round tag (k + 1) hk (by omega)]
            split <;> omega

/-- One scheduler edge acting on one gap whose physical edges are `edgeAt`. -/
def localStep {n : Nat} (edgeAt : Fin h → Fin n) (round : Bool)
    (s : TaggedGapState h) (e : Fin n) : TaggedGapState h :=
  match s.advanceEdge with
  | some a => if edgeAt a = e then advance round s else s
  | none => s

theorem work_localStep_le {n : Nat} (edgeAt : Fin h → Fin n) (round : Bool)
    (s : TaggedGapState h) (e : Fin n) :
    (localStep edgeAt round s e).work round ≤ s.work round := by
  unfold localStep
  split
  · rename_i a ha
    split
    · have := work_advance_of_some round s a ha
      omega
    · exact Nat.le_refl _
  · exact Nat.le_refl _

theorem localStep_advanceEdge {n : Nat} (edgeAt : Fin h → Fin n)
    (round : Bool) (s : TaggedGapState h) (a : Fin h)
    (ha : s.advanceEdge = some a) :
    localStep edgeAt round s (edgeAt a) = advance round s := by
  simp [localStep, ha]

theorem work_localStep_advance {n : Nat} (edgeAt : Fin h → Fin n)
    (round : Bool) (s : TaggedGapState h) (a : Fin h)
    (ha : s.advanceEdge = some a) :
    (localStep edgeAt round s (edgeAt a)).work round + 1 = s.work round := by
  rw [localStep_advanceEdge edgeAt round s a ha]
  exact work_advance_of_some round s a ha

/-- Every edge other than the advancing edge leaves the gap unchanged. -/
theorem localStep_eq_of_ne {n : Nat} (edgeAt : Fin h → Fin n) (round : Bool)
    (s : TaggedGapState h) (e : Fin n)
    (hne : ∀ a, s.advanceEdge = some a → edgeAt a ≠ e) :
    localStep edgeAt round s e = s := by
  unfold localStep
  split
  · rename_i a ha
    rw [if_neg (hne a ha)]
  · rfl

/-- Work of a fresh declaration at the left root: one round trip. -/
theorem work_cleanDeclare (round : Bool) (hpos : 0 < h) :
    work round (⟨.declareRight 0 hpos, round⟩ : TaggedGapState h) = 2 * h := by
  rw [work_declareRight, if_pos (rfl : round = round)]
  omega

/-- Work of a stale declaration at the left root: one wasted round trip
(walk right, be rejected, echo walks back) plus one fresh round trip. -/
theorem work_staleDeclare (round : Bool) (hpos : 0 < h) :
    work round (⟨.declareRight 0 hpos, !round⟩ : TaggedGapState h) = 4 * h := by
  have h2 : (!round) ≠ round := by cases round <;> decide
  rw [work_declareRight, if_neg h2]
  omega

end TaggedGapState

/-! ## `m` gaps on disjoint edge sets, each with its own round bit -/

/-- Joint tagged carrier state with at least one gap still in transit. -/
structure TaggedMultiGapState (h m : Nat) where
  gap : Fin m → TaggedGapState h
  hasActive : ∃ g, 0 < (gap g).carrier.hops

/-- Total remaining work over all gaps. -/
def totalWork {h m : Nat} (round : Fin m → Bool)
    (gap : Fin m → TaggedGapState h) : Nat :=
  (List.ofFn (fun g => (gap g).work (round g))).sum

/-- One scheduler edge acting on every gap through its own edge set. -/
def multiLocalStep {n h m : Nat} (L : GapLayout n h m) (round : Fin m → Bool)
    (gap : Fin m → TaggedGapState h) (e : Fin n) :
    Fin m → TaggedGapState h :=
  fun g => TaggedGapState.localStep (L.edgeAt g) (round g) (gap g) e

theorem totalWork_multiLocalStep_le {n h m : Nat} (L : GapLayout n h m)
    (round : Fin m → Bool) (gap : Fin m → TaggedGapState h) (e : Fin n) :
    totalWork round (multiLocalStep L round gap e) ≤ totalWork round gap :=
  ofFn_sum_le _ _
    (fun g => TaggedGapState.work_localStep_le (L.edgeAt g) (round g) (gap g) e)

/-- The advancing edge of any in-transit gap strictly lowers the total. -/
theorem totalWork_multiLocalStep_lt {n h m : Nat} (L : GapLayout n h m)
    (round : Fin m → Bool) (gap : Fin m → TaggedGapState h) (g : Fin m)
    (a : Fin h) (ha : (gap g).advanceEdge = some a) :
    totalWork round (multiLocalStep L round gap (L.edgeAt g a)) <
      totalWork round gap := by
  apply ofFn_sum_lt_of_single_lt _ _ g
  · intro g'
    exact TaggedGapState.work_localStep_le (L.edgeAt g') (round g') (gap g') _
  · have := TaggedGapState.work_localStep_advance
      (L.edgeAt g) (round g) (gap g) a ha
    show (multiLocalStep L round gap (L.edgeAt g a) g).work (round g) <
      (gap g).work (round g)
    simp only [multiLocalStep]
    omega

/-- A gap's advancing edge leaves every other gap unchanged. -/
theorem multiLocalStep_other {n h m : Nat} (L : GapLayout n h m)
    (round : Fin m → Bool) (gap : Fin m → TaggedGapState h) (g g' : Fin m)
    (hne : g' ≠ g) (a : Fin h) :
    multiLocalStep L round gap (L.edgeAt g a) g' = gap g' := by
  apply TaggedGapState.localStep_eq_of_ne
  intro a' _ heq
  exact hne (L.edgeAt_injective g' a' g a heq).1

/-- The parity-authenticated rearm service stops only after every gap is
discharged. -/
noncomputable def taggedGapStep {n h m : Nat} (L : GapLayout n h m)
    (round : Fin m → Bool) :
    TaggedMultiGapState h m → Fin n → StopNode (TaggedMultiGapState h m) :=
  fun state edge =>
    let next := multiLocalStep L round state.gap edge
    if hnext : ∃ g, 0 < (next g).carrier.hops then
      .active ⟨next, hnext⟩
    else .success

def taggedGapPotential {n h m : Nat} (round : Fin m → Bool) :
    StopNode (TaggedMultiGapState h m) → Nat
  | .active state => n * totalWork round state.gap
  | .success => 0
  | .failure => 0

private theorem taggedGapPotential_step_le
    {n h m : Nat} (L : GapLayout n h m) (round : Fin m → Bool)
    (state : TaggedMultiGapState h m) (edge : Fin n) :
    taggedGapPotential (n := n) round (taggedGapStep L round state edge) ≤
      n * totalWork round (multiLocalStep L round state.gap edge) := by
  classical
  simp only [taggedGapStep]
  split <;> simp [taggedGapPotential]

/-- The exact child-sum inequality for remaining work. -/
theorem totalWork_childSum {n h m : Nat} (L : GapLayout n h m)
    (round : Fin m → Bool) (state : TaggedMultiGapState h m) :
    1 + (List.ofFn (fun edge : Fin n =>
      totalWork round (multiLocalStep L round state.gap edge))).sum ≤
        n * totalWork round state.gap := by
  obtain ⟨g, hg⟩ := state.hasActive
  obtain ⟨a, ha⟩ := TaggedGapState.advanceEdge_of_hops_pos _ hg
  have hsumlt := ofFn_sum_lt_of_single_lt
    (fun edge : Fin n => totalWork round (multiLocalStep L round state.gap edge))
    (fun _ : Fin n => totalWork round state.gap) (L.edgeAt g a)
    (fun edge => totalWork_multiLocalStep_le L round state.gap edge)
    (totalWork_multiLocalStep_lt L round state.gap g a ha)
  rw [ofFn_sum_const] at hsumlt
  omega

/-- The parity-authenticated rearm service has expected work at most `n`
times the initial total work (hops plus reserved fresh round trips). -/
theorem taggedGap_natBellmanSuperSolution
    {n h m : Nat} (L : GapLayout n h m) (round : Fin m → Bool) :
    NatBellmanSuperSolution (taggedGapStep L round) 1
      (taggedGapPotential (n := n) round) := by
  refine ⟨rfl, rfl, ?_⟩
  intro state
  have hdebt := totalWork_childSum L round state
  have hscaled := Nat.mul_le_mul_left n hdebt
  have hchildren :
      (List.ofFn (fun edge : Fin n =>
        taggedGapPotential (n := n) round (taggedGapStep L round state edge))).sum ≤
        n * (List.ofFn (fun edge : Fin n =>
          totalWork round (multiLocalStep L round state.gap edge))).sum := by
    calc
      (List.ofFn (fun edge : Fin n =>
          taggedGapPotential (n := n) round
            (taggedGapStep L round state edge))).sum ≤
        (List.ofFn (fun edge : Fin n =>
          n * totalWork round (multiLocalStep L round state.gap edge))).sum := by
            apply ofFn_sum_le
            intro edge
            exact taggedGapPotential_step_le L round state edge
      _ = n * (List.ofFn (fun edge : Fin n =>
          totalWork round (multiLocalStep L round state.gap edge))).sum :=
        ofFn_sum_mul_left n _
  calc
    1 * n + (List.ofFn (fun edge : Fin n =>
        taggedGapPotential (n := n) round (taggedGapStep L round state edge))).sum ≤
      n + n * (List.ofFn (fun edge : Fin n =>
        totalWork round (multiLocalStep L round state.gap edge))).sum := by
          simpa using Nat.add_le_add_left hchildren n
    _ = n * (1 + (List.ofFn (fun edge : Fin n =>
        totalWork round (multiLocalStep L round state.gap edge))).sum) := by
      rw [Nat.mul_add, Nat.mul_one]
    _ ≤ n * (n * totalWork round state.gap) := hscaled
    _ = n * taggedGapPotential (n := n) round (.active state) := rfl

theorem taggedGapStep_ne_failure {n h m : Nat} (L : GapLayout n h m)
    (round : Fin m → Bool) :
    ∀ state edge, taggedGapStep L round state edge ≠ .failure := by
  classical
  intro state edge
  simp only [taggedGapStep]
  split <;> simp

/-! ### Start states -/

/-- Clean start: every left root's fresh declaration at position `0`. -/
def cleanDeclareStart {n h m : Nat} (L : GapLayout n h m)
    (round : Fin m → Bool) (hm : 0 < m) : TaggedMultiGapState h m :=
  ⟨fun g => ⟨.declareRight 0 L.hpos, round g⟩,
    ⟨⟨0, hm⟩, by
      have := L.hpos
      simp only [GapDenialState.hops]
      omega⟩⟩

/-- Worst-case start: every gap holds a stale declaration (wrong parity) at
position `0`, which must walk to the right root, be rejected, echo back, and
only then be replaced by the fresh declaration. -/
def staleDeclareStart {n h m : Nat} (L : GapLayout n h m)
    (round : Fin m → Bool) (hm : 0 < m) : TaggedMultiGapState h m :=
  ⟨fun g => ⟨.declareRight 0 L.hpos, !round g⟩,
    ⟨⟨0, hm⟩, by
      have := L.hpos
      simp only [GapDenialState.hops]
      omega⟩⟩

@[simp] theorem totalWork_cleanDeclare {h m : Nat} (round : Fin m → Bool)
    (hpos : 0 < h) :
    totalWork round (fun g : Fin m =>
      (⟨.declareRight 0 hpos, round g⟩ : TaggedGapState h)) = m * (2 * h) := by
  simp only [totalWork, TaggedGapState.work_cleanDeclare, ofFn_sum_const]

@[simp] theorem totalWork_staleDeclare {h m : Nat} (round : Fin m → Bool)
    (hpos : 0 < h) :
    totalWork round (fun g : Fin m =>
      (⟨.declareRight 0 hpos, !round g⟩ : TaggedGapState h)) = m * (4 * h) := by
  simp only [totalWork, TaggedGapState.work_staleDeclare, ofFn_sum_const]

/-- Every admissible start (one token per gap, stale or not) has total work
at most `m * (4*h)`. -/
theorem totalWork_le {h m : Nat} (round : Fin m → Bool)
    (gap : Fin m → TaggedGapState h) :
    totalWork round gap ≤ m * (4 * h) := by
  unfold totalWork
  rw [← ofFn_sum_const m (4 * h)]
  exact ofFn_sum_le _ _ (fun g => TaggedGapState.work_le (round g) (gap g))

@[simp] theorem taggedGapPotential_cleanDeclare
    {n h m : Nat} (L : GapLayout n h m) (round : Fin m → Bool) (hm : 0 < m) :
    taggedGapPotential (n := n) round (.active (cleanDeclareStart L round hm)) =
      n * (m * (2 * h)) := by
  simp [taggedGapPotential, cleanDeclareStart]

@[simp] theorem taggedGapPotential_staleDeclare
    {n h m : Nat} (L : GapLayout n h m) (round : Fin m → Bool) (hm : 0 < m) :
    taggedGapPotential (n := n) round (.active (staleDeclareStart L round hm)) =
      n * (m * (4 * h)) := by
  simp [taggedGapPotential, staleDeclareStart]

theorem taggedGapPotential_active_le
    {n h m : Nat} (round : Fin m → Bool) (state : TaggedMultiGapState h m) :
    taggedGapPotential (n := n) round (.active state) ≤ n * (m * (4 * h)) :=
  Nat.mul_le_mul_left n (totalWork_le round state.gap)

/-! ### Composition with the candidate round -/

/-- Parity-authenticated token-walk implementation of the candidate rearm
interface for `m` gaps of physical length `h` on disjoint edge sets, from an
arbitrary admissible start (one token per gap, possibly stale). -/
noncomputable def taggedGapDenialRearmSpec
    {n h m : Nat} (L : GapLayout n h m) (round : Fin m → Bool)
    (start : TaggedMultiGapState h m) : CandidateRearmSpec n where
  State := TaggedMultiGapState h m
  step := taggedGapStep L round
  start := start
  potential := taggedGapPotential (n := n) round
  bellman := taggedGap_natBellmanSuperSolution L round
  noFailure := taggedGapStep_ne_failure L round

/-- Complete candidate process with parity-authenticated token-walk rearm. -/
noncomputable def taggedGapCandidateRestartStep
    {n h m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (L : GapLayout n h m) (round : Fin m → Bool)
    (start : TaggedMultiGapState h m) (hm : 0 < m) :=
  (taggedGapDenialRearmSpec L round start).restartStep ring P hm

private theorem stale_budget_eq (n h m : Nat) :
    2 * (n * m) * (1 + 2 * h) = 2 * (n * m) + n * (m * (4 * h)) := by
  rw [Nat.mul_add, Nat.mul_one]
  have hswap : n * (m * (4 * h)) = 2 * (n * m) * (2 * h) := by
    rw [show 4 * h = 2 * (2 * h) by omega]
    ac_rfl
  rw [hswap]

private theorem clean_budget_eq (n h m : Nat) :
    2 * (n * m) * (1 + h) = 2 * (n * m) + n * (m * (2 * h)) := by
  rw [Nat.mul_add, Nat.mul_one]
  have hswap : n * (m * (2 * h)) = 2 * (n * m) * h := by ac_rfl
  rw [hswap]

/-- **Capstone.**  From any admissible rearm start (one token per gap, of
either kind and either parity), repeated candidate rounds with
parity-authenticated token-walk rearm have expected work at most
`2*n*m*(1+2*h)`: `2*n*m` for the balanced candidate round, `2*n*m*h` for one
possibly wasted round trip (`2*h` hops) per gap, and `2*n*m*h` for the fresh round trip. -/
theorem taggedGapCandidateRestart_truncatedCost_le
    {n h m : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (L : GapLayout n h m)
    (round : Fin m → Bool) (start : TaggedMultiGapState h m) (T : Nat) :
    truncatedActiveCostNumerator
        (taggedGapCandidateRestartStep ring P L round start (by omega))
        (.active (.round (allRaceCandidateDrainState ring (by omega)))) T ≤
      n ^ T * (2 * (n * m) * (1 + 2 * h)) := by
  have hcost :=
    (taggedGapDenialRearmSpec L round start).allRace_truncatedCost_le
      ring hm P hn T
  simp only [taggedGapCandidateRestartStep, taggedGapDenialRearmSpec] at hcost ⊢
  rw [stale_budget_eq]
  refine Nat.le_trans hcost (Nat.mul_le_mul_left _ ?_)
  exact Nat.add_le_add_left (taggedGapPotential_active_le round start) _

/-- The all-stale start is the worst admissible start, and it saturates the
potential bound `n*(m*(4*h))` used in the budget `2*n*m*(1+2*h)`. -/
theorem taggedGapCandidateRestart_staleStart_truncatedCost_le
    {n h m : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (L : GapLayout n h m)
    (round : Fin m → Bool) (T : Nat) :
    truncatedActiveCostNumerator
        (taggedGapCandidateRestartStep ring P L round
          (staleDeclareStart L round (by omega)) (by omega))
        (.active (.round (allRaceCandidateDrainState ring (by omega)))) T ≤
      n ^ T * (2 * (n * m) * (1 + 2 * h)) :=
  taggedGapCandidateRestart_truncatedCost_le ring hm P hn L round _ T

/-- The clean start matches the untagged transport bound `2*n*m*(1+h)`
numerically (no reduction of the tagged process to the untagged one is
proved). -/
theorem taggedGapCandidateRestart_cleanStart_truncatedCost_le
    {n h m : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (L : GapLayout n h m)
    (round : Fin m → Bool) (T : Nat) :
    truncatedActiveCostNumerator
        (taggedGapCandidateRestartStep ring P L round
          (cleanDeclareStart L round (by omega)) (by omega))
        (.active (.round (allRaceCandidateDrainState ring (by omega)))) T ≤
      n ^ T * (2 * (n * m) * (1 + h)) := by
  have hcost :=
    (taggedGapDenialRearmSpec L round
      (cleanDeclareStart L round (by omega))).allRace_truncatedCost_le
      ring hm P hn T
  simp only [taggedGapCandidateRestartStep, taggedGapDenialRearmSpec,
    taggedGapPotential_cleanDeclare] at hcost ⊢
  rw [clean_budget_eq]
  exact hcost

/-- Exact reciprocal success tail for the all-stale start. -/
theorem taggedGapCandidateRestart_staleStart_success_one_minus_inv_factor
    {n h m factor : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (L : GapLayout n h m)
    (round : Fin m → Bool) :
    (factor - 1) * n ^ (factor * (2 * (n * m) * (1 + 2 * h))) ≤
      factor * successCount
        (taggedGapCandidateRestartStep ring P L round
          (staleDeclareStart L round (by omega)) (by omega))
        (.active (.round (allRaceCandidateDrainState ring (by omega))))
        (factor * (2 * (n * m) * (1 + 2 * h))) := by
  have hsuccess :=
    CandidateRearmSpec.allRace_success_one_minus_inv_factor
      (taggedGapDenialRearmSpec L round (staleDeclareStart L round (by omega)))
      ring hm P hn (factor := factor)
  simp only [taggedGapCandidateRestartStep, taggedGapDenialRearmSpec,
    taggedGapPotential_staleDeclare] at hsuccess ⊢
  rw [stale_budget_eq]
  exact hsuccess

#print axioms TaggedGapState.accepted_receipt_current
#print axioms TaggedGapState.wasted_advance_le
#print axioms TaggedGapState.work_advance_of_some
#print axioms taggedGap_natBellmanSuperSolution
#print axioms taggedGapCandidateRestart_truncatedCost_le
#print axioms taggedGapCandidateRestart_staleStart_success_one_minus_inv_factor

end ShortGapReceiptParity

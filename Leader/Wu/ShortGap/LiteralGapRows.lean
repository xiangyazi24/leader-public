import Leader.Core.FiniteUniformStoppingTree

/-!
# Literal radius-one rows of ONE gap, as a pair-transition table

This file formalizes the *literal* row table of `TWO_DENIAL_LITERAL_CARRIER.md`
Section 1 for a **single** gap of a directed ring, together with the service
debt `δ` of Section 3.2 and the three Bellman facts of Section 3.3 restricted
to that one gap.

**What is literal here.**  The per-agent state is the paper's state: a root
carries `ch ∈ {race, out1, in0}`, a clockwise port `cw ∈ {toSend, waiting,
heldDenial, heldCandidate}` and a counterclockwise port `ccw ∈ {free,
heldDenial, heldCandidate}`; an interior agent carries one slot
`∈ {empty, decl c, reply d}`.  The transition `row : Agent → Agent →
Agent × Agent` rewrites BOTH endpoints of a scheduled directed edge
(`Leader/Core/Basic.lean` convention: the pair is `(initiator, responder)` and the
transition returns both new states), and implements the fourteen paper rows
`L1 … P3` across fourteen constructor-disjoint pair equations, several rows
being folded into one equation through `resolveInit`/`resolveResp` (see the
table header below); the remaining equations are the identity for this layer.
`res c d = heldCandidate` iff `(c, d) = (out1, in0)`, else `heldDenial`, for
both port types; it is factored through a two-valued `Verdict` so that the
owner's `cw` receipt and the right root's `ccw` receipt are two renderings of
one verdict.

**Scope and abstraction boundary (read this before reusing anything).**

* ONE gap only.  Positions are `Fin (h+1)` with `0` the owner (left root),
  `h` the right root and `1, …, h-1` the interior agents; gap edge `j : Fin h`
  joins positions `j` and `j+1`.  For `h = 1` the single edge is
  `(left, right)` and the `RR` rows apply.
* NO JOIN.  The post-step join of Section 1.2 needs the *neighbouring* gap's
  receipt, so in this single-gap file the owner's `cw ∈ {heldDenial,
  heldCandidate}` is TERMINAL: no row of `row` ever writes a held `cw` back to
  `toSend` and no row writes `ch := race`.  Consequently there is no rearm, no
  second round, and no pipelining here.
* Clean lane only.  `Clean` is the paper's clean-state predicate (a) pre-launch,
  (b) declaration in flight, (c) reply in flight, (d) delivered, specialised to
  one gap with the owner's `ccw` field and the right root's `cw` field framed
  at arbitrary fixed values `ccw0`, `cw0`.  The dirty rows `L3`, `V2`, `P3` are
  defined (the table is total) but are never exercised from a clean state; the
  same holds for the incidence rows `L2`, `K2`, `K4`, `P2`, which need a `race`
  root and clean states have none.
* NO shared-root composition: the neighbouring gap that shares the right root
  is absent, so the "one firing changes exactly one `δ`" argument of
  Section 3.4 is not reproved here.
* NO claim about stabilization, about the whole `m`-gap service, or about a
  final complexity bound.  The only quantitative output is the one-gap Bellman
  supersolution with start potential `n * (2*h - 1)`.

**Result.**  Rows preserve `Clean` for every scheduler edge (`clean_step`); the
debt `δ` of Section 3.2 (`2h-1`, `2h-1-j`, `j`, `0`) never increases
(`delta_step_le`) and the unique useful edge lowers it by exactly one
(`delta_useful_lt`); hence `n * δ` is a `NatBellmanSuperSolution` with scale
`1` on the active part of the subtype `{cfg // Clean cfg}`
(`gap_natBellmanSuperSolution`), starting at `n * (2*h - 1)`.  Authentication:
the owner holds its declared choice `c` in every clean state
(`owner_choice_held`) and in the delivered state its `cw` receipt is the `cw`
rendering of the same verdict `res c d` whose `ccw` rendering the right root
holds (`owner_receipt_eq_right_result`).
-/

namespace ShortGapLiteralGapRows

open FiniteUniformStoppingTree

set_option autoImplicit false

/-! ## Finite uniform sum helpers -/

private theorem ofFn_sum_eq_zero : ∀ {N : Nat} (f : Fin N → Nat),
    (∀ k, f k = 0) → (List.ofFn f).sum = 0 := by
  intro N
  induction N with
  | zero => intro f _; simp
  | succ N ih =>
      intro f hz
      rw [List.ofFn_succ, List.sum_cons, hz 0,
        ih (fun k => f k.succ) (fun k => hz k.succ)]

private theorem ofFn_sum_single : ∀ {N : Nat} (f : Fin N → Nat) (i : Fin N),
    (∀ k, k ≠ i → f k = 0) → (List.ofFn f).sum = f i := by
  intro N
  induction N with
  | zero => intro _ i _; exact Fin.elim0 i
  | succ N ih =>
      intro f i hz
      rw [List.ofFn_succ, List.sum_cons]
      by_cases h0 : i.val = 0
      · have hi : (0 : Fin (N + 1)) = i := Fin.ext (by simp [h0])
        have htail : (List.ofFn (fun k : Fin N => f k.succ)).sum = 0 := by
          apply ofFn_sum_eq_zero
          intro k
          apply hz
          intro hk
          have hv := congrArg Fin.val hk
          simp only [Fin.val_succ] at hv
          omega
        rw [htail, hi]
        simp
      · have hlt : i.val < N + 1 := i.isLt
        have hipos : 0 < i.val := Nat.pos_of_ne_zero h0
        have hprev : i.val - 1 < N := by omega
        have hsucc : (⟨i.val - 1, hprev⟩ : Fin N).succ = i :=
          Fin.ext (by simp only [Fin.val_succ]; omega)
        have hhead : f 0 = 0 := by
          apply hz
          intro hk
          apply h0
          rw [← hk]
          simp
        have htail : (List.ofFn (fun k : Fin N => f k.succ)).sum =
            f (⟨i.val - 1, hprev⟩ : Fin N).succ := by
          apply ih
          intro k hk
          apply hz
          intro hki
          apply hk
          apply Fin.ext
          have hv := congrArg Fin.val hki
          simp only [Fin.val_succ] at hv
          simp only []
          omega
        rw [hhead, htail, hsucc]
        simp

private theorem ofFn_sum_lt_of_single_lt
    {N : Nat} (f g : Fin N → Nat) (chosen : Fin N)
    (hle : ∀ i, f i ≤ g i) (hlt : f chosen < g chosen) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction N with
  | zero => exact Fin.elim0 chosen
  | succ N ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      by_cases hzero : chosen = 0
      · subst chosen
        have htail := ofFn_sum_le
          (fun i : Fin N => f i.succ) (fun i => g i.succ)
          (fun i => hle i.succ)
        omega
      · have hpos : 0 < chosen.val := by
          have hne : chosen.val ≠ 0 :=
            fun h => hzero (Fin.ext (by simpa using h))
          omega
        have hprev : chosen.val - 1 < N := by
          have := chosen.isLt
          omega
        have hsucc : (⟨chosen.val - 1, hprev⟩ : Fin N).succ = chosen :=
          Fin.ext (by simp only [Fin.val_succ]; omega)
        have htail := ih
          (fun i : Fin N => f i.succ) (fun i => g i.succ)
          ⟨chosen.val - 1, hprev⟩
          (fun i => hle i.succ) (by simpa only [hsucc] using hlt)
        have hhead := hle 0
        omega

/-! ## Per-agent state (Section 1.1) -/

/-- The incidence choice held by a root. -/
inductive Choice where
  | race
  | out1
  | in0
  deriving DecidableEq

/-- The clockwise port of a root (the gap it owns). -/
inductive CwPort where
  | toSend
  | waiting
  | heldDenial
  | heldCandidate
  deriving DecidableEq

/-- The counterclockwise port of a root (the gap in which it is right root). -/
inductive CcwPort where
  | free
  | heldDenial
  | heldCandidate
  deriving DecidableEq

/-- The single message slot of an interior agent. -/
inductive Slot where
  | empty
  | decl (c : Choice)
  | reply (d : Choice)
  deriving DecidableEq

/-- A per-agent state of the carrier layer. -/
inductive Agent where
  | root (ch : Choice) (cw : CwPort) (ccw : CcwPort)
  | interior (slot : Slot)
  deriving DecidableEq

/-- The outcome of one endpoint comparison. -/
inductive Verdict where
  | denial
  | candidate
  deriving DecidableEq

/-- `res c d` of the paper: a candidate iff the owner declared `out1` and the
right root declared `in0`; a denial otherwise. -/
def res (c d : Choice) : Verdict :=
  if c = Choice.out1 ∧ d = Choice.in0 then Verdict.candidate else Verdict.denial

/-- The clockwise-port rendering of a verdict (the owner's receipt). -/
def Verdict.cw : Verdict → CwPort
  | .denial => .heldDenial
  | .candidate => .heldCandidate

/-- The counterclockwise-port rendering of a verdict (the right root's
receipt). -/
def Verdict.ccw : Verdict → CcwPort
  | .denial => .heldDenial
  | .candidate => .heldCandidate

/-- `res` as a clockwise port value. -/
def resCw (c d : Choice) : CwPort := (res c d).cw

/-- `res` as a counterclockwise port value. -/
def resCcw (c d : Choice) : CcwPort := (res c d).ccw

theorem Verdict.cw_ne_toSend (v : Verdict) : v.cw ≠ CwPort.toSend := by
  cases v <;> simp [Verdict.cw]

theorem Verdict.cw_ne_waiting (v : Verdict) : v.cw ≠ CwPort.waiting := by
  cases v <;> simp [Verdict.cw]

theorem Verdict.ccw_ne_free (v : Verdict) : v.ccw ≠ CcwPort.free := by
  cases v <;> simp [Verdict.ccw]

theorem resCw_ne_toSend (c d : Choice) : resCw c d ≠ CwPort.toSend :=
  Verdict.cw_ne_toSend _

theorem resCw_ne_waiting (c d : Choice) : resCw c d ≠ CwPort.waiting :=
  Verdict.cw_ne_waiting _

theorem resCcw_ne_free (c d : Choice) : resCcw c d ≠ CcwPort.free :=
  Verdict.ccw_ne_free _

/-- The incidence resolution of an initiator: a `race` root becomes `out1`. -/
def resolveInit (ch : Choice) : Choice :=
  if ch = Choice.race then Choice.out1 else ch

/-- The incidence resolution of a responder: a `race` root becomes `in0`. -/
def resolveResp (ch : Choice) : Choice :=
  if ch = Choice.race then Choice.in0 else ch

/-- A frozen (non-`race`) choice. -/
def IsBase (c : Choice) : Prop := c = Choice.out1 ∨ c = Choice.in0

theorem resolveInit_of_base {c : Choice} (h : IsBase c) : resolveInit c = c := by
  rcases h with h | h <;> subst h <;> simp [resolveInit]

theorem resolveResp_of_base {c : Choice} (h : IsBase c) : resolveResp c = c := by
  rcases h with h | h <;> subst h <;> simp [resolveResp]

/-! ## Optional field readers -/

/-- The held choice of a root. -/
def Agent.choice : Agent → Option Choice
  | .root ch _ _ => some ch
  | .interior _ => none

/-- The clockwise port of a root. -/
def Agent.cwPort : Agent → Option CwPort
  | .root _ cw _ => some cw
  | .interior _ => none

/-- The counterclockwise port of a root. -/
def Agent.ccwPort : Agent → Option CcwPort
  | .root _ _ ccw => some ccw
  | .interior _ => none

/-! ## The row table (Section 1.3)

The fourteen paper rows, written as constructor-disjoint defining equations of
one pair transition.  The initiator is the left endpoint of the scheduled
directed edge and the responder is the right endpoint; the transition returns
both new states.  Rows that the paper writes with a `race` side condition are
folded into `resolveInit` / `resolveResp`, which are the identity on frozen
choices, so e.g. the single `root × interior-empty` equation is `L1` when the
owner is frozen and `L2` when it is racing.
-/

/-- The literal radius-one row table of one gap.

* `root × interior empty` : `L1` (launch, frozen owner) and `L2` (incidence +
  launch, racing owner); a no-op when the owner's `cw ≠ toSend`.
* `root × interior decl`  : `L3` (dirty: incidence only) and otherwise a no-op.
* `root × interior reply` : `V1` (deliver the receipt to the owner) when
  `cw = waiting`; `V2` (dirty: erase an orphan reply, plus `L3` incidence when
  `cw = toSend`) otherwise.
* `interior decl × root`  : `K1` (compare) and `K2` (incidence + compare) when
  the right root's `ccw = free`; `K3` (wait) otherwise.
* `interior empty × root`, `interior reply × root` : `K4` (incidence only).
* `interior decl × interior empty` : `F1` (clockwise hop).
* `interior empty × interior reply` : `B1` (counterclockwise pull).
* `root × root` (`h = 1`) : `P1` (launch + compare + deliver atomically),
  `P2` (incidence only, right root still holds), `P3` (dirty).

Every other interior/interior pattern is a no-op for this layer. -/
def row : Agent → Agent → Agent × Agent
  -- L1 / L2
  | .root ch cw ccw, .interior .empty =>
      if cw = CwPort.toSend then
        (.root (resolveInit ch) CwPort.waiting ccw,
          .interior (Slot.decl (resolveInit ch)))
      else (.root ch cw ccw, .interior .empty)
  -- L3 (dirty)
  | .root ch cw ccw, .interior (.decl c0) =>
      if cw = CwPort.toSend then
        (.root (resolveInit ch) cw ccw, .interior (Slot.decl c0))
      else (.root ch cw ccw, .interior (Slot.decl c0))
  -- V1 / V2 (V2 dirty)
  | .root ch cw ccw, .interior (.reply d) =>
      if cw = CwPort.waiting then
        (.root ch (resCw ch d) ccw, .interior Slot.empty)
      else if cw = CwPort.toSend then
        (.root (resolveInit ch) cw ccw, .interior Slot.empty)
      else (.root ch cw ccw, .interior Slot.empty)
  -- K1 / K2 / K3
  | .interior (.decl c0), .root ch cw ccw =>
      if ccw = CcwPort.free then
        (.interior (Slot.reply (resolveResp ch)),
          .root (resolveResp ch) cw (resCcw c0 (resolveResp ch)))
      else (.interior (Slot.decl c0), .root ch cw ccw)
  -- K4
  | .interior .empty, .root ch cw ccw =>
      (.interior Slot.empty, .root (resolveResp ch) cw ccw)
  -- K4
  | .interior (.reply d), .root ch cw ccw =>
      (.interior (Slot.reply d), .root (resolveResp ch) cw ccw)
  -- interior / interior
  | .interior .empty, .interior .empty =>
      (.interior Slot.empty, .interior Slot.empty)
  | .interior .empty, .interior (.decl c1) =>
      (.interior Slot.empty, .interior (Slot.decl c1))
  -- B1
  | .interior .empty, .interior (.reply d) =>
      (.interior (Slot.reply d), .interior Slot.empty)
  -- F1
  | .interior (.decl c0), .interior .empty =>
      (.interior Slot.empty, .interior (Slot.decl c0))
  | .interior (.decl c0), .interior (.decl c1) =>
      (.interior (Slot.decl c0), .interior (Slot.decl c1))
  | .interior (.decl c0), .interior (.reply d) =>
      (.interior (Slot.decl c0), .interior (Slot.reply d))
  | .interior (.reply d0), .interior t =>
      (.interior (Slot.reply d0), .interior t)
  -- P1 / P2 / P3
  | .root ch cw ccw, .root ch' cw' ccw' =>
      if cw = CwPort.toSend then
        if ccw' = CcwPort.free then
          (.root (resolveInit ch)
              (resCw (resolveInit ch) (resolveResp ch')) ccw,
            .root (resolveResp ch') cw'
              (resCcw (resolveInit ch) (resolveResp ch')))
        else (.root (resolveInit ch) cw ccw, .root ch' cw' ccw')
      else
        if ccw' = CcwPort.free then
          (.root (resolveInit ch) cw ccw, .root (resolveResp ch') cw' ccw')
        else (.root (resolveInit ch) cw ccw, .root ch' cw' ccw')

/-! ## One gap as a configuration on `Fin (h+1)` -/

/-- The static data of one gap: its physical length `h ≥ 1`, the owner's
frozen choice `c`, the right root's frozen choice `d`, and the two framed
fields (`ccw0`, the owner's counterclockwise port, which belongs to the
previous gap; `cw0`, the right root's clockwise port, which belongs to the
next gap). -/
structure Frame where
  h : Nat
  hpos : 0 < h
  c : Choice
  d : Choice
  hc : IsBase c
  hd : IsBase d
  ccw0 : CcwPort
  cw0 : CwPort

/-- A configuration of one gap: position `0` is the owner (left root),
position `h` is the right root, positions `1, …, h-1` are interior. -/
abbrev Config (F : Frame) := Fin (F.h + 1) → Agent

/-- Position of the owner. -/
def leftPos (F : Frame) : Fin (F.h + 1) := ⟨0, Nat.succ_pos _⟩

/-- Position of the right root. -/
def rightPos (F : Frame) : Fin (F.h + 1) := ⟨F.h, Nat.lt_succ_self _⟩

/-- Initiator (left endpoint) of gap edge `j`. -/
def leftEnd (F : Frame) (j : Fin F.h) : Fin (F.h + 1) :=
  ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩

/-- Responder (right endpoint) of gap edge `j`. -/
def rightEnd (F : Frame) (j : Fin F.h) : Fin (F.h + 1) :=
  ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩

/-- Scheduling gap edge `j`: apply `row` to the two endpoints and update
exactly those two positions. -/
def gapStep (F : Frame) (cfg : Config F) (j : Fin F.h) : Config F :=
  fun k =>
    if k.val = j.val then (row (cfg (leftEnd F j)) (cfg (rightEnd F j))).1
    else if k.val = j.val + 1 then (row (cfg (leftEnd F j)) (cfg (rightEnd F j))).2
    else cfg k

theorem gapStep_id (F : Frame) (cfg : Config F) (j : Fin F.h)
    (hrow : row (cfg (leftEnd F j)) (cfg (rightEnd F j))
      = (cfg (leftEnd F j), cfg (rightEnd F j))) :
    gapStep F cfg j = cfg := by
  funext k
  simp only [gapStep, hrow]
  by_cases h1 : k.val = j.val
  · rw [if_pos h1]
    exact congrArg cfg (Fin.ext (show (leftEnd F j).val = k.val from h1.symm))
  · rw [if_neg h1]
    by_cases h2 : k.val = j.val + 1
    · rw [if_pos h2]
      exact congrArg cfg (Fin.ext (show (rightEnd F j).val = k.val from h2.symm))
    · rw [if_neg h2]

/-! ## The clean lane (Section 3.1) -/

/-- The four clean phases of one gap. -/
inductive Phase where
  /-- (a) pre-launch. -/
  | prelaunch
  /-- (b) the owner's declaration sits at interior position `j`. -/
  | declAt (j : Nat)
  /-- (c) the right root's reply sits at interior position `j`. -/
  | replyAt (j : Nat)
  /-- (d) the owner has received its receipt. -/
  | delivered
  deriving DecidableEq

/-- Index ranges of a phase: the token position of (b) and (c) is an interior
position. -/
def PhaseOk (F : Frame) : Phase → Prop
  | .prelaunch => True
  | .declAt j => 1 ≤ j ∧ j < F.h
  | .replyAt j => 1 ≤ j ∧ j < F.h
  | .delivered => True

/-- The state of the agent at position `k` in a clean phase. -/
def siteOf (F : Frame) : Phase → Nat → Agent
  | .prelaunch, k =>
      if k = 0 then .root F.c CwPort.toSend F.ccw0
      else if k = F.h then .root F.d F.cw0 CcwPort.free
      else .interior Slot.empty
  | .declAt j, k =>
      if k = 0 then .root F.c CwPort.waiting F.ccw0
      else if k = F.h then .root F.d F.cw0 CcwPort.free
      else if k = j then .interior (Slot.decl F.c)
      else .interior Slot.empty
  | .replyAt j, k =>
      if k = 0 then .root F.c CwPort.waiting F.ccw0
      else if k = F.h then .root F.d F.cw0 (resCcw F.c F.d)
      else if k = j then .interior (Slot.reply F.d)
      else .interior Slot.empty
  | .delivered, k =>
      if k = 0 then .root F.c (resCw F.c F.d) F.ccw0
      else if k = F.h then .root F.d F.cw0 (resCcw F.c F.d)
      else .interior Slot.empty

/-- The configuration of a clean phase. -/
def configOf (F : Frame) (p : Phase) : Config F := fun k => siteOf F p k.val

theorem configOf_apply (F : Frame) (p : Phase) (k : Fin (F.h + 1)) :
    configOf F p k = siteOf F p k.val := rfl

theorem configOf_leftEnd (F : Frame) (p : Phase) (j : Fin F.h) :
    configOf F p (leftEnd F j) = siteOf F p j.val := rfl

theorem configOf_rightEnd (F : Frame) (p : Phase) (j : Fin F.h) :
    configOf F p (rightEnd F j) = siteOf F p (j.val + 1) := rfl

/-! ### Pointwise readback of `siteOf` -/

theorem siteOf_prelaunch_zero (F : Frame) :
    siteOf F Phase.prelaunch 0 = Agent.root F.c CwPort.toSend F.ccw0 := by
  rfl

theorem siteOf_prelaunch_last (F : Frame) (k : Nat) (h0 : k ≠ 0) (hh : k = F.h) :
    siteOf F Phase.prelaunch k = Agent.root F.d F.cw0 CcwPort.free := by
  simp only [siteOf, if_neg h0, if_pos hh]

theorem siteOf_prelaunch_mid (F : Frame) (k : Nat) (h0 : k ≠ 0) (hh : k ≠ F.h) :
    siteOf F Phase.prelaunch k = Agent.interior Slot.empty := by
  simp only [siteOf, if_neg h0, if_neg hh]

theorem siteOf_declAt_zero (F : Frame) (j0 : Nat) :
    siteOf F (Phase.declAt j0) 0 = Agent.root F.c CwPort.waiting F.ccw0 := by
  rfl

theorem siteOf_declAt_last (F : Frame) (j0 k : Nat) (h0 : k ≠ 0) (hh : k = F.h) :
    siteOf F (Phase.declAt j0) k = Agent.root F.d F.cw0 CcwPort.free := by
  simp only [siteOf, if_neg h0, if_pos hh]

theorem siteOf_declAt_tok (F : Frame) (j0 k : Nat) (h0 : k ≠ 0) (hh : k ≠ F.h)
    (hj : k = j0) :
    siteOf F (Phase.declAt j0) k = Agent.interior (Slot.decl F.c) := by
  simp only [siteOf, if_neg h0, if_neg hh, if_pos hj]

theorem siteOf_declAt_mid (F : Frame) (j0 k : Nat) (h0 : k ≠ 0) (hh : k ≠ F.h)
    (hj : k ≠ j0) :
    siteOf F (Phase.declAt j0) k = Agent.interior Slot.empty := by
  simp only [siteOf, if_neg h0, if_neg hh, if_neg hj]

theorem siteOf_replyAt_zero (F : Frame) (j0 : Nat) :
    siteOf F (Phase.replyAt j0) 0 = Agent.root F.c CwPort.waiting F.ccw0 := by
  rfl

theorem siteOf_replyAt_last (F : Frame) (j0 k : Nat) (h0 : k ≠ 0) (hh : k = F.h) :
    siteOf F (Phase.replyAt j0) k
      = Agent.root F.d F.cw0 (resCcw F.c F.d) := by
  simp only [siteOf, if_neg h0, if_pos hh]

theorem siteOf_replyAt_tok (F : Frame) (j0 k : Nat) (h0 : k ≠ 0) (hh : k ≠ F.h)
    (hj : k = j0) :
    siteOf F (Phase.replyAt j0) k = Agent.interior (Slot.reply F.d) := by
  simp only [siteOf, if_neg h0, if_neg hh, if_pos hj]

theorem siteOf_replyAt_mid (F : Frame) (j0 k : Nat) (h0 : k ≠ 0) (hh : k ≠ F.h)
    (hj : k ≠ j0) :
    siteOf F (Phase.replyAt j0) k = Agent.interior Slot.empty := by
  simp only [siteOf, if_neg h0, if_neg hh, if_neg hj]

theorem siteOf_delivered_zero (F : Frame) :
    siteOf F Phase.delivered 0 = Agent.root F.c (resCw F.c F.d) F.ccw0 := by
  rfl

theorem siteOf_delivered_last (F : Frame) (k : Nat) (h0 : k ≠ 0) (hh : k = F.h) :
    siteOf F Phase.delivered k = Agent.root F.d F.cw0 (resCcw F.c F.d) := by
  simp only [siteOf, if_neg h0, if_pos hh]

theorem siteOf_delivered_mid (F : Frame) (k : Nat) (h0 : k ≠ 0) (hh : k ≠ F.h) :
    siteOf F Phase.delivered k = Agent.interior Slot.empty := by
  simp only [siteOf, if_neg h0, if_neg hh]

/-- The clean-state predicate of Section 3.1 for one gap.  Case (a) is
pre-launch, (b) is a declaration carrying the owner's frozen choice `c` with
the owner waiting, (c) is a reply carrying the right root's frozen choice `d`
with the owner waiting and the right root already holding `res c d`, and (d) is
the delivered state in which the owner holds `res c d` too. -/
inductive Clean (F : Frame) : Config F → Prop where
  | prelaunch : Clean F (configOf F Phase.prelaunch)
  | declAt (j : Nat) (h1 : 1 ≤ j) (h2 : j < F.h) :
      Clean F (configOf F (Phase.declAt j))
  | replyAt (j : Nat) (h1 : 1 ≤ j) (h2 : j < F.h) :
      Clean F (configOf F (Phase.replyAt j))
  | delivered : Clean F (configOf F Phase.delivered)

theorem Clean.exists_phase {F : Frame} {cfg : Config F} (h : Clean F cfg) :
    ∃ p : Phase, PhaseOk F p ∧ cfg = configOf F p := by
  cases h with
  | prelaunch => exact ⟨Phase.prelaunch, trivial, rfl⟩
  | declAt j h1 h2 => exact ⟨Phase.declAt j, ⟨h1, h2⟩, rfl⟩
  | replyAt j h1 h2 => exact ⟨Phase.replyAt j, ⟨h1, h2⟩, rfl⟩
  | delivered => exact ⟨Phase.delivered, trivial, rfl⟩

theorem Clean.of_phaseOk (F : Frame) (p : Phase) (hp : PhaseOk F p) :
    Clean F (configOf F p) := by
  cases p with
  | prelaunch => exact .prelaunch
  | declAt j => exact .declAt j hp.1 hp.2
  | replyAt j => exact .replyAt j hp.1 hp.2
  | delivered => exact .delivered

/-! ## The phase transition induced by the rows -/

/-- The phase reached by scheduling gap edge `j`.  Every edge other than the
unique useful edge of the phase is a no-op. -/
def nextPhase (F : Frame) : Phase → Fin F.h → Phase
  | .prelaunch, j =>
      if j.val = 0 then (if F.h = 1 then Phase.delivered else Phase.declAt 1)
      else Phase.prelaunch
  | .declAt j0, j =>
      if j.val = j0 then
        (if j0 + 1 = F.h then Phase.replyAt j0 else Phase.declAt (j0 + 1))
      else Phase.declAt j0
  | .replyAt j0, j =>
      if j.val + 1 = j0 then
        (if j0 = 1 then Phase.delivered else Phase.replyAt (j0 - 1))
      else Phase.replyAt j0
  | .delivered, _ => Phase.delivered

theorem nextPhase_phaseOk (F : Frame) (p : Phase) (hp : PhaseOk F p)
    (j : Fin F.h) : PhaseOk F (nextPhase F p j) := by
  have hjlt : j.val < F.h := j.isLt
  cases p with
  | prelaunch =>
      simp only [nextPhase]
      split
      · split
        · trivial
        · exact ⟨Nat.le_refl 1, by omega⟩
      · trivial
  | declAt j0 =>
      have h1 : 1 ≤ j0 := hp.1
      have h2 : j0 < F.h := hp.2
      simp only [nextPhase]
      split
      · split
        · exact ⟨h1, h2⟩
        · rename_i hc; exact ⟨by omega, by omega⟩
      · exact ⟨h1, h2⟩
  | replyAt j0 =>
      have h1 : 1 ≤ j0 := hp.1
      have h2 : j0 < F.h := hp.2
      simp only [nextPhase]
      split
      · split
        · trivial
        · rename_i hc; exact ⟨by omega, by omega⟩
      · exact ⟨h1, h2⟩
  | delivered => trivial

/-! ### Rows applied to each clean phase -/

theorem gapStep_prelaunch (F : Frame) (j : Fin F.h) :
    gapStep F (configOf F Phase.prelaunch) j
      = configOf F (nextPhase F Phase.prelaunch j) := by
  have hjlt : j.val < F.h := j.isLt
  have hhpos : 0 < F.h := F.hpos
  by_cases hj : j.val = 0
  · have hu : configOf F Phase.prelaunch (leftEnd F j)
        = Agent.root F.c CwPort.toSend F.ccw0 := by
      rw [configOf_leftEnd, hj, siteOf_prelaunch_zero]
    by_cases hh : F.h = 1
    · -- `P1`: the one-edge gap launches, compares and delivers atomically.
      have hv : configOf F Phase.prelaunch (rightEnd F j)
          = Agent.root F.d F.cw0 CcwPort.free := by
        rw [configOf_rightEnd]
        exact siteOf_prelaunch_last F _ (by omega) (by omega)
      have hrow : row (Agent.root F.c CwPort.toSend F.ccw0)
            (Agent.root F.d F.cw0 CcwPort.free)
          = (Agent.root F.c (resCw F.c F.d) F.ccw0,
             Agent.root F.d F.cw0 (resCcw F.c F.d)) := by
        simp [row, resolveInit_of_base F.hc, resolveResp_of_base F.hd]
      have hnext : nextPhase F Phase.prelaunch j = Phase.delivered := by
        simp [nextPhase, hj, hh]
      rw [hnext]
      funext k
      have hklt : k.val < F.h + 1 := k.isLt
      simp only [gapStep, hu, hv, hrow]
      by_cases hk0 : k.val = 0
      · rw [if_pos (by omega), configOf_apply, hk0, siteOf_delivered_zero]
      · rw [if_neg (by omega), if_pos (by omega), configOf_apply,
          siteOf_delivered_last F k.val (by omega) (by omega)]
    · -- `L1`: the owner launches its declaration into a long gap.
      have hh2 : 2 ≤ F.h := by omega
      have hv : configOf F Phase.prelaunch (rightEnd F j)
          = Agent.interior Slot.empty := by
        rw [configOf_rightEnd]
        exact siteOf_prelaunch_mid F _ (by omega) (by omega)
      have hrow : row (Agent.root F.c CwPort.toSend F.ccw0)
            (Agent.interior Slot.empty)
          = (Agent.root F.c CwPort.waiting F.ccw0,
             Agent.interior (Slot.decl F.c)) := by
        simp [row, resolveInit_of_base F.hc]
      have hnext : nextPhase F Phase.prelaunch j = Phase.declAt 1 := by
        simp [nextPhase, hj, hh]
      rw [hnext]
      funext k
      have hklt : k.val < F.h + 1 := k.isLt
      simp only [gapStep, hu, hv, hrow]
      by_cases hk0 : k.val = 0
      · rw [if_pos (by omega), configOf_apply, hk0, siteOf_declAt_zero]
      · by_cases hk1 : k.val = 1
        · rw [if_neg (by omega), if_pos (by omega), configOf_apply,
            siteOf_declAt_tok F 1 k.val (by omega) (by omega) (by omega)]
        · rw [if_neg (by omega), if_neg (by omega)]
          simp only [configOf_apply]
          by_cases hkh : k.val = F.h
          · rw [siteOf_prelaunch_last F k.val (by omega) hkh,
              siteOf_declAt_last F 1 k.val (by omega) hkh]
          · rw [siteOf_prelaunch_mid F k.val (by omega) hkh,
              siteOf_declAt_mid F 1 k.val (by omega) hkh (by omega)]
  · -- no useful edge: the gap is frozen.
    have hnext : nextPhase F Phase.prelaunch j = Phase.prelaunch := by
      simp [nextPhase, hj]
    rw [hnext]
    have hu : configOf F Phase.prelaunch (leftEnd F j)
        = Agent.interior Slot.empty := by
      rw [configOf_leftEnd]
      exact siteOf_prelaunch_mid F _ (by omega) (by omega)
    apply gapStep_id
    by_cases hh : j.val + 1 = F.h
    · have hv : configOf F Phase.prelaunch (rightEnd F j)
          = Agent.root F.d F.cw0 CcwPort.free := by
        rw [configOf_rightEnd]
        exact siteOf_prelaunch_last F _ (by omega) hh
      rw [hu, hv]
      simp [row, resolveResp_of_base F.hd]
    · have hv : configOf F Phase.prelaunch (rightEnd F j)
          = Agent.interior Slot.empty := by
        rw [configOf_rightEnd]
        exact siteOf_prelaunch_mid F _ (by omega) hh
      rw [hu, hv]
      simp [row]

theorem gapStep_declAt (F : Frame) (j0 : Nat) (hj1 : 1 ≤ j0) (hj2 : j0 < F.h)
    (j : Fin F.h) :
    gapStep F (configOf F (Phase.declAt j0)) j
      = configOf F (nextPhase F (Phase.declAt j0) j) := by
  have hjlt : j.val < F.h := j.isLt
  have hh2 : 2 ≤ F.h := by omega
  by_cases hj : j.val = j0
  · have hu : configOf F (Phase.declAt j0) (leftEnd F j)
        = Agent.interior (Slot.decl F.c) := by
      rw [configOf_leftEnd]
      exact siteOf_declAt_tok F j0 _ (by omega) (by omega) hj
    by_cases hc : j0 + 1 = F.h
    · -- `K1`: the right root compares and writes its receipt.
      have hv : configOf F (Phase.declAt j0) (rightEnd F j)
          = Agent.root F.d F.cw0 CcwPort.free := by
        rw [configOf_rightEnd]
        exact siteOf_declAt_last F j0 _ (by omega) (by omega)
      have hrow : row (Agent.interior (Slot.decl F.c))
            (Agent.root F.d F.cw0 CcwPort.free)
          = (Agent.interior (Slot.reply F.d),
             Agent.root F.d F.cw0 (resCcw F.c F.d)) := by
        simp [row, resolveResp_of_base F.hd]
      have hnext : nextPhase F (Phase.declAt j0) j = Phase.replyAt j0 := by
        simp [nextPhase, hj, hc]
      rw [hnext]
      funext k
      have hklt : k.val < F.h + 1 := k.isLt
      simp only [gapStep, hu, hv, hrow]
      by_cases hk : k.val = j.val
      · rw [if_pos hk, configOf_apply,
          siteOf_replyAt_tok F j0 k.val (by omega) (by omega) (by omega)]
      · rw [if_neg hk]
        by_cases hk2 : k.val = j.val + 1
        · rw [if_pos hk2, configOf_apply,
            siteOf_replyAt_last F j0 k.val (by omega) (by omega)]
        · rw [if_neg hk2]
          simp only [configOf_apply]
          by_cases hk0 : k.val = 0
          · rw [hk0, siteOf_declAt_zero, siteOf_replyAt_zero]
          · rw [siteOf_declAt_mid F j0 k.val hk0 (by omega) (by omega),
              siteOf_replyAt_mid F j0 k.val hk0 (by omega) (by omega)]
    · -- `F1`: the declaration hops one position clockwise.
      have hc2 : j0 + 1 < F.h := by omega
      have hv : configOf F (Phase.declAt j0) (rightEnd F j)
          = Agent.interior Slot.empty := by
        rw [configOf_rightEnd]
        exact siteOf_declAt_mid F j0 _ (by omega) (by omega) (by omega)
      have hrow : row (Agent.interior (Slot.decl F.c))
            (Agent.interior Slot.empty)
          = (Agent.interior Slot.empty, Agent.interior (Slot.decl F.c)) := by
        simp [row]
      have hnext : nextPhase F (Phase.declAt j0) j = Phase.declAt (j0 + 1) := by
        simp [nextPhase, hj, hc]
      rw [hnext]
      funext k
      have hklt : k.val < F.h + 1 := k.isLt
      simp only [gapStep, hu, hv, hrow]
      by_cases hk : k.val = j.val
      · rw [if_pos hk, configOf_apply,
          siteOf_declAt_mid F (j0 + 1) k.val (by omega) (by omega) (by omega)]
      · rw [if_neg hk]
        by_cases hk2 : k.val = j.val + 1
        · rw [if_pos hk2, configOf_apply,
            siteOf_declAt_tok F (j0 + 1) k.val (by omega) (by omega) (by omega)]
        · rw [if_neg hk2]
          simp only [configOf_apply]
          by_cases hk0 : k.val = 0
          · rw [hk0, siteOf_declAt_zero, siteOf_declAt_zero]
          · by_cases hkh : k.val = F.h
            · rw [siteOf_declAt_last F j0 k.val hk0 hkh,
                siteOf_declAt_last F (j0 + 1) k.val hk0 hkh]
            · rw [siteOf_declAt_mid F j0 k.val hk0 hkh (by omega),
                siteOf_declAt_mid F (j0 + 1) k.val hk0 hkh (by omega)]
  · -- no useful edge.
    have hnext : nextPhase F (Phase.declAt j0) j = Phase.declAt j0 := by
      simp [nextPhase, hj]
    rw [hnext]
    apply gapStep_id
    by_cases hk0 : j.val = 0
    · have hu : configOf F (Phase.declAt j0) (leftEnd F j)
          = Agent.root F.c CwPort.waiting F.ccw0 := by
        rw [configOf_leftEnd, hk0, siteOf_declAt_zero]
      by_cases he : j.val + 1 = j0
      · have hv : configOf F (Phase.declAt j0) (rightEnd F j)
            = Agent.interior (Slot.decl F.c) := by
          rw [configOf_rightEnd]
          exact siteOf_declAt_tok F j0 _ (by omega) (by omega) he
        rw [hu, hv]
        simp [row]
      · have hv : configOf F (Phase.declAt j0) (rightEnd F j)
            = Agent.interior Slot.empty := by
          rw [configOf_rightEnd]
          exact siteOf_declAt_mid F j0 _ (by omega) (by omega) he
        rw [hu, hv]
        simp [row]
    · have hu : configOf F (Phase.declAt j0) (leftEnd F j)
          = Agent.interior Slot.empty := by
        rw [configOf_leftEnd]
        exact siteOf_declAt_mid F j0 _ hk0 (by omega) hj
      by_cases hh : j.val + 1 = F.h
      · have hv : configOf F (Phase.declAt j0) (rightEnd F j)
            = Agent.root F.d F.cw0 CcwPort.free := by
          rw [configOf_rightEnd]
          exact siteOf_declAt_last F j0 _ (by omega) hh
        rw [hu, hv]
        simp [row, resolveResp_of_base F.hd]
      · by_cases he : j.val + 1 = j0
        · have hv : configOf F (Phase.declAt j0) (rightEnd F j)
              = Agent.interior (Slot.decl F.c) := by
            rw [configOf_rightEnd]
            exact siteOf_declAt_tok F j0 _ (by omega) hh he
          rw [hu, hv]
          simp [row]
        · have hv : configOf F (Phase.declAt j0) (rightEnd F j)
              = Agent.interior Slot.empty := by
            rw [configOf_rightEnd]
            exact siteOf_declAt_mid F j0 _ (by omega) hh he
          rw [hu, hv]
          simp [row]

theorem gapStep_replyAt (F : Frame) (j0 : Nat) (hj1 : 1 ≤ j0) (hj2 : j0 < F.h)
    (j : Fin F.h) :
    gapStep F (configOf F (Phase.replyAt j0)) j
      = configOf F (nextPhase F (Phase.replyAt j0) j) := by
  have hjlt : j.val < F.h := j.isLt
  have hh2 : 2 ≤ F.h := by omega
  by_cases hj : j.val + 1 = j0
  · by_cases hc : j0 = 1
    · -- `V1`: the owner receives its receipt.
      have hk0 : j.val = 0 := by omega
      have hu : configOf F (Phase.replyAt j0) (leftEnd F j)
          = Agent.root F.c CwPort.waiting F.ccw0 := by
        rw [configOf_leftEnd, hk0, siteOf_replyAt_zero]
      have hv : configOf F (Phase.replyAt j0) (rightEnd F j)
          = Agent.interior (Slot.reply F.d) := by
        rw [configOf_rightEnd]
        exact siteOf_replyAt_tok F j0 _ (by omega) (by omega) hj
      have hrow : row (Agent.root F.c CwPort.waiting F.ccw0)
            (Agent.interior (Slot.reply F.d))
          = (Agent.root F.c (resCw F.c F.d) F.ccw0,
             Agent.interior Slot.empty) := by
        simp [row]
      have hnext : nextPhase F (Phase.replyAt j0) j = Phase.delivered := by
        simp [nextPhase, hj, hc]
      rw [hnext]
      funext k
      have hklt : k.val < F.h + 1 := k.isLt
      simp only [gapStep, hu, hv, hrow]
      by_cases hk : k.val = j.val
      · rw [if_pos hk, configOf_apply, (by omega : k.val = 0),
          siteOf_delivered_zero]
      · rw [if_neg hk]
        by_cases hk2 : k.val = j.val + 1
        · rw [if_pos hk2, configOf_apply,
            siteOf_delivered_mid F k.val (by omega) (by omega)]
        · rw [if_neg hk2]
          simp only [configOf_apply]
          by_cases hkh : k.val = F.h
          · rw [siteOf_replyAt_last F j0 k.val (by omega) hkh,
              siteOf_delivered_last F k.val (by omega) hkh]
          · rw [siteOf_replyAt_mid F j0 k.val (by omega) hkh (by omega),
              siteOf_delivered_mid F k.val (by omega) hkh]
    · -- `B1`: the reply is pulled one position counterclockwise.
      have hc2 : 2 ≤ j0 := by omega
      have hu : configOf F (Phase.replyAt j0) (leftEnd F j)
          = Agent.interior Slot.empty := by
        rw [configOf_leftEnd]
        exact siteOf_replyAt_mid F j0 _ (by omega) (by omega) (by omega)
      have hv : configOf F (Phase.replyAt j0) (rightEnd F j)
          = Agent.interior (Slot.reply F.d) := by
        rw [configOf_rightEnd]
        exact siteOf_replyAt_tok F j0 _ (by omega) (by omega) hj
      have hrow : row (Agent.interior Slot.empty)
            (Agent.interior (Slot.reply F.d))
          = (Agent.interior (Slot.reply F.d), Agent.interior Slot.empty) := by
        simp [row]
      have hnext : nextPhase F (Phase.replyAt j0) j
          = Phase.replyAt (j0 - 1) := by
        simp [nextPhase, hj, hc]
      rw [hnext]
      funext k
      have hklt : k.val < F.h + 1 := k.isLt
      simp only [gapStep, hu, hv, hrow]
      by_cases hk : k.val = j.val
      · rw [if_pos hk, configOf_apply,
          siteOf_replyAt_tok F (j0 - 1) k.val (by omega) (by omega) (by omega)]
      · rw [if_neg hk]
        by_cases hk2 : k.val = j.val + 1
        · rw [if_pos hk2, configOf_apply,
            siteOf_replyAt_mid F (j0 - 1) k.val (by omega) (by omega) (by omega)]
        · rw [if_neg hk2]
          simp only [configOf_apply]
          by_cases hk0 : k.val = 0
          · rw [hk0, siteOf_replyAt_zero, siteOf_replyAt_zero]
          · by_cases hkh : k.val = F.h
            · rw [siteOf_replyAt_last F j0 k.val hk0 hkh,
                siteOf_replyAt_last F (j0 - 1) k.val hk0 hkh]
            · rw [siteOf_replyAt_mid F j0 k.val hk0 hkh (by omega),
                siteOf_replyAt_mid F (j0 - 1) k.val hk0 hkh (by omega)]
  · -- no useful edge.
    have hnext : nextPhase F (Phase.replyAt j0) j = Phase.replyAt j0 := by
      simp [nextPhase, hj]
    rw [hnext]
    apply gapStep_id
    by_cases hk0 : j.val = 0
    · have hu : configOf F (Phase.replyAt j0) (leftEnd F j)
          = Agent.root F.c CwPort.waiting F.ccw0 := by
        rw [configOf_leftEnd, hk0, siteOf_replyAt_zero]
      have hv : configOf F (Phase.replyAt j0) (rightEnd F j)
          = Agent.interior Slot.empty := by
        rw [configOf_rightEnd]
        exact siteOf_replyAt_mid F j0 _ (by omega) (by omega) hj
      rw [hu, hv]
      simp [row]
    · by_cases hh : j.val + 1 = F.h
      · have hv : configOf F (Phase.replyAt j0) (rightEnd F j)
            = Agent.root F.d F.cw0 (resCcw F.c F.d) := by
          rw [configOf_rightEnd]
          exact siteOf_replyAt_last F j0 _ (by omega) hh
        by_cases he : j.val = j0
        · have hu : configOf F (Phase.replyAt j0) (leftEnd F j)
              = Agent.interior (Slot.reply F.d) := by
            rw [configOf_leftEnd]
            exact siteOf_replyAt_tok F j0 _ hk0 (by omega) he
          rw [hu, hv]
          simp [row, resolveResp_of_base F.hd]
        · have hu : configOf F (Phase.replyAt j0) (leftEnd F j)
              = Agent.interior Slot.empty := by
            rw [configOf_leftEnd]
            exact siteOf_replyAt_mid F j0 _ hk0 (by omega) he
          rw [hu, hv]
          simp [row, resolveResp_of_base F.hd]
      · have hv : configOf F (Phase.replyAt j0) (rightEnd F j)
            = Agent.interior Slot.empty := by
          rw [configOf_rightEnd]
          exact siteOf_replyAt_mid F j0 _ (by omega) hh hj
        by_cases he : j.val = j0
        · have hu : configOf F (Phase.replyAt j0) (leftEnd F j)
              = Agent.interior (Slot.reply F.d) := by
            rw [configOf_leftEnd]
            exact siteOf_replyAt_tok F j0 _ hk0 (by omega) he
          rw [hu, hv]
          simp [row]
        · have hu : configOf F (Phase.replyAt j0) (leftEnd F j)
              = Agent.interior Slot.empty := by
            rw [configOf_leftEnd]
            exact siteOf_replyAt_mid F j0 _ hk0 (by omega) he
          rw [hu, hv]
          simp [row]

theorem gapStep_delivered (F : Frame) (j : Fin F.h) :
    gapStep F (configOf F Phase.delivered) j
      = configOf F (nextPhase F Phase.delivered j) := by
  have hjlt : j.val < F.h := j.isLt
  have hhpos : 0 < F.h := F.hpos
  have hnext : nextPhase F Phase.delivered j = Phase.delivered := rfl
  rw [hnext]
  apply gapStep_id
  by_cases hk0 : j.val = 0
  · have hu : configOf F Phase.delivered (leftEnd F j)
        = Agent.root F.c (resCw F.c F.d) F.ccw0 := by
      rw [configOf_leftEnd, hk0, siteOf_delivered_zero]
    by_cases hh : j.val + 1 = F.h
    · have hv : configOf F Phase.delivered (rightEnd F j)
          = Agent.root F.d F.cw0 (resCcw F.c F.d) := by
        rw [configOf_rightEnd]
        exact siteOf_delivered_last F _ (by omega) hh
      rw [hu, hv]
      simp [row, resCw_ne_toSend, resCcw_ne_free, resolveInit_of_base F.hc]
    · have hv : configOf F Phase.delivered (rightEnd F j)
          = Agent.interior Slot.empty := by
        rw [configOf_rightEnd]
        exact siteOf_delivered_mid F _ (by omega) hh
      rw [hu, hv]
      simp [row, resCw_ne_toSend]
  · have hu : configOf F Phase.delivered (leftEnd F j)
        = Agent.interior Slot.empty := by
      rw [configOf_leftEnd]
      exact siteOf_delivered_mid F _ hk0 (by omega)
    by_cases hh : j.val + 1 = F.h
    · have hv : configOf F Phase.delivered (rightEnd F j)
          = Agent.root F.d F.cw0 (resCcw F.c F.d) := by
        rw [configOf_rightEnd]
        exact siteOf_delivered_last F _ (by omega) hh
      rw [hu, hv]
      simp [row, resolveResp_of_base F.hd]
    · have hv : configOf F Phase.delivered (rightEnd F j)
          = Agent.interior Slot.empty := by
        rw [configOf_rightEnd]
        exact siteOf_delivered_mid F _ (by omega) hh
      rw [hu, hv]
      simp [row]

/-- The rows carry each clean phase to the phase computed by `nextPhase`. -/
theorem gapStep_configOf (F : Frame) (p : Phase) (hp : PhaseOk F p)
    (j : Fin F.h) :
    gapStep F (configOf F p) j = configOf F (nextPhase F p j) := by
  cases p with
  | prelaunch => exact gapStep_prelaunch F j
  | declAt j0 => exact gapStep_declAt F j0 hp.1 hp.2 j
  | replyAt j0 => exact gapStep_replyAt F j0 hp.1 hp.2 j
  | delivered => exact gapStep_delivered F j

/-! ## The service debt (Section 3.2) -/

/-- Debt contributed by the owner's clockwise port. -/
def leftDebt (F : Frame) : Agent → Nat
  | .root _ .toSend _ => 2 * F.h - 1
  | .root _ .waiting _ => 0
  | .root _ .heldDenial _ => 0
  | .root _ .heldCandidate _ => 0
  | .interior _ => 0

/-- Debt contributed by an interior agent at position `k`: a declaration still
owes the rest of its clockwise walk, the compare, and the whole reply walk; a
reply owes exactly its remaining counterclockwise walk. -/
def interiorDebt (F : Frame) (k : Nat) : Agent → Nat
  | .interior .empty => 0
  | .interior (.decl _) => 2 * F.h - 1 - k
  | .interior (.reply _) => k
  | .root _ _ _ => 0

/-- Per-position debt. -/
def siteDebt (F : Frame) (k : Nat) (a : Agent) : Nat :=
  if k = 0 then leftDebt F a
  else if k = F.h then 0
  else interiorDebt F k a

theorem siteDebt_zero (F : Frame) (a : Agent) :
    siteDebt F 0 a = leftDebt F a := by
  rfl

theorem siteDebt_last (F : Frame) (k : Nat) (h0 : k ≠ 0) (hh : k = F.h)
    (a : Agent) : siteDebt F k a = 0 := by
  simp only [siteDebt, if_neg h0, if_pos hh]

theorem siteDebt_mid (F : Frame) (k : Nat) (h0 : k ≠ 0) (hh : k ≠ F.h)
    (a : Agent) : siteDebt F k a = interiorDebt F k a := by
  simp only [siteDebt, if_neg h0, if_neg hh]

theorem leftDebt_root_held (F : Frame) (ch : Choice) (v : Verdict)
    (ccw : CcwPort) : leftDebt F (Agent.root ch v.cw ccw) = 0 := by
  cases v <;> rfl

/-- `δ` of Section 3.2 for one gap: the number of remaining useful firings. -/
def deltaOf (F : Frame) (cfg : Config F) : Nat :=
  (List.ofFn (fun k : Fin (F.h + 1) => siteDebt F k.val (cfg k))).sum

/-- The paper's `δ` values `(2h-1, 2h-1-j, j, 0)`. -/
def phaseDebt (F : Frame) : Phase → Nat
  | .prelaunch => 2 * F.h - 1
  | .declAt j => 2 * F.h - 1 - j
  | .replyAt j => j
  | .delivered => 0

theorem deltaOf_configOf (F : Frame) (p : Phase) (hp : PhaseOk F p) :
    deltaOf F (configOf F p) = phaseDebt F p := by
  have hhpos : 0 < F.h := F.hpos
  cases p with
  | prelaunch =>
      rw [deltaOf, ofFn_sum_single _ (⟨0, Nat.succ_pos _⟩ : Fin (F.h + 1))]
      · show siteDebt F 0 (configOf F Phase.prelaunch ⟨0, Nat.succ_pos _⟩)
          = phaseDebt F Phase.prelaunch
        rw [configOf_apply]
        show siteDebt F 0 (siteOf F Phase.prelaunch 0) = _
        rw [siteOf_prelaunch_zero, siteDebt_zero]
        rfl
      · intro k hk
        have hk0 : k.val ≠ 0 := fun h => hk (Fin.ext (by simp [h]))
        by_cases hkh : k.val = F.h
        · exact siteDebt_last F _ hk0 hkh _
        · rw [configOf_apply, siteDebt_mid F _ hk0 hkh,
            siteOf_prelaunch_mid F _ hk0 hkh]
          rfl
  | declAt j0 =>
      have h1 : 1 ≤ j0 := hp.1
      have h2 : j0 < F.h := hp.2
      rw [deltaOf, ofFn_sum_single _ (⟨j0, by omega⟩ : Fin (F.h + 1))]
      · show siteDebt F j0 (configOf F (Phase.declAt j0) ⟨j0, by omega⟩)
          = phaseDebt F (Phase.declAt j0)
        rw [configOf_apply]
        show siteDebt F j0 (siteOf F (Phase.declAt j0) j0) = _
        rw [siteOf_declAt_tok F j0 j0 (by omega) (by omega) rfl,
          siteDebt_mid F j0 (by omega) (by omega)]
        rfl
      · intro k hk
        have hkj : k.val ≠ j0 := fun h => hk (Fin.ext (by simp [h]))
        by_cases hk0 : k.val = 0
        · rw [configOf_apply, hk0, siteOf_declAt_zero, siteDebt_zero]
          rfl
        · by_cases hkh : k.val = F.h
          · exact siteDebt_last F _ hk0 hkh _
          · rw [configOf_apply, siteDebt_mid F _ hk0 hkh,
              siteOf_declAt_mid F j0 _ hk0 hkh hkj]
            rfl
  | replyAt j0 =>
      have h1 : 1 ≤ j0 := hp.1
      have h2 : j0 < F.h := hp.2
      rw [deltaOf, ofFn_sum_single _ (⟨j0, by omega⟩ : Fin (F.h + 1))]
      · show siteDebt F j0 (configOf F (Phase.replyAt j0) ⟨j0, by omega⟩)
          = phaseDebt F (Phase.replyAt j0)
        rw [configOf_apply]
        show siteDebt F j0 (siteOf F (Phase.replyAt j0) j0) = _
        rw [siteOf_replyAt_tok F j0 j0 (by omega) (by omega) rfl,
          siteDebt_mid F j0 (by omega) (by omega)]
        rfl
      · intro k hk
        have hkj : k.val ≠ j0 := fun h => hk (Fin.ext (by simp [h]))
        by_cases hk0 : k.val = 0
        · rw [configOf_apply, hk0, siteOf_replyAt_zero, siteDebt_zero]
          rfl
        · by_cases hkh : k.val = F.h
          · exact siteDebt_last F _ hk0 hkh _
          · rw [configOf_apply, siteDebt_mid F _ hk0 hkh,
              siteOf_replyAt_mid F j0 _ hk0 hkh hkj]
            rfl
  | delivered =>
      rw [deltaOf, ofFn_sum_eq_zero]
      · rfl
      · intro k
        by_cases hk0 : k.val = 0
        · rw [configOf_apply, hk0, siteOf_delivered_zero, siteDebt_zero]
          exact leftDebt_root_held F F.c (res F.c F.d) F.ccw0
        · by_cases hkh : k.val = F.h
          · exact siteDebt_last F _ hk0 hkh _
          · rw [configOf_apply, siteDebt_mid F _ hk0 hkh,
              siteOf_delivered_mid F _ hk0 hkh]
            rfl

/-- (i) of Section 3.3 at the level of phases: no edge increases `δ`. -/
theorem phaseDebt_nextPhase_le (F : Frame) (p : Phase) (hp : PhaseOk F p)
    (j : Fin F.h) : phaseDebt F (nextPhase F p j) ≤ phaseDebt F p := by
  have hjlt : j.val < F.h := j.isLt
  have hhpos : 0 < F.h := F.hpos
  cases p with
  | prelaunch =>
      simp only [nextPhase]
      split
      · split <;> simp only [phaseDebt] <;> omega
      · exact Nat.le_refl _
  | declAt j0 =>
      have h1 : 1 ≤ j0 := hp.1
      have h2 : j0 < F.h := hp.2
      simp only [nextPhase]
      split
      · split <;> simp only [phaseDebt] <;> omega
      · exact Nat.le_refl _
  | replyAt j0 =>
      have h1 : 1 ≤ j0 := hp.1
      have h2 : j0 < F.h := hp.2
      simp only [nextPhase]
      split
      · split <;> simp only [phaseDebt] <;> omega
      · exact Nat.le_refl _
  | delivered => exact Nat.le_refl _

/-- (ii) of Section 3.3 at the level of phases: the unique useful edge exists
and lowers `δ` by exactly one. -/
theorem exists_useful_gapEdge (F : Frame) (p : Phase) (hp : PhaseOk F p)
    (hpos : 0 < phaseDebt F p) :
    ∃ a : Fin F.h, phaseDebt F (nextPhase F p a) + 1 = phaseDebt F p := by
  have hhpos : 0 < F.h := F.hpos
  cases p with
  | prelaunch =>
      refine ⟨⟨0, F.hpos⟩, ?_⟩
      by_cases hh : F.h = 1
      · have hnext : nextPhase F Phase.prelaunch ⟨0, F.hpos⟩ = Phase.delivered := by
          simp [nextPhase, hh]
        rw [hnext]
        simp only [phaseDebt]
        omega
      · have hnext : nextPhase F Phase.prelaunch ⟨0, F.hpos⟩ = Phase.declAt 1 := by
          simp [nextPhase, hh]
        rw [hnext]
        simp only [phaseDebt]
        omega
  | declAt j0 =>
      have h1 : 1 ≤ j0 := hp.1
      have h2 : j0 < F.h := hp.2
      refine ⟨⟨j0, h2⟩, ?_⟩
      by_cases hc : j0 + 1 = F.h
      · have hnext : nextPhase F (Phase.declAt j0) ⟨j0, h2⟩ = Phase.replyAt j0 := by
          simp [nextPhase, hc]
        rw [hnext]
        simp only [phaseDebt]
        omega
      · have hnext : nextPhase F (Phase.declAt j0) ⟨j0, h2⟩
            = Phase.declAt (j0 + 1) := by
          simp [nextPhase, hc]
        rw [hnext]
        simp only [phaseDebt]
        omega
  | replyAt j0 =>
      have h1 : 1 ≤ j0 := hp.1
      have h2 : j0 < F.h := hp.2
      have hprev : j0 - 1 < F.h := by omega
      refine ⟨⟨j0 - 1, hprev⟩, ?_⟩
      by_cases hc : j0 = 1
      · have hnext : nextPhase F (Phase.replyAt j0) ⟨j0 - 1, hprev⟩
            = Phase.delivered := by
          simp [nextPhase, hc]
        rw [hnext]
        simp only [phaseDebt]
        omega
      · have hval : j0 - 1 + 1 = j0 := by omega
        have hnext : nextPhase F (Phase.replyAt j0) ⟨j0 - 1, hprev⟩
            = Phase.replyAt (j0 - 1) := by
          simp [nextPhase, hval, hc]
        rw [hnext]
        simp only [phaseDebt]
        omega
  | delivered => exact absurd hpos (Nat.lt_irrefl 0)

/-! ## Embedding one gap into a scheduler of `n` edges -/

/-- An injective assignment of the gap's `h` physical edges to scheduler
edges.  Scheduler edges outside the image are no-ops for this gap.

Because `edgeAt` is injective, a `GapEmbedding F n` presupposes `F.h ≤ n`; for
`n < F.h` no embedding exists and every statement below quantified over one is
vacuous. -/
structure GapEmbedding (F : Frame) (n : Nat) where
  edgeAt : Fin F.h → Fin n
  inj : ∀ a b, edgeAt a = edgeAt b → a = b

open Classical in
/-- One scheduler edge acting on the gap. -/
noncomputable def schedStep {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : Config F) (e : Fin n) : Config F :=
  if hx : ∃ a : Fin F.h, E.edgeAt a = e then gapStep F cfg hx.choose else cfg

theorem schedStep_eq {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : Config F) (a : Fin F.h) :
    schedStep F E cfg (E.edgeAt a) = gapStep F cfg a := by
  classical
  have hx : ∃ b : Fin F.h, E.edgeAt b = E.edgeAt a := ⟨a, rfl⟩
  rw [schedStep, dif_pos hx]
  have hchoose : E.edgeAt hx.choose = E.edgeAt a := hx.choose_spec
  rw [E.inj _ _ hchoose]

theorem schedStep_id {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : Config F) (e : Fin n) (hne : ∀ a : Fin F.h, E.edgeAt a ≠ e) :
    schedStep F E cfg e = cfg := by
  classical
  rw [schedStep, dif_neg]
  rintro ⟨a, ha⟩
  exact hne a ha

theorem schedStep_cases {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : Config F) (e : Fin n) :
    schedStep F E cfg e = cfg
      ∨ ∃ a : Fin F.h, schedStep F E cfg e = gapStep F cfg a := by
  classical
  by_cases hx : ∃ a : Fin F.h, E.edgeAt a = e
  · obtain ⟨a, ha⟩ := hx
    subst ha
    exact Or.inr ⟨a, schedStep_eq F E cfg a⟩
  · exact Or.inl (schedStep_id F E cfg e (fun a ha => hx ⟨a, ha⟩))

/-! ## The three Bellman facts for one gap -/

/-- Every row preserves the clean lane, for every scheduler edge. -/
theorem clean_step {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : Config F) (hcl : Clean F cfg) (e : Fin n) :
    Clean F (schedStep F E cfg e) := by
  rcases schedStep_cases F E cfg e with h | ⟨a, h⟩
  · rw [h]; exact hcl
  · obtain ⟨p, hp, rfl⟩ := hcl.exists_phase
    rw [h, gapStep_configOf F p hp a]
    exact Clean.of_phaseOk F _ (nextPhase_phaseOk F p hp a)

/-- (i) No scheduler edge increases the service debt. -/
theorem delta_step_le {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : Config F) (hcl : Clean F cfg) (e : Fin n) :
    deltaOf F (schedStep F E cfg e) ≤ deltaOf F cfg := by
  rcases schedStep_cases F E cfg e with h | ⟨a, h⟩
  · rw [h]
    exact Nat.le_refl _
  · obtain ⟨p, hp, rfl⟩ := hcl.exists_phase
    rw [h, gapStep_configOf F p hp a,
      deltaOf_configOf F _ (nextPhase_phaseOk F p hp a),
      deltaOf_configOf F p hp]
    exact phaseDebt_nextPhase_le F p hp a

/-- (ii) From any non-terminal clean state the unique useful edge lowers the
service debt by exactly one. -/
theorem delta_useful_lt {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : Config F) (hcl : Clean F cfg) (hpos : 0 < deltaOf F cfg) :
    ∃ a : Fin F.h,
      deltaOf F (schedStep F E cfg (E.edgeAt a)) + 1 = deltaOf F cfg := by
  obtain ⟨p, hp, rfl⟩ := hcl.exists_phase
  rw [deltaOf_configOf F p hp] at hpos
  obtain ⟨a, ha⟩ := exists_useful_gapEdge F p hp hpos
  refine ⟨a, ?_⟩
  rw [schedStep_eq F E _ a, gapStep_configOf F p hp a,
    deltaOf_configOf F _ (nextPhase_phaseOk F p hp a),
    deltaOf_configOf F p hp]
  exact ha

/-- The exact child-sum inequality of Section 3.3. -/
theorem delta_childSum {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : Config F) (hcl : Clean F cfg) (hpos : 0 < deltaOf F cfg) :
    1 + (List.ofFn (fun e : Fin n => deltaOf F (schedStep F E cfg e))).sum
      ≤ n * deltaOf F cfg := by
  obtain ⟨a, ha⟩ := delta_useful_lt F E cfg hcl hpos
  have hlt := ofFn_sum_lt_of_single_lt
    (fun e : Fin n => deltaOf F (schedStep F E cfg e))
    (fun _ : Fin n => deltaOf F cfg) (E.edgeAt a)
    (fun e => delta_step_le F E cfg hcl e)
    (by omega)
  rw [ofFn_sum_const] at hlt
  omega

/-! ## The one-gap Bellman supersolution -/

/-- The subtype of clean configurations. -/
def CleanConfig (F : Frame) : Type := {cfg : Config F // Clean F cfg}

/-- The active (non-discharged) part of that subtype. -/
def ActiveCleanConfig (F : Frame) : Type :=
  {s : CleanConfig F // 0 < deltaOf F s.1}

/-- The one-gap service as an absorbing stopped process: it stops in
`.success` exactly when the debt reaches `0`, and never exposes `.failure`. -/
noncomputable def gapNode {n : Nat} (F : Frame) (E : GapEmbedding F n) :
    ActiveCleanConfig F → Fin n → StopNode (ActiveCleanConfig F) :=
  fun s e =>
    if hp : 0 < deltaOf F (schedStep F E s.1.1 e) then
      .active ⟨⟨schedStep F E s.1.1 e, clean_step F E s.1.1 s.1.2 e⟩, hp⟩
    else .success

/-- The potential `n * δ`. -/
def gapPotential {n : Nat} (F : Frame) : StopNode (ActiveCleanConfig F) → Nat
  | .active s => n * deltaOf F s.1.1
  | .success => 0
  | .failure => 0

theorem gapNode_ne_failure {n : Nat} (F : Frame) (E : GapEmbedding F n) :
    ∀ s e, gapNode F E s e ≠ .failure := by
  intro s e
  simp only [gapNode]
  split <;> simp

private theorem gapPotential_gapNode {n : Nat} (F : Frame)
    (E : GapEmbedding F n) (s : ActiveCleanConfig F) (e : Fin n) :
    gapPotential (n := n) F (gapNode F E s e)
      = n * deltaOf F (schedStep F E s.1.1 e) := by
  simp only [gapNode]
  split
  · rfl
  · rename_i hne
    have hz : deltaOf F (schedStep F E s.1.1 e) = 0 := by omega
    simp [gapPotential, hz]

/-- The one-gap literal carrier is a `NatBellmanSuperSolution` with scale `1`
for the potential `n * δ`. -/
theorem gap_natBellmanSuperSolution {n : Nat} (F : Frame)
    (E : GapEmbedding F n) :
    NatBellmanSuperSolution (gapNode F E) 1 (gapPotential (n := n) F) := by
  refine ⟨rfl, rfl, ?_⟩
  intro s
  have hdebt := delta_childSum F E s.1.1 s.1.2 s.2
  have hscaled := Nat.mul_le_mul_left n hdebt
  have hchildren :
      (List.ofFn (fun e : Fin n =>
        gapPotential (n := n) F (gapNode F E s e))).sum
        = n * (List.ofFn (fun e : Fin n =>
            deltaOf F (schedStep F E s.1.1 e))).sum := by
    rw [← ofFn_sum_mul_left]
    exact ofFn_sum_eq _ _ (fun e => gapPotential_gapNode F E s e)
  calc
    1 * n + (List.ofFn (fun e : Fin n =>
        gapPotential (n := n) F (gapNode F E s e))).sum
        = n * (1 + (List.ofFn (fun e : Fin n =>
            deltaOf F (schedStep F E s.1.1 e))).sum) := by
          rw [hchildren, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    _ ≤ n * (n * deltaOf F s.1.1) := hscaled
    _ = n * gapPotential (n := n) F (.active s) := rfl

/-- The pre-launch start state of the gap. -/
def startState (F : Frame) : ActiveCleanConfig F :=
  ⟨⟨configOf F Phase.prelaunch, Clean.prelaunch⟩, by
    rw [deltaOf_configOf F Phase.prelaunch trivial]
    have := F.hpos
    simp only [phaseDebt]
    omega⟩

/-- The start potential is `n * (2*h - 1)`: the `2h-1` useful firings of the
gap (launch, `h-1` forward hops, the compare, `h-1` backward hops, delivery),
each charged `n`. -/
theorem gapPotential_startState {n : Nat} (F : Frame) :
    gapPotential (n := n) F (.active (startState F)) = n * (2 * F.h - 1) := by
  show n * deltaOf F (configOf F Phase.prelaunch) = n * (2 * F.h - 1)
  rw [deltaOf_configOf F Phase.prelaunch trivial]
  rfl

/-! ## Authentication (Section 1.4) -/

/-- The owner holds its declared choice in every clean state: no row of the
table writes the owner's `ch` from launch to delivery. -/
theorem owner_choice_held (F : Frame) (cfg : Config F) (hcl : Clean F cfg) :
    (cfg (leftPos F)).choice = some F.c := by
  obtain ⟨p, _, rfl⟩ := hcl.exists_phase
  show (siteOf F p 0).choice = some F.c
  cases p with
  | prelaunch => rw [siteOf_prelaunch_zero]; rfl
  | declAt j0 => rw [siteOf_declAt_zero]; rfl
  | replyAt j0 => rw [siteOf_replyAt_zero]; rfl
  | delivered => rw [siteOf_delivered_zero]; rfl

/-- A clean state of debt `0` is the delivered state (d). -/
theorem clean_delta_zero_delivered (F : Frame) (cfg : Config F)
    (hcl : Clean F cfg) (h0 : deltaOf F cfg = 0) :
    cfg = configOf F Phase.delivered := by
  have hhpos : 0 < F.h := F.hpos
  obtain ⟨p, hp, rfl⟩ := hcl.exists_phase
  rw [deltaOf_configOf F p hp] at h0
  cases p with
  | prelaunch => exfalso; simp only [phaseDebt] at h0; omega
  | declAt j0 =>
      exfalso
      have h1 : 1 ≤ j0 := hp.1
      have h2 : j0 < F.h := hp.2
      simp only [phaseDebt] at h0
      omega
  | replyAt j0 =>
      exfalso
      have h1 : 1 ≤ j0 := hp.1
      simp only [phaseDebt] at h0
      omega
  | delivered => rfl

/-- In the delivered state the owner's clockwise receipt and the right root's
counterclockwise receipt are the two renderings of ONE verdict, namely
`res c d` computed from the owner's held choice `c` and the right root's held
choice `d`.  This is the paper's authentication statement: the receipt equality
IS the hold invariant, with no case analysis on a payload result field. -/
theorem owner_receipt_eq_right_result (F : Frame) (cfg : Config F)
    (hcl : Clean F cfg) (h0 : deltaOf F cfg = 0) :
    ∃ v : Verdict,
      v = res F.c F.d ∧
      (cfg (leftPos F)).cwPort = some v.cw ∧
      (cfg (rightPos F)).ccwPort = some v.ccw ∧
      (cfg (leftPos F)).choice = some F.c := by
  have hhne : F.h ≠ 0 := by have := F.hpos; omega
  have hdel := clean_delta_zero_delivered F cfg hcl h0
  subst hdel
  refine ⟨res F.c F.d, rfl, ?_, ?_, ?_⟩
  · show (siteOf F Phase.delivered 0).cwPort = _
    rw [siteOf_delivered_zero]
    rfl
  · show (siteOf F Phase.delivered F.h).ccwPort = _
    rw [siteOf_delivered_last F F.h hhne rfl]
    rfl
  · show (siteOf F Phase.delivered 0).choice = _
    rw [siteOf_delivered_zero]
    rfl

#print axioms clean_step
#print axioms gap_natBellmanSuperSolution
#print axioms owner_receipt_eq_right_result

end ShortGapLiteralGapRows

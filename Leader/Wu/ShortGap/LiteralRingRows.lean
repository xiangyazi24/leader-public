import Leader.Wu.ShortGap.LiteralGapRows

/-!
# The `m`-gap shared-root product of the literal rows, on the uniform lane

This file composes the literal radius-one row table of
`Leader/Wu/ShortGap/LiteralGapRows.lean` (`Agent`, `row`, the fourteen paper rows
of `TWO_DENIAL_LITERAL_CARRIER.md` Section 1.3) into a whole directed ring of
`m ≥ 2` gaps that SHARE their roots, adds the post-step JOIN of Section 1.2,
and proves the shared-root check of Section 3.4, the service debt of
Section 3.2, Claim T, and the three Bellman facts of Section 3.3 for the
`m`-gap system.

## Geometry (uniform gap length)

Gaps have the SAME length `h ≥ 1`, so the ring has `n = m * h` vertices and
`n` scheduler edges.  A vertex is a pair `(g, r) : Fin m × Fin h`: offset `0`
is the root of gap `g`, offsets `1, …, h-1` are its interior agents, and the
right root of gap `g` is the root of gap `g+1`.  `rn` is the ring's right
neighbour, `edgeVtx : Fin n → Vtx` the scheduler's edge indexing (`encE` its
inverse on `(g, r)`).  The non-uniform case `len g ≥ 1` with
`n = Σ_g len g` is NOT done here; see "Scope" below.

## The step

`ringStep cfg e` rewrites both endpoints of edge `e` by `row` and then applies
the post-step JOIN `joinA (root _ heldDenial heldDenial) = root race toSend
free` to both endpoints (`ringStep_frame`: nothing else changes).  ONE
exception, stated as a modelling restriction, not as a theorem: an edge with a
`race` (already joined) root endpoint is a no-op (`frozen`, `frozen_iff`).

Why: the raw table is total and its round-`k+1` rows DO fire on a joined root
-- `row_L2_on_joined_root` (a fresh declaration is launched out of `root race
toSend free`) and `row_K4_on_joined_root` (the responder half of `K2` resolves
the `race` back to a base) are proved in this file.  Modelling them means
modelling pipelined rounds, which is out of scope here, and no local debt
function can survive them (after a JOIN the root state `root race toSend free`
and, after a `K4`, `root b toSend free` are indistinguishable from a fresh
pre-launch root).  So they are excluded by the freeze.  The exclusion is
harmless for everything proved here: `exists_useful_ring` proves the useful
edge of an indebted gap is NEVER frozen (a frozen edge always has a delivered
gap on the relevant side), so the freeze removes no progress from the Bellman
argument.

## The clean lane

`RingClean cfg` says `cfg = cfgOf P` for a phase vector `P : Fin m → Phase`
with `PhaseOk` (the one-gap phases (a) pre-launch, (b) declaration at `j`,
(c) reply at `j`, (d) delivered, reused verbatim from the one-gap file).  The
whole ring configuration is a function of `P`:

* interior of gap `g`: the token of phase `P g` (`slotAgent`);
* root of gap `g`: `root race toSend free` when `joined P g`, i.e. when gap `g`
  has delivered AND gap `g-1` has compared, and otherwise
  `root b (cwOf (P g)) (ccwOf (P (g-1)))`, the shared root's clockwise port
  belonging to gap `g` and its counterclockwise port to gap `g-1`.

That `joined` is a FUNCTION of `P` is the small structural fact that makes the
composition finite: both writes that can complete a root's two denials (the
delivery on its own gap and the comparison on the previous gap) happen on
edges incident to that root, so the post-step JOIN fires with the later of the
two, never later.

`ringClean_step` (Section 3.4): every physical edge preserves `RingClean`.  It
is proved through the simulation theorem `ringStep_cfgOf`:
`ringStep (cfgOf P) e = cfgOf (nextP P e)`, where `nextP` advances only gap
`e.1`, by the one-gap `nextPhase`.  The four edge kinds are the paper's
`RI` (`L1`, `V1`), `II` (`F1`, `B1`), `IR` (`K1`, `K3`, `K4`) and, for `h = 1`,
`RR` (`P1`, `P2`, `P3`).

## The debt and the Bellman facts

`D cfg = Σ_g Σ_r siteDebtR r (cfg (g, r))` is a sum of LOCAL site debts:
`2h-1` for a root `root ch toSend _` with `ch = b` (the pre-launch marker on
the uniform lane -- a joined root is in `race`, not in `b`, and pays `0`),
`2h-1-r` for a declaration at offset `r`, `r` for a reply at offset `r`.  On
the clean lane `D (cfgOf P) = Σ_g phaseDebt (P g)` (`D_cfgOf`), the paper's
`δ ∈ {2h-1, 2h-1-j, j, 0}`.

* `D_step_le` (i): no edge increases `D`.
* `D_useful_lt` (ii): if `D > 0` some edge lowers it by EXACTLY one; the
  witness is the unique next useful edge of an indebted gap, whose guard holds
  on the uniform lane -- in particular the compare guard `ccw = free`, because
  a gap whose token has not yet been compared leaves its right root's
  counterclockwise port free.
* `D_childSum` (iii): `1 + Σ_e D(step e) ≤ n * D`, hence
  `ring_natBellmanSuperSolution`: `n * D` is a `NatBellmanSuperSolution` with
  scale `1` on the active clean configurations, stopping in `.success` exactly
  when `D = 0` and never reaching `.failure`.
* `D_start`: `D (uniformStart) = Σ_g (2h - 1) = 2n - m`, so the start
  potential is `n * (2n - m)` (`ringPotential_startState`).

`claimT`: on the clean lane `D = 0` iff every root is `root race toSend free`,
i.e. iff every root has performed its JOIN.

`p1_writes_both`, `p1_adjacent_prelaunch`, `p1_join_same_step` and
`p1_join_same_step_left`: for `h = 1` (all gaps of length one, so all gaps
adjacent) ONE firing of a pre-launch gap's single edge writes the owner's
clockwise receipt and the shared root's counterclockwise receipt atomically,
and if that firing completes either root's two denials, that root's JOIN fires
in the SAME step.

## Scope

* UNIFORM gap length `h` for all `m` gaps.  The general `len : Fin m → Nat`
  with `len g ≥ 1` and `n = Σ_g len g` is not treated; the phase machinery is
  already per-gap (`nextPhase (F0 R)` only reads the gap length), so the
  generalization is a re-indexing of the geometry, not new protocol content.
* `m ≥ 2`.  The degenerate `m = 1` self-gap (one root that owns the gap and is
  also its right root) is excluded.
* UNIFORM lane only: every root starts frozen at ONE base `b ∈ {out1, in0}`,
  both bases allowed.  Hence `res b b = denial` always: every verdict on this
  lane is a denial, `heldCandidate` never occurs, and no candidate is ever
  produced.  `resolveInit`/`resolveResp` are identities, so every incidence
  row is a no-op here.
* The dirty rows `L3`, `V2`, `P3` are never exercised: on the base lane they
  are the identity (`row_RI_decl`, `row_RR_noSend`), which is what the clean
  cases use.
* NO pipelining beyond the JOIN itself: a joined root becomes `race` and then
  stays put, by the freeze described above.  No round-`k+1` declaration,
  comparison or incidence is modelled.
* NO claim about stabilization, leader election, or composition with
  `BalancedFailureRestart`.  The only quantitative output is the ring Bellman
  supersolution with start potential `n * (2n - m)`.
-/

namespace ShortGapLiteralRingRows

open FiniteUniformStoppingTree
open ShortGapLiteralGapRows

set_option autoImplicit false

/-! ## Finite uniform sum helpers

Copies of the private helpers of the one-gap file, which are not exported. -/

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

/-! ## The ring frame -/

/-- Static data of the ring: `m ≥ 2` gaps, each of `h ≥ 1` physical edges, and
the uniform base `b ∈ {out1, in0}` held by every root at the start. -/
structure RFrame where
  m : Nat
  h : Nat
  hm : 2 ≤ m
  hh : 0 < h
  b : Choice
  hb : IsBase b

/-- The number of ring vertices, which is also the number of scheduler
edges. -/
def RFrame.n (R : RFrame) : Nat := R.m * R.h

theorem RFrame.n_pos (R : RFrame) : 0 < R.n :=
  Nat.mul_pos (by have := R.hm; omega) R.hh

/-- A ring vertex: gap index and offset inside the gap.  Offset `0` is the
root of that gap; offsets `1, …, h-1` are its interior agents. -/
abbrev Vtx (R : RFrame) := Fin R.m × Fin R.h

/-- A phase vector: one clean phase per gap. -/
abbrev PV (R : RFrame) := Fin R.m → Phase

/-- The one-gap frame with the ring's gap length and the uniform base on both
endpoints.  Only its `h` field is used for phases and phase debts. -/
abbrev F0 (R : RFrame) : Frame :=
  { h := R.h, hpos := R.hh, c := R.b, d := R.b, hc := R.hb, hd := R.hb,
    ccw0 := CcwPort.free, cw0 := CwPort.toSend }

/-! ## Cyclic successor and predecessor of gap indices -/

/-- The next gap clockwise. -/
def next (R : RFrame) (g : Fin R.m) : Fin R.m :=
  ⟨if g.val + 1 = R.m then 0 else g.val + 1, by
    have h1 := g.isLt; have h2 := R.hm; split <;> omega⟩

/-- The previous gap clockwise. -/
def prev (R : RFrame) (g : Fin R.m) : Fin R.m :=
  ⟨if g.val = 0 then R.m - 1 else g.val - 1, by
    have h1 := g.isLt; have h2 := R.hm; split <;> omega⟩

theorem next_val (R : RFrame) (g : Fin R.m) :
    (next R g).val = if g.val + 1 = R.m then 0 else g.val + 1 := rfl

theorem prev_val (R : RFrame) (g : Fin R.m) :
    (prev R g).val = if g.val = 0 then R.m - 1 else g.val - 1 := rfl

theorem prev_next (R : RFrame) (g : Fin R.m) : prev R (next R g) = g := by
  have h1 := g.isLt
  have h2 := R.hm
  apply Fin.ext
  rw [prev_val, next_val]
  by_cases hg : g.val + 1 = R.m
  · rw [if_pos hg, if_pos rfl]; omega
  · rw [if_neg hg, if_neg (by omega)]; omega

theorem next_prev (R : RFrame) (g : Fin R.m) : next R (prev R g) = g := by
  have h1 := g.isLt
  have h2 := R.hm
  apply Fin.ext
  rw [next_val, prev_val]
  by_cases hg : g.val = 0
  · rw [if_pos hg, if_pos (by omega)]; omega
  · rw [if_neg hg, if_neg (by omega)]; omega

theorem next_ne_self (R : RFrame) (g : Fin R.m) : next R g ≠ g := by
  have h1 := g.isLt
  have h2 := R.hm
  intro hcon
  have := congrArg Fin.val hcon
  rw [next_val] at this
  by_cases hg : g.val + 1 = R.m
  · rw [if_pos hg] at this; omega
  · rw [if_neg hg] at this; omega

theorem prev_ne_self (R : RFrame) (g : Fin R.m) : prev R g ≠ g := by
  intro hcon
  have h1 : next R (prev R g) = next R g := by rw [hcon]
  rw [next_prev] at h1
  exact next_ne_self R g h1.symm

theorem prev_eq_iff (R : RFrame) (g g' : Fin R.m) :
    prev R g' = g ↔ g' = next R g := by
  constructor
  · intro h
    rw [← h, next_prev]
  · intro h
    rw [h, prev_next]

theorem next_inj (R : RFrame) (g g' : Fin R.m) (h : next R g = next R g') :
    g = g' := by
  rw [← prev_next R g, ← prev_next R g', h]

/-! ## Vertex bookkeeping -/

theorem vtx_eq (R : RFrame) (v w : Vtx R) (h1 : v.1 = w.1)
    (h2 : v.2.val = w.2.val) : v = w := by
  obtain ⟨a, b⟩ := v
  obtain ⟨c, d⟩ := w
  simp only at h1 h2
  subst h1
  rw [Fin.ext h2]

theorem vtx_ne_of_fst (R : RFrame) (v w : Vtx R) (h : v.1 ≠ w.1) : v ≠ w :=
  fun hcon => h (by rw [hcon])

theorem vtx_ne_of_snd (R : RFrame) (v w : Vtx R) (h : v.2.val ≠ w.2.val) :
    v ≠ w :=
  fun hcon => h (by rw [hcon])

/-! ## The clean lane of one gap, as fields of the ring configuration -/

/-- The clockwise port that gap `g`'s phase puts on the root of gap `g`. -/
def cwOf : Phase → CwPort
  | .prelaunch => CwPort.toSend
  | .declAt _ => CwPort.waiting
  | .replyAt _ => CwPort.waiting
  | .delivered => CwPort.heldDenial

/-- The counterclockwise port that gap `g`'s phase puts on the root of gap
`g+1` (the shared root).  On the uniform lane every verdict is a denial. -/
def ccwOf : Phase → CcwPort
  | .replyAt _ => CcwPort.heldDenial
  | .delivered => CcwPort.heldDenial
  | _ => CcwPort.free

/-- Phase (d): the owner has received its receipt. -/
def IsDelivered : Phase → Bool
  | .delivered => true
  | _ => false

/-- Phases (c) and (d): the shared root at the far end has compared. -/
def Compared : Phase → Bool
  | .replyAt _ => true
  | .delivered => true
  | _ => false

/-- The root of gap `g` has performed its JOIN: its own gap delivered and the
previous gap compared.  Both writes happen on edges incident to that root, so
the post-step JOIN fires at the later of the two; hence this is a function of
the phase vector alone. -/
def joined (R : RFrame) (P : PV R) (g : Fin R.m) : Bool :=
  IsDelivered (P g) && Compared (P (prev R g))

/-- The state of the root of gap `g`. -/
def rootAgent (R : RFrame) (P : PV R) (g : Fin R.m) : Agent :=
  if joined R P g then Agent.root Choice.race CwPort.toSend CcwPort.free
  else Agent.root R.b (cwOf (P g)) (ccwOf (P (prev R g)))

/-- The state of the interior agent at offset `r ≥ 1` of gap `g`. -/
def slotAgent (R : RFrame) : Phase → Nat → Agent
  | .declAt j, r =>
      if r = j then Agent.interior (Slot.decl R.b) else Agent.interior Slot.empty
  | .replyAt j, r =>
      if r = j then Agent.interior (Slot.reply R.b) else Agent.interior Slot.empty
  | _, _ => Agent.interior Slot.empty

/-- The ring configuration of a phase vector. -/
def cfgOf (R : RFrame) (P : PV R) : Vtx R → Agent :=
  fun v => if v.2.val = 0 then rootAgent R P v.1 else slotAgent R (P v.1) v.2.val

theorem cfgOf_root (R : RFrame) (P : PV R) (v : Vtx R) (hr : v.2.val = 0) :
    cfgOf R P v = rootAgent R P v.1 := by
  simp only [cfgOf, if_pos hr]

theorem cfgOf_slot (R : RFrame) (P : PV R) (v : Vtx R) (hr : v.2.val ≠ 0) :
    cfgOf R P v = slotAgent R (P v.1) v.2.val := by
  simp only [cfgOf, if_neg hr]

/-! ## The physical ring step -/

/-- The right neighbour of a vertex on the directed ring. -/
def rn (R : RFrame) (v : Vtx R) : Vtx R :=
  if hlt : v.2.val + 1 < R.h then (v.1, ⟨v.2.val + 1, hlt⟩)
  else (next R v.1, ⟨0, R.hh⟩)

theorem rn_of_lt (R : RFrame) (v : Vtx R) (h : v.2.val + 1 < R.h) :
    rn R v = (v.1, ⟨v.2.val + 1, h⟩) := by
  simp only [rn, dif_pos h]

theorem rn_of_last (R : RFrame) (v : Vtx R) (h : ¬ (v.2.val + 1 < R.h)) :
    rn R v = (next R v.1, ⟨0, R.hh⟩) := by
  simp only [rn, dif_neg h]

theorem rn_ne_self (R : RFrame) (v : Vtx R) : rn R v ≠ v := by
  by_cases h : v.2.val + 1 < R.h
  · rw [rn_of_lt R v h]
    exact vtx_ne_of_snd R _ _ (by simp)
  · rw [rn_of_last R v h]
    exact vtx_ne_of_fst R _ _ (next_ne_self R v.1)

/-- The post-step JOIN of Section 1.2: two held denials rearm the root. -/
def joinA : Agent → Agent
  | .root _ .heldDenial .heldDenial =>
      Agent.root Choice.race CwPort.toSend CcwPort.free
  | a => a

/-- A root that has already joined, and is therefore in `race`. -/
def isRaceRoot : Agent → Bool
  | .root Choice.race _ _ => true
  | _ => false

/-- The freeze guard: the edge has an already joined (`race`) root endpoint. -/
def frozen (R : RFrame) (cfg : Vtx R → Agent) (e : Vtx R) : Bool :=
  isRaceRoot (cfg e) || isRaceRoot (cfg (rn R e))

/-- One scheduled physical edge: rewrite both endpoints by `row`, then apply
the post-step JOIN to both endpoints.  An edge with an already joined (`race`)
root endpoint is a no-op: this is the explicit exclusion of the round-`k+1`
incidence and launch rows (`L2`, `K2`, `K4`, `P2`) at a joined root. -/
def ringStep (R : RFrame) (cfg : Vtx R → Agent) (e : Vtx R) : Vtx R → Agent :=
  if frozen R cfg e then cfg
  else
    fun w =>
      if w = e then joinA (row (cfg e) (cfg (rn R e))).1
      else if w = rn R e then joinA (row (cfg e) (cfg (rn R e))).2
      else cfg w

theorem ringStep_frozen (R : RFrame) (cfg : Vtx R → Agent) (e : Vtx R)
    (h : frozen R cfg e = true) : ringStep R cfg e = cfg := by
  simp only [ringStep, if_pos h]

theorem ringStep_fire (R : RFrame) (cfg : Vtx R → Agent) (e w : Vtx R)
    (h : ¬ (frozen R cfg e = true)) :
    ringStep R cfg e w =
      (if w = e then joinA (row (cfg e) (cfg (rn R e))).1
       else if w = rn R e then joinA (row (cfg e) (cfg (rn R e))).2
       else cfg w) := by
  simp only [ringStep, if_neg h]

/-- Frame lemma: one firing changes only the two endpoints of the edge. -/
theorem ringStep_frame (R : RFrame) (cfg : Vtx R → Agent) (e w : Vtx R)
    (h1 : w ≠ e) (h2 : w ≠ rn R e) : ringStep R cfg e w = cfg w := by
  by_cases h : frozen R cfg e = true
  · rw [ringStep_frozen R cfg e h]
  · rw [ringStep_fire R cfg e w h, if_neg h1, if_neg h2]

theorem ringStep_left (R : RFrame) (cfg : Vtx R → Agent) (e : Vtx R)
    (h : ¬ (frozen R cfg e = true)) :
    ringStep R cfg e e = joinA (row (cfg e) (cfg (rn R e))).1 := by
  rw [ringStep_fire R cfg e e h, if_pos rfl]

theorem ringStep_right (R : RFrame) (cfg : Vtx R → Agent) (e : Vtx R)
    (h : ¬ (frozen R cfg e = true)) :
    ringStep R cfg e (rn R e) = joinA (row (cfg e) (cfg (rn R e))).2 := by
  rw [ringStep_fire R cfg e (rn R e) h, if_neg (rn_ne_self R e), if_pos rfl]

/-! ## The rows on the uniform lane

Every root holds the same frozen base `b`, so `resolveInit` and `resolveResp`
are identities, every incidence row is a no-op, and every verdict is a denial:
`res b b = denial` for both bases. -/

theorem b_ne_race (R : RFrame) : R.b ≠ Choice.race := by
  rcases R.hb with h | h <;> rw [h] <;> simp

theorem res_base (R : RFrame) : res R.b R.b = Verdict.denial := by
  rcases R.hb with h | h <;> rw [h] <;> simp [res]

theorem resCw_base (R : RFrame) : resCw R.b R.b = CwPort.heldDenial := by
  rw [resCw, res_base]; rfl

theorem resCcw_base (R : RFrame) : resCcw R.b R.b = CcwPort.heldDenial := by
  rw [resCcw, res_base]; rfl

theorem resolveInit_b (R : RFrame) : resolveInit R.b = R.b :=
  resolveInit_of_base R.hb

theorem resolveResp_b (R : RFrame) : resolveResp R.b = R.b :=
  resolveResp_of_base R.hb

/-- `L1`: the owner launches its declaration. -/
theorem row_L1 (R : RFrame) (X : CcwPort) :
    row (Agent.root R.b CwPort.toSend X) (Agent.interior Slot.empty)
      = (Agent.root R.b CwPort.waiting X,
         Agent.interior (Slot.decl R.b)) := by
  simp [row, resolveInit_b R]

/-- A root whose clockwise port is not `toSend` does not launch. -/
theorem row_RI_empty (R : RFrame) (cw : CwPort) (X : CcwPort)
    (h : cw ≠ CwPort.toSend) :
    row (Agent.root R.b cw X) (Agent.interior Slot.empty)
      = (Agent.root R.b cw X, Agent.interior Slot.empty) := by
  simp [row, h]

/-- `L3` on the uniform lane is the identity (the owner is already frozen). -/
theorem row_RI_decl (R : RFrame) (cw : CwPort) (X : CcwPort) (c : Choice) :
    row (Agent.root R.b cw X) (Agent.interior (Slot.decl c))
      = (Agent.root R.b cw X, Agent.interior (Slot.decl c)) := by
  by_cases hs : cw = CwPort.toSend
  · simp [row, hs, resolveInit_b R]
  · simp [row, hs]

/-- `V1`: the owner receives its receipt. -/
theorem row_V1 (R : RFrame) (X : CcwPort) :
    row (Agent.root R.b CwPort.waiting X) (Agent.interior (Slot.reply R.b))
      = (Agent.root R.b CwPort.heldDenial X, Agent.interior Slot.empty) := by
  simp [row, resCw_base R]

/-- `K1`: the shared root compares and stores its denial. -/
theorem row_K1 (R : RFrame) (Y : CwPort) :
    row (Agent.interior (Slot.decl R.b)) (Agent.root R.b Y CcwPort.free)
      = (Agent.interior (Slot.reply R.b),
         Agent.root R.b Y CcwPort.heldDenial) := by
  simp [row, resolveResp_b R, resCcw_base R]

/-- `K4` with an empty initiator slot: a no-op on the uniform lane. -/
theorem row_K4_empty (R : RFrame) (Y : CwPort) (Z : CcwPort) :
    row (Agent.interior Slot.empty) (Agent.root R.b Y Z)
      = (Agent.interior Slot.empty, Agent.root R.b Y Z) := by
  simp [row, resolveResp_b R]

/-- `K4` with a reply in the initiator slot: a no-op on the uniform lane. -/
theorem row_K4_reply (R : RFrame) (Y : CwPort) (Z : CcwPort) (d : Choice) :
    row (Agent.interior (Slot.reply d)) (Agent.root R.b Y Z)
      = (Agent.interior (Slot.reply d), Agent.root R.b Y Z) := by
  simp [row, resolveResp_b R]

/-- `F1`: the declaration hops clockwise. -/
theorem row_F1 (c : Choice) :
    row (Agent.interior (Slot.decl c)) (Agent.interior Slot.empty)
      = (Agent.interior Slot.empty, Agent.interior (Slot.decl c)) := by
  simp [row]

/-- `B1`: the reply is pulled counterclockwise. -/
theorem row_B1 (d : Choice) :
    row (Agent.interior Slot.empty) (Agent.interior (Slot.reply d))
      = (Agent.interior (Slot.reply d), Agent.interior Slot.empty) := by
  simp [row]

theorem row_II_ee :
    row (Agent.interior Slot.empty) (Agent.interior Slot.empty)
      = (Agent.interior Slot.empty, Agent.interior Slot.empty) := by
  simp [row]

theorem row_II_ed (c : Choice) :
    row (Agent.interior Slot.empty) (Agent.interior (Slot.decl c))
      = (Agent.interior Slot.empty, Agent.interior (Slot.decl c)) := by
  simp [row]

theorem row_II_r (d : Choice) (t : Slot) :
    row (Agent.interior (Slot.reply d)) (Agent.interior t)
      = (Agent.interior (Slot.reply d), Agent.interior t) := by
  simp [row]

/-- `P1`: on a gap of length one, launch, compare and delivery are atomic. -/
theorem row_P1 (R : RFrame) (X : CcwPort) (Y : CwPort) :
    row (Agent.root R.b CwPort.toSend X) (Agent.root R.b Y CcwPort.free)
      = (Agent.root R.b CwPort.heldDenial X,
         Agent.root R.b Y CcwPort.heldDenial) := by
  simp [row, resolveInit_b R, resolveResp_b R, resCw_base R, resCcw_base R]

/-- `P3` on the uniform lane is the identity. -/
theorem row_RR_noSend (R : RFrame) (cw : CwPort) (X : CcwPort) (Y : CwPort)
    (Z : CcwPort) (h : cw ≠ CwPort.toSend) :
    row (Agent.root R.b cw X) (Agent.root R.b Y Z)
      = (Agent.root R.b cw X, Agent.root R.b Y Z) := by
  by_cases hz : Z = CcwPort.free
  · simp [row, h, hz, resolveInit_b R, resolveResp_b R]
  · simp [row, h, hz, resolveInit_b R]

/-- `P2` on the uniform lane is the identity: the right root still holds. -/
theorem row_RR_wait (R : RFrame) (X : CcwPort) (Y : CwPort) (Z : CcwPort)
    (h : Z ≠ CcwPort.free) :
    row (Agent.root R.b CwPort.toSend X) (Agent.root R.b Y Z)
      = (Agent.root R.b CwPort.toSend X, Agent.root R.b Y Z) := by
  simp [row, h, resolveInit_b R]

/-! ## The post-step JOIN -/

theorem joinA_interior (s : Slot) :
    joinA (Agent.interior s) = Agent.interior s := rfl

theorem joinA_join (ch : Choice) :
    joinA (Agent.root ch CwPort.heldDenial CcwPort.heldDenial)
      = Agent.root Choice.race CwPort.toSend CcwPort.free := rfl

theorem joinA_of_cw (ch : Choice) (cw : CwPort) (ccw : CcwPort)
    (h : cw ≠ CwPort.heldDenial) :
    joinA (Agent.root ch cw ccw) = Agent.root ch cw ccw := by
  cases cw <;> cases ccw <;> simp_all [joinA]

theorem joinA_of_ccw (ch : Choice) (cw : CwPort) (ccw : CcwPort)
    (h : ccw ≠ CcwPort.heldDenial) :
    joinA (Agent.root ch cw ccw) = Agent.root ch cw ccw := by
  cases cw <;> cases ccw <;> simp_all [joinA]

/-! ## Reading the freeze guard off the phase vector -/

theorem isRaceRoot_interior (s : Slot) :
    isRaceRoot (Agent.interior s) = false := rfl

theorem isRaceRoot_base (R : RFrame) (cw : CwPort) (ccw : CcwPort) :
    isRaceRoot (Agent.root R.b cw ccw) = false := by
  rcases R.hb with h | h <;> rw [h] <;> rfl

theorem isRaceRoot_rootAgent (R : RFrame) (P : PV R) (g : Fin R.m) :
    isRaceRoot (rootAgent R P g) = joined R P g := by
  simp only [rootAgent]
  by_cases h : joined R P g = true
  · rw [if_pos h, h]; rfl
  · have hf : joined R P g = false := by
      cases hj : joined R P g
      · rfl
      · exact absurd hj h
    rw [if_neg h, hf, isRaceRoot_base R]

/-! ## Phase field readback -/

theorem cwOf_of_delivered (p : Phase) (h : IsDelivered p = true) :
    cwOf p = CwPort.heldDenial := by
  cases p <;> simp_all [IsDelivered, cwOf]

theorem cwOf_of_not_delivered (p : Phase) (h : IsDelivered p = false) :
    cwOf p ≠ CwPort.heldDenial := by
  cases p <;> simp_all [IsDelivered, cwOf]

theorem ccwOf_of_compared (p : Phase) (h : Compared p = true) :
    ccwOf p = CcwPort.heldDenial := by
  cases p <;> simp_all [Compared, ccwOf]

theorem ccwOf_of_not_compared (p : Phase) (h : Compared p = false) :
    ccwOf p = CcwPort.free := by
  cases p <;> simp_all [Compared, ccwOf]

theorem slotAgent_declAt_tok (R : RFrame) (j r : Nat) (h : r = j) :
    slotAgent R (Phase.declAt j) r = Agent.interior (Slot.decl R.b) := by
  simp only [slotAgent, if_pos h]

theorem slotAgent_declAt_off (R : RFrame) (j r : Nat) (h : r ≠ j) :
    slotAgent R (Phase.declAt j) r = Agent.interior Slot.empty := by
  simp only [slotAgent, if_neg h]

theorem slotAgent_replyAt_tok (R : RFrame) (j r : Nat) (h : r = j) :
    slotAgent R (Phase.replyAt j) r = Agent.interior (Slot.reply R.b) := by
  simp only [slotAgent, if_pos h]

theorem slotAgent_replyAt_off (R : RFrame) (j r : Nat) (h : r ≠ j) :
    slotAgent R (Phase.replyAt j) r = Agent.interior Slot.empty := by
  simp only [slotAgent, if_neg h]

theorem slotAgent_prelaunch (R : RFrame) (r : Nat) :
    slotAgent R Phase.prelaunch r = Agent.interior Slot.empty := rfl

theorem slotAgent_delivered (R : RFrame) (r : Nat) :
    slotAgent R Phase.delivered r = Agent.interior Slot.empty := rfl

/-- On a ring of one-edge gaps only the two extreme phases occur. -/
theorem phaseOk_h1 (R : RFrame) (p : Phase) (hp : PhaseOk (F0 R) p)
    (h1 : R.h = 1) : p = Phase.prelaunch ∨ p = Phase.delivered := by
  cases p with
  | prelaunch => exact Or.inl rfl
  | declAt j => exact absurd hp (by simp only [PhaseOk]; omega)
  | replyAt j => exact absurd hp (by simp only [PhaseOk]; omega)
  | delivered => exact Or.inr rfl

/-! ## The phase vector after one firing -/

/-- The phase vector after scheduling edge `e`: gap `e.1` advances by the
one-gap phase transition, unless the edge is frozen. -/
def nextP (R : RFrame) (P : PV R) (e : Vtx R) : PV R :=
  if frozen R (cfgOf R P) e then P
  else fun g => if g = e.1 then nextPhase (F0 R) (P e.1) e.2 else P g

theorem nextP_of_frozen (R : RFrame) (P : PV R) (e : Vtx R)
    (h : frozen R (cfgOf R P) e = true) : nextP R P e = P := by
  simp only [nextP, if_pos h]

theorem nextP_self (R : RFrame) (P : PV R) (e : Vtx R)
    (h : ¬ (frozen R (cfgOf R P) e = true)) :
    nextP R P e e.1 = nextPhase (F0 R) (P e.1) e.2 := by
  simp only [nextP, if_neg h]
  simp

theorem nextP_other (R : RFrame) (P : PV R) (e : Vtx R)
    (h : ¬ (frozen R (cfgOf R P) e = true)) (g : Fin R.m) (hg : g ≠ e.1) :
    nextP R P e g = P g := by
  simp only [nextP, if_neg h, if_neg hg]

theorem nextP_phaseOk (R : RFrame) (P : PV R) (hP : ∀ g, PhaseOk (F0 R) (P g))
    (e : Vtx R) (g : Fin R.m) : PhaseOk (F0 R) (nextP R P e g) := by
  by_cases h : frozen R (cfgOf R P) e = true
  · rw [nextP_of_frozen R P e h]; exact hP g
  · by_cases hg : g = e.1
    · rw [hg, nextP_self R P e h]
      exact nextPhase_phaseOk (F0 R) (P e.1) (hP e.1) e.2
    · rw [nextP_other R P e h g hg]; exact hP g

/-! ## Reduction lemmas for the simulation proof -/

theorem not_frozen_left (R : RFrame) (cfg : Vtx R → Agent) (e : Vtx R)
    (h : ¬ (frozen R cfg e = true)) : isRaceRoot (cfg e) = false := by
  cases hx : isRaceRoot (cfg e) with
  | false => rfl
  | true => exact absurd (by simp only [frozen, hx, Bool.true_or]) h

theorem not_frozen_right (R : RFrame) (cfg : Vtx R → Agent) (e : Vtx R)
    (h : ¬ (frozen R cfg e = true)) : isRaceRoot (cfg (rn R e)) = false := by
  cases hx : isRaceRoot (cfg (rn R e)) with
  | false => rfl
  | true => exact absurd (by simp only [frozen, hx, Bool.or_true]) h

/-- A firing whose row and JOIN are both the identity does not change the
configuration. -/
theorem ringStep_id (R : RFrame) (cfg : Vtx R → Agent) (e : Vtx R)
    (hfr : ¬ (frozen R cfg e = true))
    (hrow : row (cfg e) (cfg (rn R e)) = (cfg e, cfg (rn R e)))
    (hj1 : joinA (cfg e) = cfg e)
    (hj2 : joinA (cfg (rn R e)) = cfg (rn R e)) :
    ringStep R cfg e = cfg := by
  funext w
  by_cases hw1 : w = e
  · subst hw1
    rw [ringStep_left R cfg w hfr, hrow, hj1]
  · by_cases hw2 : w = rn R e
    · subst hw2
      rw [ringStep_right R cfg e hfr, hrow, hj2]
    · exact ringStep_frame R cfg e w hw1 hw2

/-- The two-endpoint update, matched against a target phase vector. -/
theorem cfgOf_ext (R : RFrame) (P P' : PV R) (e : Vtx R)
    (hfr : ¬ (frozen R (cfgOf R P) e = true))
    (h1 : joinA (row (cfgOf R P e) (cfgOf R P (rn R e))).1 = cfgOf R P' e)
    (h2 : joinA (row (cfgOf R P e) (cfgOf R P (rn R e))).2 = cfgOf R P' (rn R e))
    (h3 : ∀ w, w ≠ e → w ≠ rn R e → cfgOf R P' w = cfgOf R P w) :
    ringStep R (cfgOf R P) e = cfgOf R P' := by
  funext w
  by_cases hw1 : w = e
  · subst hw1
    rw [ringStep_left R _ w hfr, h1]
  · by_cases hw2 : w = rn R e
    · subst hw2
      rw [ringStep_right R _ e hfr, h2]
    · rw [ringStep_frame R _ e w hw1 hw2, h3 w hw1 hw2]

/-- Only gap `g`'s column and the two roots at its ends can change. -/
theorem cfgOf_rest (R : RFrame) (P P' : PV R) (g : Fin R.m)
    (hother : ∀ g', g' ≠ g → P' g' = P g') (w : Vtx R)
    (hrg : w.1 = g → w.2.val = 0 → rootAgent R P' g = rootAgent R P g)
    (hrn : w.1 = next R g → w.2.val = 0 →
      rootAgent R P' (next R g) = rootAgent R P (next R g))
    (hslot : w.1 = g → w.2.val ≠ 0 →
      slotAgent R (P' g) w.2.val = slotAgent R (P g) w.2.val) :
    cfgOf R P' w = cfgOf R P w := by
  by_cases hz : w.2.val = 0
  · rw [cfgOf_root R P' w hz, cfgOf_root R P w hz]
    by_cases hg : w.1 = g
    · rw [hg]; exact hrg hg hz
    · by_cases hn : w.1 = next R g
      · rw [hn]; exact hrn hn hz
      · have h1 : P' w.1 = P w.1 := hother _ hg
        have h2 : prev R w.1 ≠ g := fun hc => hn ((prev_eq_iff R g w.1).mp hc)
        have h3 : P' (prev R w.1) = P (prev R w.1) := hother _ h2
        simp only [rootAgent, joined, h1, h3]
        rfl
  · rw [cfgOf_slot R P' w hz, cfgOf_slot R P w hz]
    by_cases hg : w.1 = g
    · rw [hg]; exact hslot hg hz
    · rw [hother _ hg]

theorem rootAgent_congr (R : RFrame) (P P' : PV R) (g : Fin R.m)
    (hcw : cwOf (P' g) = cwOf (P g))
    (hdel : IsDelivered (P' g) = IsDelivered (P g))
    (hccw : ccwOf (P' (prev R g)) = ccwOf (P (prev R g)))
    (hcmp : Compared (P' (prev R g)) = Compared (P (prev R g))) :
    rootAgent R P' g = rootAgent R P g := by
  simp only [rootAgent, joined, hcw, hdel, hccw, hcmp]
  rfl

@[simp] theorem cwOf_prelaunch : cwOf Phase.prelaunch = CwPort.toSend := rfl
@[simp] theorem cwOf_declAt (j : Nat) :
    cwOf (Phase.declAt j) = CwPort.waiting := rfl
@[simp] theorem cwOf_replyAt (j : Nat) :
    cwOf (Phase.replyAt j) = CwPort.waiting := rfl
@[simp] theorem cwOf_delivered : cwOf Phase.delivered = CwPort.heldDenial := rfl
@[simp] theorem ccwOf_prelaunch : ccwOf Phase.prelaunch = CcwPort.free := rfl
@[simp] theorem ccwOf_declAt (j : Nat) :
    ccwOf (Phase.declAt j) = CcwPort.free := rfl
@[simp] theorem ccwOf_replyAt (j : Nat) :
    ccwOf (Phase.replyAt j) = CcwPort.heldDenial := rfl
@[simp] theorem ccwOf_delivered :
    ccwOf Phase.delivered = CcwPort.heldDenial := rfl

/-! ## Simulation: the interior-to-interior edges (`F1`, `B1`) -/

private theorem nextP_id (R : RFrame) (P : PV R) (e : Vtx R)
    (hfr : ¬ (frozen R (cfgOf R P) e = true))
    (hstay : nextPhase (F0 R) (P e.1) e.2 = P e.1) : nextP R P e = P := by
  funext g
  by_cases hg : g = e.1
  · rw [hg, nextP_self R P e hfr]; exact hstay
  · exact nextP_other R P e hfr g hg

private theorem step_case_B (R : RFrame) (P : PV R)
    (hP : ∀ g, PhaseOk (F0 R) (P g)) (e : Vtx R)
    (hfr : ¬ (frozen R (cfgOf R P) e = true))
    (hlt : e.2.val + 1 < R.h) (h0 : e.2.val ≠ 0) :
    ringStep R (cfgOf R P) e = cfgOf R (nextP R P e) := by
  have hrnE : rn R e = (e.1, ⟨e.2.val + 1, hlt⟩) := rn_of_lt R e hlt
  have hrn1 : (rn R e).1 = e.1 := by rw [hrnE]
  have hrn2 : (rn R e).2.val = e.2.val + 1 := by rw [hrnE]
  have hu : cfgOf R P e = slotAgent R (P e.1) e.2.val := cfgOf_slot R P e h0
  have hv : cfgOf R P (rn R e) = slotAgent R (P e.1) (e.2.val + 1) := by
    rw [cfgOf_slot R P (rn R e) (by rw [hrn2]; omega), hrn1, hrn2]
  have hprev : prev R e.1 ≠ e.1 := prev_ne_self R e.1
  have hnext : next R e.1 ≠ e.1 := next_ne_self R e.1
  cases hp : P e.1 with
  | prelaunch =>
      have hid : nextP R P e = P := by
        refine nextP_id R P e hfr ?_
        rw [hp]; simp only [nextPhase, if_neg h0]
      rw [hid]
      refine ringStep_id R _ e hfr ?_ ?_ ?_
      · rw [hu, hv, hp, slotAgent_prelaunch, slotAgent_prelaunch]
        exact row_II_ee
      · rw [hu, hp, slotAgent_prelaunch]; exact joinA_interior _
      · rw [hv, hp, slotAgent_prelaunch]; exact joinA_interior _
  | delivered =>
      have hid : nextP R P e = P := by
        refine nextP_id R P e hfr ?_
        rw [hp]; rfl
      rw [hid]
      refine ringStep_id R _ e hfr ?_ ?_ ?_
      · rw [hu, hv, hp, slotAgent_delivered, slotAgent_delivered]
        exact row_II_ee
      · rw [hu, hp, slotAgent_delivered]; exact joinA_interior _
      · rw [hv, hp, slotAgent_delivered]; exact joinA_interior _
  | declAt j =>
      have hpo := hP e.1
      rw [hp] at hpo
      simp only [PhaseOk] at hpo
      by_cases he : e.2.val = j
      · -- `F1`: the declaration hops one position clockwise.
        have hnp : nextP R P e e.1 = Phase.declAt (j + 1) := by
          rw [nextP_self R P e hfr, hp]
          simp only [nextPhase, if_pos he, if_neg (by omega : j + 1 ≠ R.h)]
        refine cfgOf_ext R P _ e hfr ?_ ?_ ?_
        · rw [hu, hv, hp, slotAgent_declAt_tok R j e.2.val he,
            slotAgent_declAt_off R j (e.2.val + 1) (by omega), row_F1,
            joinA_interior, cfgOf_slot R _ e h0, hnp,
            slotAgent_declAt_off R (j + 1) e.2.val (by omega)]
        · rw [hu, hv, hp, slotAgent_declAt_tok R j e.2.val he,
            slotAgent_declAt_off R j (e.2.val + 1) (by omega), row_F1,
            joinA_interior, cfgOf_slot R _ (rn R e) (by rw [hrn2]; omega),
            hrn1, hrn2, hnp, slotAgent_declAt_tok R (j + 1) (e.2.val + 1)
              (by omega)]
        · intro w hw1 hw2
          refine cfgOf_rest R P _ e.1
            (fun g' hg' => nextP_other R P e hfr g' hg') w ?_ ?_ ?_
          · intro hwg hwz
            refine rootAgent_congr R P _ e.1 ?_ ?_ ?_ ?_
            · rw [hnp, hp]; rfl
            · rw [hnp, hp]; rfl
            · rw [nextP_other R P e hfr _ hprev]
            · rw [nextP_other R P e hfr _ hprev]
          · intro hwg hwz
            refine rootAgent_congr R P _ (next R e.1) ?_ ?_ ?_ ?_
            · rw [nextP_other R P e hfr _ hnext]
            · rw [nextP_other R P e hfr _ hnext]
            · rw [prev_next, hnp, hp]; rfl
            · rw [prev_next, hnp, hp]; rfl
          · intro hwg hwz
            have hk1 : w.2.val ≠ e.2.val := fun hc => hw1 (vtx_eq R w e hwg hc)
            have hk2 : w.2.val ≠ e.2.val + 1 := fun hc =>
              hw2 (vtx_eq R w (rn R e) (by rw [hwg, hrn1]) (by rw [hrn2]; exact hc))
            rw [hnp, hp, slotAgent_declAt_off R (j + 1) w.2.val (by omega),
              slotAgent_declAt_off R j w.2.val (by omega)]
      · -- no useful firing at this edge.
        have hid : nextP R P e = P := by
          refine nextP_id R P e hfr ?_
          rw [hp]; simp only [nextPhase, if_neg he]
        rw [hid]
        have huu : slotAgent R (Phase.declAt j) e.2.val
            = Agent.interior Slot.empty := slotAgent_declAt_off R j e.2.val he
        refine ringStep_id R _ e hfr ?_ ?_ ?_
        · rw [hu, hv, hp, huu]
          by_cases he2 : e.2.val + 1 = j
          · rw [slotAgent_declAt_tok R j (e.2.val + 1) he2]; exact row_II_ed _
          · rw [slotAgent_declAt_off R j (e.2.val + 1) he2]; exact row_II_ee
        · rw [hu, hp, huu]; exact joinA_interior _
        · rw [hv, hp]
          by_cases he2 : e.2.val + 1 = j
          · rw [slotAgent_declAt_tok R j (e.2.val + 1) he2]
            exact joinA_interior _
          · rw [slotAgent_declAt_off R j (e.2.val + 1) he2]
            exact joinA_interior _
  | replyAt j =>
      have hpo := hP e.1
      rw [hp] at hpo
      simp only [PhaseOk] at hpo
      by_cases he : e.2.val + 1 = j
      · -- `B1`: the reply is pulled one position counterclockwise.
        have hnp : nextP R P e e.1 = Phase.replyAt (j - 1) := by
          rw [nextP_self R P e hfr, hp]
          simp only [nextPhase, if_pos he, if_neg (by omega : j ≠ 1)]
        refine cfgOf_ext R P _ e hfr ?_ ?_ ?_
        · rw [hu, hv, hp, slotAgent_replyAt_off R j e.2.val (by omega),
            slotAgent_replyAt_tok R j (e.2.val + 1) he, row_B1,
            joinA_interior, cfgOf_slot R _ e h0, hnp,
            slotAgent_replyAt_tok R (j - 1) e.2.val (by omega)]
        · rw [hu, hv, hp, slotAgent_replyAt_off R j e.2.val (by omega),
            slotAgent_replyAt_tok R j (e.2.val + 1) he, row_B1,
            joinA_interior, cfgOf_slot R _ (rn R e) (by rw [hrn2]; omega),
            hrn1, hrn2, hnp,
            slotAgent_replyAt_off R (j - 1) (e.2.val + 1) (by omega)]
        · intro w hw1 hw2
          refine cfgOf_rest R P _ e.1
            (fun g' hg' => nextP_other R P e hfr g' hg') w ?_ ?_ ?_
          · intro hwg hwz
            refine rootAgent_congr R P _ e.1 ?_ ?_ ?_ ?_
            · rw [hnp, hp]; rfl
            · rw [hnp, hp]; rfl
            · rw [nextP_other R P e hfr _ hprev]
            · rw [nextP_other R P e hfr _ hprev]
          · intro hwg hwz
            refine rootAgent_congr R P _ (next R e.1) ?_ ?_ ?_ ?_
            · rw [nextP_other R P e hfr _ hnext]
            · rw [nextP_other R P e hfr _ hnext]
            · rw [prev_next, hnp, hp]; rfl
            · rw [prev_next, hnp, hp]; rfl
          · intro hwg hwz
            have hk1 : w.2.val ≠ e.2.val := fun hc => hw1 (vtx_eq R w e hwg hc)
            have hk2 : w.2.val ≠ e.2.val + 1 := fun hc =>
              hw2 (vtx_eq R w (rn R e) (by rw [hwg, hrn1]) (by rw [hrn2]; exact hc))
            rw [hnp, hp, slotAgent_replyAt_off R (j - 1) w.2.val (by omega),
              slotAgent_replyAt_off R j w.2.val (by omega)]
      · -- no useful firing at this edge.
        have hid : nextP R P e = P := by
          refine nextP_id R P e hfr ?_
          rw [hp]; simp only [nextPhase, if_neg he]
        rw [hid]
        have hvv : slotAgent R (Phase.replyAt j) (e.2.val + 1)
            = Agent.interior Slot.empty := slotAgent_replyAt_off R j _ he
        refine ringStep_id R _ e hfr ?_ ?_ ?_
        · rw [hu, hv, hp, hvv]
          by_cases he2 : e.2.val = j
          · rw [slotAgent_replyAt_tok R j e.2.val he2]; exact row_II_r _ _
          · rw [slotAgent_replyAt_off R j e.2.val he2]; exact row_II_ee
        · rw [hu, hp]
          by_cases he2 : e.2.val = j
          · rw [slotAgent_replyAt_tok R j e.2.val he2]; exact joinA_interior _
          · rw [slotAgent_replyAt_off R j e.2.val he2]; exact joinA_interior _
        · rw [hv, hp, hvv]; exact joinA_interior _

/-! ## Simulation: the owner's edge (`L1`, `V1`) -/

private theorem step_case_A (R : RFrame) (P : PV R)
    (hP : ∀ g, PhaseOk (F0 R) (P g)) (e : Vtx R)
    (hfr : ¬ (frozen R (cfgOf R P) e = true))
    (hlt : e.2.val + 1 < R.h) (h0 : e.2.val = 0) :
    ringStep R (cfgOf R P) e = cfgOf R (nextP R P e) := by
  have hh2 : 1 < R.h := by omega
  have hrnE : rn R e = (e.1, ⟨e.2.val + 1, hlt⟩) := rn_of_lt R e hlt
  have hrn1 : (rn R e).1 = e.1 := by rw [hrnE]
  have hrn2 : (rn R e).2.val = 1 := by
    rw [hrnE]
    show e.2.val + 1 = 1
    omega
  have hprev : prev R e.1 ≠ e.1 := prev_ne_self R e.1
  have hnext : next R e.1 ≠ e.1 := next_ne_self R e.1
  have hpv : nextP R P e (prev R e.1) = P (prev R e.1) :=
    nextP_other R P e hfr _ hprev
  have hnv : nextP R P e (next R e.1) = P (next R e.1) :=
    nextP_other R P e hfr _ hnext
  have hjn : joined R P e.1 = false := by
    have hx := not_frozen_left R (cfgOf R P) e hfr
    rw [cfgOf_root R P e h0, isRaceRoot_rootAgent] at hx
    exact hx
  have hu : cfgOf R P e
      = Agent.root R.b (cwOf (P e.1)) (ccwOf (P (prev R e.1))) := by
    rw [cfgOf_root R P e h0, rootAgent, if_neg (by rw [hjn]; simp)]
  have hv : cfgOf R P (rn R e) = slotAgent R (P e.1) 1 := by
    rw [cfgOf_slot R P (rn R e) (by rw [hrn2]; omega), hrn1, hrn2]
  cases hp : P e.1 with
  | prelaunch =>
      -- `L1`: the owner launches its declaration.
      have hnp : nextP R P e e.1 = Phase.declAt 1 := by
        rw [nextP_self R P e hfr, hp]
        simp only [nextPhase, if_pos h0, if_neg (by omega : R.h ≠ 1)]
      refine cfgOf_ext R P _ e hfr ?_ ?_ ?_
      · rw [hu, hv, hp, slotAgent_prelaunch, cwOf, row_L1,
          joinA_of_cw _ _ _ (by simp), cfgOf_root R _ e h0, rootAgent, joined,
          hnp, hpv]
        simp only [IsDelivered, Bool.false_and, if_neg (by simp : ¬ (false = true)),
          cwOf]
      · rw [hu, hv, hp, slotAgent_prelaunch, cwOf, row_L1, joinA_interior,
          cfgOf_slot R _ (rn R e) (by rw [hrn2]; omega), hrn1, hrn2, hnp,
          slotAgent_declAt_tok R 1 1 rfl]
      · intro w hw1 hw2
        refine cfgOf_rest R P _ e.1
          (fun g' hg' => nextP_other R P e hfr g' hg') w ?_ ?_ ?_
        · intro hwg hwz
          exact absurd (vtx_eq R w e hwg (by rw [hwz, h0])) hw1
        · intro hwg hwz
          refine rootAgent_congr R P _ (next R e.1) ?_ ?_ ?_ ?_
          · rw [hnv]
          · rw [hnv]
          · rw [prev_next, hnp, hp]; rfl
          · rw [prev_next, hnp, hp]; rfl
        · intro hwg hwz
          have hk2 : w.2.val ≠ 1 := fun hc =>
            hw2 (vtx_eq R w (rn R e) (by rw [hwg, hrn1]) (by rw [hrn2]; exact hc))
          rw [hnp, hp, slotAgent_declAt_off R 1 w.2.val hk2, slotAgent_prelaunch]
  | delivered =>
      have hcmp : Compared (P (prev R e.1)) = false := by
        have hx := hjn
        rw [joined, hp] at hx
        simp only [IsDelivered, Bool.true_and] at hx
        exact hx
      have hid : nextP R P e = P := by
        refine nextP_id R P e hfr ?_
        rw [hp]; rfl
      rw [hid]
      refine ringStep_id R _ e hfr ?_ ?_ ?_
      · rw [hu, hv, hp, slotAgent_delivered, cwOf]
        exact row_RI_empty R _ _ (by simp)
      · rw [hu, hp, cwOf, ccwOf_of_not_compared _ hcmp]
        exact joinA_of_ccw _ _ _ (by simp)
      · rw [hv, hp, slotAgent_delivered]; exact joinA_interior _
  | declAt j =>
      have hpo := hP e.1
      rw [hp] at hpo
      simp only [PhaseOk] at hpo
      have hid : nextP R P e = P := by
        refine nextP_id R P e hfr ?_
        rw [hp]; simp only [nextPhase, if_neg (by omega : ¬ (e.2.val = j))]
      rw [hid]
      refine ringStep_id R _ e hfr ?_ ?_ ?_
      · rw [hu, hv, hp, cwOf]
        by_cases hj : (1 : Nat) = j
        · rw [slotAgent_declAt_tok R j 1 hj]; exact row_RI_decl R _ _ _
        · rw [slotAgent_declAt_off R j 1 hj]; exact row_RI_empty R _ _ (by simp)
      · rw [hu, hp, cwOf]; exact joinA_of_cw _ _ _ (by simp)
      · rw [hv, hp]
        by_cases hj : (1 : Nat) = j
        · rw [slotAgent_declAt_tok R j 1 hj]; exact joinA_interior _
        · rw [slotAgent_declAt_off R j 1 hj]; exact joinA_interior _
  | replyAt j =>
      have hpo := hP e.1
      rw [hp] at hpo
      simp only [PhaseOk] at hpo
      by_cases hj : j = 1
      · -- `V1`: the owner receives its receipt, and JOINs if its
        -- counterclockwise port already held a denial.
        have hnp : nextP R P e e.1 = Phase.delivered := by
          rw [nextP_self R P e hfr, hp]
          simp only [nextPhase, if_pos (by omega : e.2.val + 1 = j), if_pos hj]
        have hcfg1 : cfgOf R (nextP R P e) e
            = (if Compared (P (prev R e.1)) = true then
                Agent.root Choice.race CwPort.toSend CcwPort.free
              else Agent.root R.b CwPort.heldDenial (ccwOf (P (prev R e.1)))) := by
          rw [cfgOf_root R _ e h0, rootAgent, joined, hnp, hpv]
          simp only [IsDelivered, Bool.true_and, cwOf]
        refine cfgOf_ext R P _ e hfr ?_ ?_ ?_
        · rw [hu, hv, hp, cwOf, slotAgent_replyAt_tok R j 1 hj.symm, row_V1,
            hcfg1]
          by_cases hc : Compared (P (prev R e.1)) = true
          · rw [if_pos hc, ccwOf_of_compared _ hc]
            exact joinA_join _
          · have hc' : Compared (P (prev R e.1)) = false := by
              cases hx : Compared (P (prev R e.1)) with
              | false => rfl
              | true => exact absurd hx hc
            rw [if_neg hc, ccwOf_of_not_compared _ hc']
            exact joinA_of_ccw _ _ _ (by simp)
        · rw [hu, hv, hp, cwOf, slotAgent_replyAt_tok R j 1 hj.symm, row_V1,
            joinA_interior, cfgOf_slot R _ (rn R e) (by rw [hrn2]; omega),
            hrn1, hrn2, hnp, slotAgent_delivered]
        · intro w hw1 hw2
          refine cfgOf_rest R P _ e.1
            (fun g' hg' => nextP_other R P e hfr g' hg') w ?_ ?_ ?_
          · intro hwg hwz
            exact absurd (vtx_eq R w e hwg (by rw [hwz, h0])) hw1
          · intro hwg hwz
            refine rootAgent_congr R P _ (next R e.1) ?_ ?_ ?_ ?_
            · rw [hnv]
            · rw [hnv]
            · rw [prev_next, hnp, hp, hj]; rfl
            · rw [prev_next, hnp, hp, hj]; rfl
          · intro hwg hwz
            have hk2 : w.2.val ≠ 1 := fun hc =>
              hw2 (vtx_eq R w (rn R e) (by rw [hwg, hrn1]) (by rw [hrn2]; exact hc))
            rw [hnp, hp, slotAgent_delivered,
              slotAgent_replyAt_off R j w.2.val (by omega)]
      · have hid : nextP R P e = P := by
          refine nextP_id R P e hfr ?_
          rw [hp]; simp only [nextPhase,
            if_neg (by omega : ¬ (e.2.val + 1 = j))]
        rw [hid]
        have hvv : slotAgent R (Phase.replyAt j) 1 = Agent.interior Slot.empty :=
          slotAgent_replyAt_off R j 1 (by omega)
        refine ringStep_id R _ e hfr ?_ ?_ ?_
        · rw [hu, hv, hp, cwOf, hvv]; exact row_RI_empty R _ _ (by simp)
        · rw [hu, hp, cwOf]; exact joinA_of_cw _ _ _ (by simp)
        · rw [hv, hp, hvv]; exact joinA_interior _

/-! ## Simulation: the shared root's edge (`K1`, `K3`, `K4`) -/

private theorem step_case_C (R : RFrame) (P : PV R)
    (hP : ∀ g, PhaseOk (F0 R) (P g)) (e : Vtx R)
    (hfr : ¬ (frozen R (cfgOf R P) e = true))
    (hlast : ¬ (e.2.val + 1 < R.h)) (h0 : e.2.val ≠ 0) :
    ringStep R (cfgOf R P) e = cfgOf R (nextP R P e) := by
  have hle : e.2.val + 1 = R.h := by have := e.2.isLt; omega
  have hrnE : rn R e = (next R e.1, ⟨0, R.hh⟩) := rn_of_last R e hlast
  have hrn1 : (rn R e).1 = next R e.1 := by rw [hrnE]
  have hrn2 : (rn R e).2.val = 0 := by rw [hrnE]
  have hprev : prev R e.1 ≠ e.1 := prev_ne_self R e.1
  have hnext : next R e.1 ≠ e.1 := next_ne_self R e.1
  have hpv : nextP R P e (prev R e.1) = P (prev R e.1) :=
    nextP_other R P e hfr _ hprev
  have hnv : nextP R P e (next R e.1) = P (next R e.1) :=
    nextP_other R P e hfr _ hnext
  have hjn2 : joined R P (next R e.1) = false := by
    have hx := not_frozen_right R (cfgOf R P) e hfr
    rw [cfgOf_root R P (rn R e) hrn2, hrn1, isRaceRoot_rootAgent] at hx
    exact hx
  have hu : cfgOf R P e = slotAgent R (P e.1) e.2.val := cfgOf_slot R P e h0
  have hv : cfgOf R P (rn R e)
      = Agent.root R.b (cwOf (P (next R e.1))) (ccwOf (P e.1)) := by
    rw [cfgOf_root R P (rn R e) hrn2, hrn1, rootAgent,
      if_neg (by rw [hjn2]; simp), prev_next]
  cases hp : P e.1 with
  | prelaunch =>
      have hid : nextP R P e = P := by
        refine nextP_id R P e hfr ?_
        rw [hp]; simp only [nextPhase, if_neg h0]
      rw [hid]
      refine ringStep_id R _ e hfr ?_ ?_ ?_
      · rw [hu, hv, hp, slotAgent_prelaunch, ccwOf_prelaunch]
        exact row_K4_empty R _ _
      · rw [hu, hp, slotAgent_prelaunch]; exact joinA_interior _
      · rw [hv, hp, ccwOf_prelaunch]; exact joinA_of_ccw _ _ _ (by simp)
  | delivered =>
      have hnd : IsDelivered (P (next R e.1)) = false := by
        have hx := hjn2
        rw [joined, prev_next, hp] at hx
        simp only [Compared, Bool.and_true] at hx
        exact hx
      have hid : nextP R P e = P := by
        refine nextP_id R P e hfr ?_
        rw [hp]; rfl
      rw [hid]
      refine ringStep_id R _ e hfr ?_ ?_ ?_
      · rw [hu, hv, hp, slotAgent_delivered]
        exact row_K4_empty R _ _
      · rw [hu, hp, slotAgent_delivered]; exact joinA_interior _
      · rw [hv, hp]
        exact joinA_of_cw _ _ _ (cwOf_of_not_delivered _ hnd)
  | declAt j =>
      have hpo := hP e.1
      rw [hp] at hpo
      simp only [PhaseOk] at hpo
      by_cases hj : e.2.val = j
      · -- `K1`: the shared root compares, and JOINs if its clockwise port
        -- already held a denial.
        have hnp : nextP R P e e.1 = Phase.replyAt j := by
          rw [nextP_self R P e hfr, hp]
          simp only [nextPhase, if_pos hj, if_pos (by omega : j + 1 = R.h)]
        have hcfg2 : cfgOf R (nextP R P e) (rn R e)
            = (if IsDelivered (P (next R e.1)) = true then
                Agent.root Choice.race CwPort.toSend CcwPort.free
              else Agent.root R.b (cwOf (P (next R e.1)))
                CcwPort.heldDenial) := by
          rw [cfgOf_root R _ (rn R e) hrn2, hrn1, rootAgent, joined, prev_next,
            hnv, hnp]
          simp only [Compared, Bool.and_true, ccwOf_replyAt]
        refine cfgOf_ext R P _ e hfr ?_ ?_ ?_
        · rw [hu, hv, hp, slotAgent_declAt_tok R j e.2.val hj, ccwOf_declAt, row_K1,
            joinA_interior, cfgOf_slot R _ e h0, hnp,
            slotAgent_replyAt_tok R j e.2.val hj]
        · rw [hu, hv, hp, slotAgent_declAt_tok R j e.2.val hj, ccwOf_declAt, row_K1,
            hcfg2]
          by_cases hd : IsDelivered (P (next R e.1)) = true
          · rw [if_pos hd, cwOf_of_delivered _ hd]
            exact joinA_join _
          · have hd' : IsDelivered (P (next R e.1)) = false := by
              cases hx : IsDelivered (P (next R e.1)) with
              | false => rfl
              | true => exact absurd hx hd
            rw [if_neg hd]
            exact joinA_of_cw _ _ _ (cwOf_of_not_delivered _ hd')
        · intro w hw1 hw2
          refine cfgOf_rest R P _ e.1
            (fun g' hg' => nextP_other R P e hfr g' hg') w ?_ ?_ ?_
          · intro hwg hwz
            refine rootAgent_congr R P _ e.1 ?_ ?_ ?_ ?_
            · rw [hnp, hp]; rfl
            · rw [hnp, hp]; rfl
            · rw [hpv]
            · rw [hpv]
          · intro hwg hwz
            exact absurd (vtx_eq R w (rn R e) (by rw [hwg, hrn1])
              (by rw [hrn2]; exact hwz)) hw2
          · intro hwg hwz
            have hk1 : w.2.val ≠ e.2.val := fun hc => hw1 (vtx_eq R w e hwg hc)
            rw [hnp, hp, slotAgent_replyAt_off R j w.2.val (by omega),
              slotAgent_declAt_off R j w.2.val (by omega)]
      · have hid : nextP R P e = P := by
          refine nextP_id R P e hfr ?_
          rw [hp]; simp only [nextPhase, if_neg hj]
        rw [hid]
        have huu : slotAgent R (Phase.declAt j) e.2.val
            = Agent.interior Slot.empty := slotAgent_declAt_off R j _ hj
        refine ringStep_id R _ e hfr ?_ ?_ ?_
        · rw [hu, hv, hp, huu, ccwOf_declAt]; exact row_K4_empty R _ _
        · rw [hu, hp, huu]; exact joinA_interior _
        · rw [hv, hp, ccwOf_declAt]; exact joinA_of_ccw _ _ _ (by simp)
  | replyAt j =>
      have hpo := hP e.1
      rw [hp] at hpo
      simp only [PhaseOk] at hpo
      have hnd : IsDelivered (P (next R e.1)) = false := by
        have hx := hjn2
        rw [joined, prev_next, hp] at hx
        simp only [Compared, Bool.and_true] at hx
        exact hx
      have hid : nextP R P e = P := by
        refine nextP_id R P e hfr ?_
        rw [hp]
        simp only [nextPhase, if_neg (by omega : ¬ (e.2.val + 1 = j))]
      rw [hid]
      refine ringStep_id R _ e hfr ?_ ?_ ?_
      · rw [hu, hv, hp]
        by_cases hj : e.2.val = j
        · rw [slotAgent_replyAt_tok R j e.2.val hj]
          exact row_K4_reply R _ _ _
        · rw [slotAgent_replyAt_off R j e.2.val hj]
          exact row_K4_empty R _ _
      · rw [hu, hp]
        by_cases hj : e.2.val = j
        · rw [slotAgent_replyAt_tok R j e.2.val hj]; exact joinA_interior _
        · rw [slotAgent_replyAt_off R j e.2.val hj]; exact joinA_interior _
      · rw [hv, hp]
        exact joinA_of_cw _ _ _ (cwOf_of_not_delivered _ hnd)

/-! ## Simulation: a gap of length one (`P1`, `P2`, `P3`) -/

private theorem step_case_D (R : RFrame) (P : PV R)
    (hP : ∀ g, PhaseOk (F0 R) (P g)) (e : Vtx R)
    (hfr : ¬ (frozen R (cfgOf R P) e = true))
    (hlast : ¬ (e.2.val + 1 < R.h)) (h0 : e.2.val = 0) :
    ringStep R (cfgOf R P) e = cfgOf R (nextP R P e) := by
  have hh1 : R.h = 1 := by have := R.hh; omega
  have hrnE : rn R e = (next R e.1, ⟨0, R.hh⟩) := rn_of_last R e hlast
  have hrn1 : (rn R e).1 = next R e.1 := by rw [hrnE]
  have hrn2 : (rn R e).2.val = 0 := by rw [hrnE]
  have hprev : prev R e.1 ≠ e.1 := prev_ne_self R e.1
  have hnext : next R e.1 ≠ e.1 := next_ne_self R e.1
  have hpv : nextP R P e (prev R e.1) = P (prev R e.1) :=
    nextP_other R P e hfr _ hprev
  have hnv : nextP R P e (next R e.1) = P (next R e.1) :=
    nextP_other R P e hfr _ hnext
  have hzero : ∀ w : Vtx R, w.2.val = 0 := by
    intro w; have := w.2.isLt; omega
  have hjn : joined R P e.1 = false := by
    have hx := not_frozen_left R (cfgOf R P) e hfr
    rw [cfgOf_root R P e h0, isRaceRoot_rootAgent] at hx
    exact hx
  have hjn2 : joined R P (next R e.1) = false := by
    have hx := not_frozen_right R (cfgOf R P) e hfr
    rw [cfgOf_root R P (rn R e) hrn2, hrn1, isRaceRoot_rootAgent] at hx
    exact hx
  have hu : cfgOf R P e
      = Agent.root R.b (cwOf (P e.1)) (ccwOf (P (prev R e.1))) := by
    rw [cfgOf_root R P e h0, rootAgent, if_neg (by rw [hjn]; simp)]
  have hv : cfgOf R P (rn R e)
      = Agent.root R.b (cwOf (P (next R e.1))) (ccwOf (P e.1)) := by
    rw [cfgOf_root R P (rn R e) hrn2, hrn1, rootAgent,
      if_neg (by rw [hjn2]; simp), prev_next]
  rcases phaseOk_h1 R (P e.1) (hP e.1) hh1 with hp | hp
  · -- `P1`: one firing serves both roots, and both JOINs may fire with it.
    have hnp : nextP R P e e.1 = Phase.delivered := by
      rw [nextP_self R P e hfr, hp]
      simp only [nextPhase, if_pos h0, if_pos hh1]
    have hcfg1 : cfgOf R (nextP R P e) e
        = (if Compared (P (prev R e.1)) = true then
            Agent.root Choice.race CwPort.toSend CcwPort.free
          else Agent.root R.b CwPort.heldDenial (ccwOf (P (prev R e.1)))) := by
      rw [cfgOf_root R _ e h0, rootAgent, joined, hnp, hpv]
      simp only [IsDelivered, Bool.true_and, cwOf_delivered]
    have hcfg2 : cfgOf R (nextP R P e) (rn R e)
        = (if IsDelivered (P (next R e.1)) = true then
            Agent.root Choice.race CwPort.toSend CcwPort.free
          else Agent.root R.b (cwOf (P (next R e.1)))
            CcwPort.heldDenial) := by
      rw [cfgOf_root R _ (rn R e) hrn2, hrn1, rootAgent, joined, prev_next,
        hnv, hnp]
      simp only [Compared, Bool.and_true, ccwOf_delivered]
    refine cfgOf_ext R P _ e hfr ?_ ?_ ?_
    · rw [hu, hv, hp, cwOf_prelaunch, ccwOf_prelaunch, row_P1, hcfg1]
      by_cases hc : Compared (P (prev R e.1)) = true
      · rw [if_pos hc, ccwOf_of_compared _ hc]
        exact joinA_join _
      · have hc' : Compared (P (prev R e.1)) = false := by
          cases hx : Compared (P (prev R e.1)) with
          | false => rfl
          | true => exact absurd hx hc
        rw [if_neg hc, ccwOf_of_not_compared _ hc']
        exact joinA_of_ccw _ _ _ (by simp)
    · rw [hu, hv, hp, cwOf_prelaunch, ccwOf_prelaunch, row_P1, hcfg2]
      by_cases hd : IsDelivered (P (next R e.1)) = true
      · rw [if_pos hd, cwOf_of_delivered _ hd]
        exact joinA_join _
      · have hd' : IsDelivered (P (next R e.1)) = false := by
          cases hx : IsDelivered (P (next R e.1)) with
          | false => rfl
          | true => exact absurd hx hd
        rw [if_neg hd]
        exact joinA_of_cw _ _ _ (cwOf_of_not_delivered _ hd')
    · intro w hw1 hw2
      refine cfgOf_rest R P _ e.1
        (fun g' hg' => nextP_other R P e hfr g' hg') w ?_ ?_ ?_
      · intro hwg hwz
        exact absurd (vtx_eq R w e hwg (by rw [hwz, h0])) hw1
      · intro hwg hwz
        exact absurd (vtx_eq R w (rn R e) (by rw [hwg, hrn1])
          (by rw [hrn2]; exact hwz)) hw2
      · intro hwg hwz
        exact absurd (hzero w) hwz
  · -- the gap has already been served: every row is a no-op.
    have hcmp : Compared (P (prev R e.1)) = false := by
      have hx := hjn
      rw [joined, hp] at hx
      simp only [IsDelivered, Bool.true_and] at hx
      exact hx
    have hnd : IsDelivered (P (next R e.1)) = false := by
      have hx := hjn2
      rw [joined, prev_next, hp] at hx
      simp only [Compared, Bool.and_true] at hx
      exact hx
    have hid : nextP R P e = P := by
      refine nextP_id R P e hfr ?_
      rw [hp]; rfl
    rw [hid]
    refine ringStep_id R _ e hfr ?_ ?_ ?_
    · rw [hu, hv, hp, cwOf_delivered]
      exact row_RR_noSend R _ _ _ _ (by simp)
    · rw [hu, hp, cwOf_delivered, ccwOf_of_not_compared _ hcmp]
      exact joinA_of_ccw _ _ _ (by simp)
    · rw [hv, hp]
      exact joinA_of_cw _ _ _ (cwOf_of_not_delivered _ hnd)

/-! ## The simulation theorem -/

/-- The literal rows plus the post-step JOIN carry the ring configuration of a
phase vector to the ring configuration of the phase vector advanced at the
fired edge's gap. -/
theorem ringStep_cfgOf (R : RFrame) (P : PV R)
    (hP : ∀ g, PhaseOk (F0 R) (P g)) (e : Vtx R) :
    ringStep R (cfgOf R P) e = cfgOf R (nextP R P e) := by
  by_cases hfr : frozen R (cfgOf R P) e = true
  · rw [ringStep_frozen R _ e hfr, nextP_of_frozen R P e hfr]
  · by_cases hlt : e.2.val + 1 < R.h
    · by_cases h0 : e.2.val = 0
      · exact step_case_A R P hP e hfr hlt h0
      · exact step_case_B R P hP e hfr hlt h0
    · by_cases h0 : e.2.val = 0
      · exact step_case_D R P hP e hfr hlt h0
      · exact step_case_C R P hP e hfr hlt h0

/-! ## The ring-clean lane -/

/-- A ring configuration is clean when it is the configuration of a phase
vector: every gap is in one of its four clean phases, every root's fields agree
with the phases of the two gaps it borders, and a root is `race` exactly when
its own gap has delivered and the previous gap has compared, i.e. exactly when
its post-step JOIN has fired. -/
def RingClean (R : RFrame) (cfg : Vtx R → Agent) : Prop :=
  ∃ P : PV R, (∀ g, PhaseOk (F0 R) (P g)) ∧ cfg = cfgOf R P

/-- Section 3.4: every physical edge preserves the ring-clean lane.  An edge
belongs to exactly one gap, its rows write only that gap's interior slots and
the two shared roots' fields that belong to that gap, and the post-step JOIN
fires exactly when the second of a root's two denials arrives. -/
theorem ringClean_step (R : RFrame) (cfg : Vtx R → Agent)
    (hcl : RingClean R cfg) (e : Vtx R) : RingClean R (ringStep R cfg e) := by
  obtain ⟨P, hP, rfl⟩ := hcl
  exact ⟨nextP R P e, nextP_phaseOk R P hP e, ringStep_cfgOf R P hP e⟩

/-! ## The service debt -/

/-- Debt of a root: a pre-launch owner still owes the `2h-1` firings of its
gap.  A joined root is in `race`, not in the base `b`, and owes nothing. -/
def rootDebt (R : RFrame) : Agent → Nat
  | .root ch .toSend _ => if ch = R.b then 2 * R.h - 1 else 0
  | _ => 0

/-- Debt of an interior agent at offset `r`. -/
def slotDebt (R : RFrame) (r : Nat) : Agent → Nat
  | .interior (.decl _) => 2 * R.h - 1 - r
  | .interior (.reply _) => r
  | _ => 0

/-- Per-site debt inside a gap. -/
def siteDebtR (R : RFrame) (r : Nat) (a : Agent) : Nat :=
  if r = 0 then rootDebt R a else slotDebt R r a

/-- `δ_g`: the debt of gap `g`, summed over its root and its interior. -/
def gapDebt (R : RFrame) (cfg : Vtx R → Agent) (g : Fin R.m) : Nat :=
  (List.ofFn (fun r : Fin R.h => siteDebtR R r.val (cfg (g, r)))).sum

/-- `D = Σ_g δ_g`: the service debt of the whole ring. -/
def D (R : RFrame) (cfg : Vtx R → Agent) : Nat :=
  (List.ofFn (fun g : Fin R.m => gapDebt R cfg g)).sum

theorem rootDebt_toSend_base (R : RFrame) (X : CcwPort) :
    rootDebt R (Agent.root R.b CwPort.toSend X) = 2 * R.h - 1 := by
  simp [rootDebt]

theorem rootDebt_race (R : RFrame) :
    rootDebt R (Agent.root Choice.race CwPort.toSend CcwPort.free) = 0 := by
  have hne : ¬ (Choice.race = R.b) := fun hc => b_ne_race R (Eq.symm hc)
  simp only [rootDebt, if_neg hne]

theorem rootDebt_waiting (R : RFrame) (ch : Choice) (X : CcwPort) :
    rootDebt R (Agent.root ch CwPort.waiting X) = 0 := rfl

theorem rootDebt_held (R : RFrame) (ch : Choice) (X : CcwPort) :
    rootDebt R (Agent.root ch CwPort.heldDenial X) = 0 := rfl

theorem slotDebt_empty (R : RFrame) (r : Nat) :
    slotDebt R r (Agent.interior Slot.empty) = 0 := rfl

theorem slotDebt_decl (R : RFrame) (r : Nat) (c : Choice) :
    slotDebt R r (Agent.interior (Slot.decl c)) = 2 * R.h - 1 - r := rfl

theorem slotDebt_reply (R : RFrame) (r : Nat) (d : Choice) :
    slotDebt R r (Agent.interior (Slot.reply d)) = r := rfl

/-- The root of a gap owes the gap's whole service exactly in phase (a); it
owes nothing while waiting, after delivery, and after its JOIN. -/
private theorem rootDebt_rootAgent (R : RFrame) (P : PV R) (g : Fin R.m) :
    rootDebt R (rootAgent R P g)
      = (if P g = Phase.prelaunch then 2 * R.h - 1 else 0) := by
  by_cases hj : joined R P g = true
  · have hd : IsDelivered (P g) = true := by
      rw [joined] at hj
      exact (Bool.and_eq_true _ _ ▸ hj).1
    have hnp : P g ≠ Phase.prelaunch := by
      intro hc; rw [hc] at hd; exact absurd hd (by simp [IsDelivered])
    rw [rootAgent, if_pos hj, rootDebt_race, if_neg hnp]
  · rw [rootAgent, if_neg hj]
    cases hp : P g with
    | prelaunch => rw [cwOf_prelaunch, rootDebt_toSend_base, if_pos rfl]
    | declAt j =>
        rw [cwOf_declAt, rootDebt_waiting, if_neg (by simp)]
    | replyAt j =>
        rw [cwOf_replyAt, rootDebt_waiting, if_neg (by simp)]
    | delivered =>
        rw [cwOf_delivered, rootDebt_held, if_neg (by simp)]

/-- Gap debt on the clean lane is the paper's `δ` of Section 3.2. -/
theorem gapDebt_cfgOf (R : RFrame) (P : PV R) (g : Fin R.m)
    (hp : PhaseOk (F0 R) (P g)) :
    gapDebt R (cfgOf R P) g = phaseDebt (F0 R) (P g) := by
  have hhpos := R.hh
  have hsite : ∀ r : Fin R.h, siteDebtR R r.val (cfgOf R P (g, r))
      = (if r.val = 0 then (if P g = Phase.prelaunch then 2 * R.h - 1 else 0)
         else slotDebt R r.val (slotAgent R (P g) r.val)) := by
    intro r
    by_cases hz : r.val = 0
    · rw [siteDebtR, if_pos hz, cfgOf_root R P (g, r) hz, rootDebt_rootAgent,
        if_pos hz]
    · rw [siteDebtR, if_neg hz, cfgOf_slot R P (g, r) hz, if_neg hz]
  cases hph : P g with
  | prelaunch =>
      rw [gapDebt, ofFn_sum_single _ (⟨0, hhpos⟩ : Fin R.h)]
      · rw [hsite ⟨0, hhpos⟩]
        simp only [hph]
        rfl
      · intro k hk
        have hk0 : k.val ≠ 0 := fun hc => hk (Fin.ext hc)
        rw [hsite k, if_neg hk0, hph, slotAgent_prelaunch, slotDebt_empty]
  | delivered =>
      rw [gapDebt, ofFn_sum_eq_zero]
      · rfl
      · intro k
        by_cases hz : k.val = 0
        · rw [hsite k, if_pos hz, hph, if_neg (by simp)]
        · rw [hsite k, if_neg hz, hph, slotAgent_delivered, slotDebt_empty]
  | declAt j =>
      rw [hph] at hp
      simp only [PhaseOk] at hp
      rw [gapDebt, ofFn_sum_single _ (⟨j, by omega⟩ : Fin R.h)]
      · rw [hsite ⟨j, by omega⟩, if_neg (by simp only []; omega), hph,
          slotAgent_declAt_tok R j j rfl, slotDebt_decl]
        rfl
      · intro k hk
        have hkj : k.val ≠ j := fun hc => hk (Fin.ext hc)
        by_cases hz : k.val = 0
        · rw [hsite k, if_pos hz, hph, if_neg (by simp)]
        · rw [hsite k, if_neg hz, hph, slotAgent_declAt_off R j k.val hkj,
            slotDebt_empty]
  | replyAt j =>
      rw [hph] at hp
      simp only [PhaseOk] at hp
      rw [gapDebt, ofFn_sum_single _ (⟨j, by omega⟩ : Fin R.h)]
      · rw [hsite ⟨j, by omega⟩, if_neg (by simp only []; omega), hph,
          slotAgent_replyAt_tok R j j rfl, slotDebt_reply]
        rfl
      · intro k hk
        have hkj : k.val ≠ j := fun hc => hk (Fin.ext hc)
        by_cases hz : k.val = 0
        · rw [hsite k, if_pos hz, hph, if_neg (by simp)]
        · rw [hsite k, if_neg hz, hph, slotAgent_replyAt_off R j k.val hkj,
            slotDebt_empty]

/-- The ring debt on the clean lane is the sum of the per-gap phase debts. -/
theorem D_cfgOf (R : RFrame) (P : PV R) (hP : ∀ g, PhaseOk (F0 R) (P g)) :
    D R (cfgOf R P)
      = (List.ofFn (fun g : Fin R.m => phaseDebt (F0 R) (P g))).sum :=
  ofFn_sum_eq _ _ (fun g => gapDebt_cfgOf R P g (hP g))

/-! ## Scheduler edges of the ring -/

private theorem ofFn_sum_pred : ∀ {N : Nat} (f g : Fin N → Nat) (i : Fin N),
    (∀ k, k ≠ i → f k = g k) → f i + 1 = g i →
    (List.ofFn f).sum + 1 = (List.ofFn g).sum := by
  intro N
  induction N with
  | zero => intro _ _ i _ _; exact Fin.elim0 i
  | succ N ih =>
      intro f g i heq hi
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      by_cases h0 : i.val = 0
      · have hi0 : i = (0 : Fin (N + 1)) := Fin.ext (by simp [h0])
        have htail : (List.ofFn (fun k : Fin N => f k.succ)).sum
            = (List.ofFn (fun k : Fin N => g k.succ)).sum :=
          ofFn_sum_eq _ _ (fun k => heq k.succ (by
            intro hk
            rw [hi0] at hk
            have hv := congrArg Fin.val hk
            simp only [Fin.val_succ] at hv
            omega))
        have hhead : f 0 + 1 = g 0 := by rw [← hi0]; exact hi
        omega
      · have hpos : 0 < i.val := Nat.pos_of_ne_zero h0
        have hprev : i.val - 1 < N := by have := i.isLt; omega
        have hsucc : (⟨i.val - 1, hprev⟩ : Fin N).succ = i :=
          Fin.ext (by simp only [Fin.val_succ]; omega)
        have hhead : f 0 = g 0 := heq 0 (fun hk => h0 (by rw [← hk]; rfl))
        have htail := ih (fun k : Fin N => f k.succ) (fun k => g k.succ)
          ⟨i.val - 1, hprev⟩
          (fun k hk => heq k.succ (by
            intro hc
            apply hk
            apply Fin.ext
            have hv := congrArg Fin.val hc
            simp only [Fin.val_succ] at hv
            simp only []
            omega))
          (by rw [hsucc]; exact hi)
        omega

/-- The vertex whose outgoing edge is scheduler edge `k`. -/
def edgeVtx (R : RFrame) (k : Fin R.n) : Vtx R :=
  (⟨k.val / R.h, by
      have hk : k.val < R.m * R.h := k.isLt
      exact (Nat.div_lt_iff_lt_mul R.hh).mpr hk⟩,
   ⟨k.val % R.h, Nat.mod_lt _ R.hh⟩)

/-- The scheduler index of the edge leaving offset `a` of gap `g`. -/
def encE (R : RFrame) (g : Fin R.m) (a : Fin R.h) : Fin R.n :=
  ⟨R.h * g.val + a.val, by
    have h1 : g.val + 1 ≤ R.m := g.isLt
    have h2 : R.h * (g.val + 1) ≤ R.h * R.m := Nat.mul_le_mul_left _ h1
    have h3 : R.h * (g.val + 1) = R.h * g.val + R.h := by
      rw [Nat.mul_add, Nat.mul_one]
    have h4 : R.h * R.m = R.m * R.h := Nat.mul_comm _ _
    have h5 : a.val < R.h := a.isLt
    show R.h * g.val + a.val < R.m * R.h
    omega⟩

theorem edgeVtx_encE (R : RFrame) (g : Fin R.m) (a : Fin R.h) :
    edgeVtx R (encE R g a) = (g, a) := by
  have hd : (R.h * g.val + a.val) / R.h = g.val := by
    rw [Nat.mul_add_div R.hh, Nat.div_eq_of_lt a.isLt]
    omega
  have hm : (R.h * g.val + a.val) % R.h = a.val := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt a.isLt]
  exact vtx_eq R _ _ (Fin.ext hd) (by exact hm)

/-- The uniform scheduler of the ring: `n = m * h` edges. -/
def bstep (R : RFrame) (cfg : Vtx R → Agent) (k : Fin R.n) : Vtx R → Agent :=
  ringStep R cfg (edgeVtx R k)

/-! ## The freeze guard never blocks a useful edge -/

theorem isRaceRoot_slotAgent (R : RFrame) (p : Phase) (r : Nat) :
    isRaceRoot (slotAgent R p r) = false := by
  cases p with
  | prelaunch => rfl
  | delivered => rfl
  | declAt j =>
      by_cases h : r = j
      · rw [slotAgent_declAt_tok R j r h]; rfl
      · rw [slotAgent_declAt_off R j r h]; rfl
  | replyAt j =>
      by_cases h : r = j
      · rw [slotAgent_replyAt_tok R j r h]; rfl
      · rw [slotAgent_replyAt_off R j r h]; rfl

theorem isRaceRoot_cfgOf (R : RFrame) (P : PV R) (v : Vtx R) :
    isRaceRoot (cfgOf R P v)
      = (if v.2.val = 0 then joined R P v.1 else false) := by
  by_cases hz : v.2.val = 0
  · rw [cfgOf_root R P v hz, isRaceRoot_rootAgent, if_pos hz]
  · rw [cfgOf_slot R P v hz, isRaceRoot_slotAgent, if_neg hz]

theorem not_frozen_edge (R : RFrame) (P : PV R) (g : Fin R.m) (a : Fin R.h)
    (h1 : a.val = 0 → joined R P g = false)
    (h2 : a.val + 1 = R.h → joined R P (next R g) = false) :
    ¬ (frozen R (cfgOf R P) (g, a) = true) := by
  intro hc
  rw [frozen, Bool.or_eq_true] at hc
  rcases hc with hc | hc
  · rw [isRaceRoot_cfgOf] at hc
    by_cases hz : a.val = 0
    · rw [if_pos hz, h1 hz] at hc; exact absurd hc (by simp)
    · rw [if_neg hz] at hc; exact absurd hc (by simp)
  · by_cases hlt : a.val + 1 < R.h
    · rw [rn_of_lt R (g, a) hlt, isRaceRoot_cfgOf, if_neg (by simp)] at hc
      exact absurd hc (by simp)
    · have hle : a.val + 1 = R.h := by have := a.isLt; omega
      rw [rn_of_last R (g, a) hlt, isRaceRoot_cfgOf, if_pos rfl,
        h2 hle] at hc
      exact absurd hc (by simp)


private theorem exists_pos_of_ofFn_sum_pos : ∀ {N : Nat} (f : Fin N → Nat),
    0 < (List.ofFn f).sum → ∃ i, 0 < f i := by
  intro N
  induction N with
  | zero => intro f h; simp at h
  | succ N ih =>
      intro f h
      rw [List.ofFn_succ, List.sum_cons] at h
      by_cases h0 : 0 < f 0
      · exact ⟨0, h0⟩
      · have hrest : 0 < (List.ofFn (fun k : Fin N => f k.succ)).sum := by omega
        obtain ⟨i, hi⟩ := ih _ hrest
        exact ⟨i.succ, hi⟩
/-- The unique next useful edge of an indebted gap: its guard holds on the
uniform lane (in particular the compare guard `ccw = free`), it is never
frozen, and it lowers the gap's debt by exactly one. -/
theorem exists_useful_ring (R : RFrame) (P : PV R)
    (hP : ∀ g, PhaseOk (F0 R) (P g)) (g : Fin R.m)
    (hpos : 0 < phaseDebt (F0 R) (P g)) :
    ∃ a : Fin R.h, ¬ (frozen R (cfgOf R P) (g, a) = true) ∧
      phaseDebt (F0 R) (nextPhase (F0 R) (P g) a) + 1
        = phaseDebt (F0 R) (P g) := by
  have hhpos := R.hh
  have hpo := hP g
  cases hp : P g with
  | prelaunch =>
      refine ⟨⟨0, hhpos⟩, ?_, ?_⟩
      · refine not_frozen_edge R P g ⟨0, hhpos⟩ (fun _ => ?_) (fun _ => ?_)
        · rw [joined, hp]; simp [IsDelivered]
        · rw [joined, prev_next, hp]; simp [Compared]
      · by_cases h1 : R.h = 1
        · have hnn : nextPhase (F0 R) Phase.prelaunch (⟨0, hhpos⟩ : Fin R.h)
              = Phase.delivered := by simp [nextPhase, h1]
          rw [hnn]
          simp only [phaseDebt, h1]
        · have hnn : nextPhase (F0 R) Phase.prelaunch (⟨0, hhpos⟩ : Fin R.h)
              = Phase.declAt 1 := by simp [nextPhase, h1]
          rw [hnn]
          simp only [phaseDebt]
          omega
  | delivered =>
      exfalso
      rw [hp] at hpos
      simp only [phaseDebt] at hpos
      exact Nat.lt_irrefl 0 hpos
  | declAt j =>
      rw [hp] at hpo
      simp only [PhaseOk] at hpo
      refine ⟨⟨j, hpo.2⟩, ?_, ?_⟩
      · refine not_frozen_edge R P g ⟨j, hpo.2⟩ (fun hz => ?_) (fun _ => ?_)
        · exact absurd hz (by simp only []; omega)
        · rw [joined, prev_next, hp]; simp [Compared]
      · by_cases h1 : j + 1 = R.h
        · have hnn : nextPhase (F0 R) (Phase.declAt j) (⟨j, hpo.2⟩ : Fin R.h)
              = Phase.replyAt j := by simp [nextPhase, h1]
          rw [hnn]
          simp only [phaseDebt]
          omega
        · have hnn : nextPhase (F0 R) (Phase.declAt j) (⟨j, hpo.2⟩ : Fin R.h)
              = Phase.declAt (j + 1) := by simp [nextPhase, h1]
          rw [hnn]
          simp only [phaseDebt]
          omega
  | replyAt j =>
      rw [hp] at hpo
      simp only [PhaseOk] at hpo
      have hjlt : j - 1 < R.h := by omega
      have hcond : j - 1 + 1 = j := by omega
      refine ⟨⟨j - 1, hjlt⟩, ?_, ?_⟩
      · refine not_frozen_edge R P g ⟨j - 1, hjlt⟩ (fun _ => ?_)
          (fun hlast => ?_)
        · rw [joined, hp]; simp [IsDelivered]
        · exact absurd hlast (by simp only []; omega)
      · by_cases h1 : j = 1
        · have hnn : nextPhase (F0 R) (Phase.replyAt j) (⟨j - 1, hjlt⟩ : Fin R.h)
              = Phase.delivered := by simp [nextPhase, h1]
          rw [hnn]
          simp only [phaseDebt]
          omega
        · have hnn : nextPhase (F0 R) (Phase.replyAt j) (⟨j - 1, hjlt⟩ : Fin R.h)
              = Phase.replyAt (j - 1) := by simp [nextPhase, hcond, h1]
          rw [hnn]
          simp only [phaseDebt]
          omega

/-! ## The three Bellman facts for the ring -/

/-- (i) No physical edge increases the service debt. -/
theorem D_step_le (R : RFrame) (cfg : Vtx R → Agent) (hcl : RingClean R cfg)
    (e : Vtx R) : D R (ringStep R cfg e) ≤ D R cfg := by
  obtain ⟨P, hP, rfl⟩ := hcl
  rw [ringStep_cfgOf R P hP e, D_cfgOf R _ (nextP_phaseOk R P hP e),
    D_cfgOf R P hP]
  refine ofFn_sum_le _ _ ?_
  intro g
  by_cases hfr : frozen R (cfgOf R P) e = true
  · rw [nextP_of_frozen R P e hfr]
    exact Nat.le_refl _
  · by_cases hg : g = e.1
    · rw [hg, nextP_self R P e hfr]
      exact phaseDebt_nextPhase_le (F0 R) (P e.1) (hP e.1) e.2
    · rw [nextP_other R P e hfr g hg]
      exact Nat.le_refl _

/-- (ii) From any indebted clean state the unique useful edge of an indebted
gap lowers the service debt by exactly one. -/
theorem D_useful_lt (R : RFrame) (P : PV R) (hP : ∀ g, PhaseOk (F0 R) (P g))
    (hpos : 0 < D R (cfgOf R P)) :
    ∃ (g : Fin R.m) (a : Fin R.h),
      D R (ringStep R (cfgOf R P) (g, a)) + 1 = D R (cfgOf R P) := by
  have hex : ∃ g, 0 < phaseDebt (F0 R) (P g) := by
    rw [D_cfgOf R P hP] at hpos
    exact exists_pos_of_ofFn_sum_pos _ hpos
  obtain ⟨g, hg⟩ := hex
  obtain ⟨a, hfr, hdec⟩ := exists_useful_ring R P hP g hg
  refine ⟨g, a, ?_⟩
  rw [ringStep_cfgOf R P hP (g, a),
    D_cfgOf R _ (nextP_phaseOk R P hP (g, a)), D_cfgOf R P hP]
  refine ofFn_sum_pred _ _ g (fun k hk => ?_) ?_
  · exact congrArg _ (nextP_other R P (g, a) hfr k hk)
  · rw [nextP_self R P (g, a) hfr]
    exact hdec

/-- The exact child-sum inequality of Section 3.3 for the ring. -/
theorem D_childSum (R : RFrame) (P : PV R) (hP : ∀ g, PhaseOk (F0 R) (P g))
    (hpos : 0 < D R (cfgOf R P)) :
    1 + (List.ofFn (fun k : Fin R.n => D R (bstep R (cfgOf R P) k))).sum
      ≤ R.n * D R (cfgOf R P) := by
  obtain ⟨g, a, ha⟩ := D_useful_lt R P hP hpos
  have hchosen : D R (bstep R (cfgOf R P) (encE R g a))
      = D R (ringStep R (cfgOf R P) (g, a)) := by
    rw [bstep, edgeVtx_encE]
  have hlt := ofFn_sum_lt_of_single_lt
    (fun k : Fin R.n => D R (bstep R (cfgOf R P) k))
    (fun _ : Fin R.n => D R (cfgOf R P)) (encE R g a)
    (fun k => D_step_le R _ ⟨P, hP, rfl⟩ (edgeVtx R k))
    (by rw [hchosen]; omega)
  rw [ofFn_sum_const] at hlt
  omega

/-! ## `UniformStart(b)` and the start debt -/

/-- Every gap pre-launch. -/
def startPV (R : RFrame) : PV R := fun _ => Phase.prelaunch

theorem startPV_phaseOk (R : RFrame) : ∀ g, PhaseOk (F0 R) (startPV R g) :=
  fun _ => trivial

/-- `UniformStart(b)`: every root is `root b toSend free`, every interior slot
is empty. -/
def uniformStart (R : RFrame) : Vtx R → Agent := cfgOf R (startPV R)

theorem uniformStart_root (R : RFrame) (v : Vtx R) (hz : v.2.val = 0) :
    uniformStart R v = Agent.root R.b CwPort.toSend CcwPort.free := by
  rw [uniformStart, cfgOf_root R _ v hz, rootAgent, if_neg (by simp [joined,
    startPV, IsDelivered])]
  rfl

theorem uniformStart_interior (R : RFrame) (v : Vtx R) (hz : v.2.val ≠ 0) :
    uniformStart R v = Agent.interior Slot.empty := by
  rw [uniformStart, cfgOf_slot R _ v hz]
  rfl

theorem uniformStart_clean (R : RFrame) : RingClean R (uniformStart R) :=
  ⟨startPV R, startPV_phaseOk R, rfl⟩

/-- `D_start = Σ_g (2 h - 1) = 2n - m`. -/
theorem D_start (R : RFrame) : D R (uniformStart R) = 2 * R.n - R.m := by
  have hsum : D R (uniformStart R) = R.m * (2 * R.h - 1) := by
    rw [uniformStart, D_cfgOf R _ (startPV_phaseOk R)]
    exact ofFn_sum_const R.m _
  have h2 : 2 * R.h - 1 + 1 = 2 * R.h := by have := R.hh; omega
  have key : R.m * (2 * R.h - 1) + R.m = 2 * (R.m * R.h) := by
    calc R.m * (2 * R.h - 1) + R.m
        = R.m * (2 * R.h - 1) + R.m * 1 := by rw [Nat.mul_one]
      _ = R.m * (2 * R.h - 1 + 1) := (Nat.mul_add _ _ _).symm
      _ = R.m * (2 * R.h) := by rw [h2]
      _ = 2 * (R.m * R.h) := Nat.mul_left_comm _ _ _
  have hn : R.n = R.m * R.h := rfl
  omega

/-! ## Claim T -/

private theorem ofFn_sum_eq_zero_elim : ∀ {N : Nat} (f : Fin N → Nat),
    (List.ofFn f).sum = 0 → ∀ i, f i = 0 := by
  intro N
  induction N with
  | zero => intro f _ i; exact Fin.elim0 i
  | succ N ih =>
      intro f h i
      rw [List.ofFn_succ, List.sum_cons] at h
      by_cases h0 : i.val = 0
      · have hi : i = 0 := Fin.ext (by simp [h0])
        rw [hi]; omega
      · have hprev : i.val - 1 < N := by have := i.isLt; omega
        have hsucc : (⟨i.val - 1, hprev⟩ : Fin N).succ = i :=
          Fin.ext (by simp only [Fin.val_succ]; omega)
        have hrest := ih (fun k : Fin N => f k.succ) (by omega)
          ⟨i.val - 1, hprev⟩
        rw [hsucc] at hrest
        exact hrest

private theorem phase_of_debt_zero (R : RFrame) (p : Phase)
    (hp : PhaseOk (F0 R) p) (h0 : phaseDebt (F0 R) p = 0) :
    p = Phase.delivered := by
  have hh := R.hh
  cases p with
  | prelaunch => simp only [phaseDebt] at h0; omega
  | declAt j =>
      simp only [PhaseOk] at hp
      simp only [phaseDebt] at h0
      omega
  | replyAt j =>
      simp only [PhaseOk] at hp
      simp only [phaseDebt] at h0
      omega
  | delivered => rfl

/-- Claim T of Section 3.2: on the ring-clean lane the service debt vanishes
exactly when every root has performed its JOIN, i.e. is `root race toSend
free`. -/
theorem claimT (R : RFrame) (P : PV R) (hP : ∀ g, PhaseOk (F0 R) (P g)) :
    D R (cfgOf R P) = 0
      ↔ ∀ g : Fin R.m, cfgOf R P (g, ⟨0, R.hh⟩)
          = Agent.root Choice.race CwPort.toSend CcwPort.free := by
  constructor
  · intro h0 g
    have hall : ∀ g', P g' = Phase.delivered := by
      intro g'
      refine phase_of_debt_zero R (P g') (hP g') ?_
      rw [D_cfgOf R P hP] at h0
      exact ofFn_sum_eq_zero_elim _ h0 g'
    have hj : joined R P g = true := by
      rw [joined, hall g, hall (prev R g)]
      rfl
    rw [cfgOf_root R P (g, ⟨0, R.hh⟩) rfl, rootAgent, if_pos hj]
  · intro hall
    have hdel : ∀ g, IsDelivered (P g) = true := by
      intro g
      have hg := hall g
      rw [cfgOf_root R P (g, ⟨0, R.hh⟩) rfl] at hg
      by_cases hj : joined R P g = true
      · rw [joined, Bool.and_eq_true] at hj
        exact hj.1
      · rw [rootAgent, if_neg hj] at hg
        exact absurd (Agent.root.inj hg).1 (b_ne_race R)
    rw [D_cfgOf R P hP]
    refine ofFn_sum_eq_zero _ (fun g => ?_)
    have hd := hdel g
    have hpg : P g = Phase.delivered := by
      cases hx : P g with
      | delivered => rfl
      | prelaunch => rw [hx] at hd; exact absurd hd (by simp [IsDelivered])
      | declAt j => rw [hx] at hd; exact absurd hd (by simp [IsDelivered])
      | replyAt j => rw [hx] at hd; exact absurd hd (by simp [IsDelivered])
    rw [hpg]
    rfl

/-! ## Adjacent gaps of length one: the atomic `P1` firing -/

/-- On a ring of one-edge gaps, one firing of the single edge of a pre-launch
gap writes the owner's clockwise receipt AND the shared root's
counterclockwise receipt.  (The frame lemma `ringStep_frame` says nothing else
changes.) -/
theorem p1_writes_both (R : RFrame) (hh1 : R.h = 1) (P : PV R)
    (hP : ∀ g, PhaseOk (F0 R) (P g)) (g : Fin R.m)
    (hg : P g = Phase.prelaunch)
    (hleft : Compared (P (prev R g)) = false)
    (hright : IsDelivered (P (next R g)) = false) :
    ringStep R (cfgOf R P) (g, ⟨0, R.hh⟩) (g, ⟨0, R.hh⟩)
        = Agent.root R.b CwPort.heldDenial CcwPort.free
      ∧ ringStep R (cfgOf R P) (g, ⟨0, R.hh⟩) (next R g, ⟨0, R.hh⟩)
        = Agent.root R.b (cwOf (P (next R g))) CcwPort.heldDenial := by
  have hfr : ¬ (frozen R (cfgOf R P) (g, ⟨0, R.hh⟩) = true) :=
    not_frozen_edge R P g ⟨0, R.hh⟩
      (fun _ => by rw [joined, hg]; simp [IsDelivered])
      (fun _ => by rw [joined, prev_next, hg]; simp [Compared])
  have hnp : nextP R P (g, ⟨0, R.hh⟩) g = Phase.delivered := by
    rw [nextP_self R P (g, ⟨0, R.hh⟩) hfr]
    simp [nextPhase, hg, hh1]
  have hpv : nextP R P (g, ⟨0, R.hh⟩) (prev R g) = P (prev R g) :=
    nextP_other R P (g, ⟨0, R.hh⟩) hfr _ (prev_ne_self R g)
  have hnv : nextP R P (g, ⟨0, R.hh⟩) (next R g) = P (next R g) :=
    nextP_other R P (g, ⟨0, R.hh⟩) hfr _ (next_ne_self R g)
  rw [ringStep_cfgOf R P hP (g, ⟨0, R.hh⟩)]
  constructor
  · rw [cfgOf_root R _ (g, ⟨0, R.hh⟩) rfl, rootAgent, joined, hnp, hpv, hleft]
    simp only [Bool.and_false, if_neg (by simp : ¬ (false = true)),
      cwOf_delivered, ccwOf_of_not_compared _ hleft]
  · rw [cfgOf_root R _ (next R g, ⟨0, R.hh⟩) rfl, rootAgent, joined, prev_next,
      hnp, hnv, hright]
    simp only [Bool.false_and, if_neg (by simp : ¬ (false = true)),
      ccwOf_delivered]

/-- If that same firing completes the shared root's two denials, its JOIN
fires in the SAME step: the shared root ends the step already rearmed. -/
theorem p1_join_same_step (R : RFrame) (hh1 : R.h = 1) (P : PV R)
    (hP : ∀ g, PhaseOk (F0 R) (P g)) (g : Fin R.m)
    (hg : P g = Phase.prelaunch)
    (hright : P (next R g) = Phase.delivered) :
    ringStep R (cfgOf R P) (g, ⟨0, R.hh⟩) (next R g, ⟨0, R.hh⟩)
      = Agent.root Choice.race CwPort.toSend CcwPort.free := by
  have hfr : ¬ (frozen R (cfgOf R P) (g, ⟨0, R.hh⟩) = true) :=
    not_frozen_edge R P g ⟨0, R.hh⟩
      (fun _ => by rw [joined, hg]; simp [IsDelivered])
      (fun _ => by rw [joined, prev_next, hg]; simp [Compared])
  have hnp : nextP R P (g, ⟨0, R.hh⟩) g = Phase.delivered := by
    rw [nextP_self R P (g, ⟨0, R.hh⟩) hfr]
    simp [nextPhase, hg, hh1]
  have hnv : nextP R P (g, ⟨0, R.hh⟩) (next R g) = P (next R g) :=
    nextP_other R P (g, ⟨0, R.hh⟩) hfr _ (next_ne_self R g)
  rw [ringStep_cfgOf R P hP (g, ⟨0, R.hh⟩),
    cfgOf_root R _ (next R g, ⟨0, R.hh⟩) rfl, rootAgent, joined, prev_next,
    hnp, hnv, hright, if_pos (by rfl : (IsDelivered Phase.delivered
      && Compared Phase.delivered) = true)]

/-! ## The ring Bellman supersolution -/

/-- The subtype of ring-clean configurations. -/
def RingCleanConfig (R : RFrame) : Type :=
  {cfg : Vtx R → Agent // RingClean R cfg}

/-- The active (non-discharged) part of that subtype. -/
def ActiveRingConfig (R : RFrame) : Type :=
  {s : RingCleanConfig R // 0 < D R s.1}

/-- The `m`-gap service as an absorbing stopped process: it stops in
`.success` exactly when the service debt reaches `0`, and never exposes
`.failure`. -/
def ringNode (R : RFrame) :
    ActiveRingConfig R → Fin R.n → StopNode (ActiveRingConfig R) :=
  fun s k =>
    if hp : 0 < D R (bstep R s.1.1 k) then
      .active ⟨⟨bstep R s.1.1 k,
        ringClean_step R s.1.1 s.1.2 (edgeVtx R k)⟩, hp⟩
    else .success

/-- The potential `n * D`. -/
def ringPotential (R : RFrame) : StopNode (ActiveRingConfig R) → Nat
  | .active s => R.n * D R s.1.1
  | .success => 0
  | .failure => 0

theorem ringNode_ne_failure (R : RFrame) :
    ∀ s k, ringNode R s k ≠ .failure := by
  intro s k
  simp only [ringNode]
  split <;> simp

theorem D_childSum' (R : RFrame) (cfg : Vtx R → Agent)
    (hcl : RingClean R cfg) (hpos : 0 < D R cfg) :
    1 + (List.ofFn (fun k : Fin R.n => D R (bstep R cfg k))).sum
      ≤ R.n * D R cfg := by
  obtain ⟨P, hP, rfl⟩ := hcl
  exact D_childSum R P hP hpos

private theorem ringPotential_ringNode (R : RFrame) (s : ActiveRingConfig R)
    (k : Fin R.n) :
    ringPotential R (ringNode R s k) = R.n * D R (bstep R s.1.1 k) := by
  simp only [ringNode]
  split
  · rfl
  · rename_i hne
    have hz : D R (bstep R s.1.1 k) = 0 := by omega
    simp [ringPotential, hz]

/-- The `m`-gap shared-root product of the literal rows is a
`NatBellmanSuperSolution` with scale `1` for the potential `n * D`. -/
theorem ring_natBellmanSuperSolution (R : RFrame) :
    NatBellmanSuperSolution (ringNode R) 1 (ringPotential R) := by
  refine ⟨rfl, rfl, ?_⟩
  intro s
  have hdebt := D_childSum' R s.1.1 s.1.2 s.2
  have hscaled := Nat.mul_le_mul_left R.n hdebt
  have hchildren :
      (List.ofFn (fun k : Fin R.n => ringPotential R (ringNode R s k))).sum
        = R.n * (List.ofFn (fun k : Fin R.n => D R (bstep R s.1.1 k))).sum := by
    rw [← ofFn_sum_mul_left]
    exact ofFn_sum_eq _ _ (fun k => ringPotential_ringNode R s k)
  calc
    1 * R.n
        + (List.ofFn (fun k : Fin R.n => ringPotential R (ringNode R s k))).sum
        = R.n * (1 + (List.ofFn
            (fun k : Fin R.n => D R (bstep R s.1.1 k))).sum) := by
          rw [hchildren, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    _ ≤ R.n * (R.n * D R s.1.1) := hscaled
    _ = R.n * ringPotential R (.active s) := rfl

/-- The `UniformStart(b)` state as an active node. -/
def startState (R : RFrame) : ActiveRingConfig R :=
  ⟨⟨uniformStart R, uniformStart_clean R⟩, by
    have hmn : R.m * 1 ≤ R.m * R.h := Nat.mul_le_mul_left _ R.hh
    have hn : R.n = R.m * R.h := rfl
    have hm := R.hm
    rw [D_start]
    omega⟩

/-- The start potential is `n * (2n - m)`. -/
theorem ringPotential_startState (R : RFrame) :
    ringPotential R (.active (startState R)) = R.n * (2 * R.n - R.m) := by
  show R.n * D R (uniformStart R) = _
  rw [D_start]

/-- Adjacent gaps of length one, both pre-launch: ONE firing of the single
edge between the two adjacent roots writes the left root's clockwise receipt
and the right root's counterclockwise receipt. -/
theorem p1_adjacent_prelaunch (R : RFrame) (hh1 : R.h = 1) (P : PV R)
    (hP : ∀ g, PhaseOk (F0 R) (P g)) (g : Fin R.m)
    (hg : P g = Phase.prelaunch) (hnx : P (next R g) = Phase.prelaunch)
    (hleft : Compared (P (prev R g)) = false) :
    ringStep R (cfgOf R P) (g, ⟨0, R.hh⟩) (g, ⟨0, R.hh⟩)
        = Agent.root R.b CwPort.heldDenial CcwPort.free
      ∧ ringStep R (cfgOf R P) (g, ⟨0, R.hh⟩) (next R g, ⟨0, R.hh⟩)
        = Agent.root R.b CwPort.toSend CcwPort.heldDenial := by
  have h := p1_writes_both R hh1 P hP g hg hleft (by rw [hnx]; rfl)
  rw [hnx, cwOf_prelaunch] at h
  exact h

/-- The left counterpart of `p1_join_same_step`: if the same firing completes
the OWNER's two denials (its counterclockwise port already held one), the
owner's JOIN fires in the same step. -/
theorem p1_join_same_step_left (R : RFrame) (hh1 : R.h = 1) (P : PV R)
    (hP : ∀ g, PhaseOk (F0 R) (P g)) (g : Fin R.m)
    (hg : P g = Phase.prelaunch)
    (hleft : Compared (P (prev R g)) = true) :
    ringStep R (cfgOf R P) (g, ⟨0, R.hh⟩) (g, ⟨0, R.hh⟩)
      = Agent.root Choice.race CwPort.toSend CcwPort.free := by
  have hfr : ¬ (frozen R (cfgOf R P) (g, ⟨0, R.hh⟩) = true) :=
    not_frozen_edge R P g ⟨0, R.hh⟩
      (fun _ => by rw [joined, hg]; simp [IsDelivered])
      (fun _ => by rw [joined, prev_next, hg]; simp [Compared])
  have hnp : nextP R P (g, ⟨0, R.hh⟩) g = Phase.delivered := by
    rw [nextP_self R P (g, ⟨0, R.hh⟩) hfr]
    simp [nextPhase, hg, hh1]
  have hpv : nextP R P (g, ⟨0, R.hh⟩) (prev R g) = P (prev R g) :=
    nextP_other R P (g, ⟨0, R.hh⟩) hfr _ (prev_ne_self R g)
  rw [ringStep_cfgOf R P hP (g, ⟨0, R.hh⟩),
    cfgOf_root R _ (g, ⟨0, R.hh⟩) rfl, rootAgent, joined, hnp, hpv, hleft,
    if_pos (by rfl : (IsDelivered Phase.delivered && true) = true)]

/-! ## What the freeze excludes, exactly

The raw row table is total, so the round-`k+1` rows DO fire on a joined
(`race`) root: `L2` relaunches a fresh declaration out of `root race toSend
free`, and `K4` (the responder half of `K2`) resolves its `race` to `in0`.
Both are proved below.  Neither is modelled here, so `ringStep` freezes any
edge with a `race` endpoint; `frozen_iff` shows that this is exactly the set of
excluded firings, and `exists_useful_ring` shows the freeze never blocks the
useful edge of an indebted gap, so nothing this file proves about progress
depends on the exclusion. -/

/-- `L2` would fire on a joined root: the raw table launches a round-`k+1`
declaration out of `root race toSend free`. -/
theorem row_L2_on_joined_root :
    row (Agent.root Choice.race CwPort.toSend CcwPort.free)
        (Agent.interior Slot.empty)
      = (Agent.root Choice.out1 CwPort.waiting CcwPort.free,
         Agent.interior (Slot.decl Choice.out1)) := by
  simp [row, resolveInit]

/-- `K4` (the responder half of `K2`) would fire on a joined root: the raw
table resolves its `race` back to a frozen base. -/
theorem row_K4_on_joined_root (cw : CwPort) (ccw : CcwPort) :
    row (Agent.interior Slot.empty) (Agent.root Choice.race cw ccw)
      = (Agent.interior Slot.empty, Agent.root Choice.in0 cw ccw) := by
  simp [row, resolveResp]

/-- An edge is frozen exactly when one of its two endpoints is a root that has
already JOINed. -/
theorem frozen_iff (R : RFrame) (P : PV R) (g : Fin R.m) (a : Fin R.h) :
    frozen R (cfgOf R P) (g, a) = true
      ↔ ((a.val = 0 ∧ joined R P g = true)
          ∨ (a.val + 1 = R.h ∧ joined R P (next R g) = true)) := by
  constructor
  · intro hc
    rw [frozen, Bool.or_eq_true] at hc
    rcases hc with hc | hc
    · rw [isRaceRoot_cfgOf] at hc
      by_cases hz : a.val = 0
      · rw [if_pos hz] at hc
        exact Or.inl ⟨hz, hc⟩
      · rw [if_neg hz] at hc
        exact absurd hc (by simp)
    · by_cases hlt : a.val + 1 < R.h
      · rw [rn_of_lt R (g, a) hlt, isRaceRoot_cfgOf, if_neg (by simp)] at hc
        exact absurd hc (by simp)
      · have hle : a.val + 1 = R.h := by have := a.isLt; omega
        rw [rn_of_last R (g, a) hlt, isRaceRoot_cfgOf, if_pos rfl] at hc
        exact Or.inr ⟨hle, hc⟩
  · intro h
    rw [frozen, Bool.or_eq_true]
    rcases h with ⟨hz, hj⟩ | ⟨hle, hj⟩
    · refine Or.inl ?_
      rw [isRaceRoot_cfgOf, if_pos hz]
      exact hj
    · refine Or.inr ?_
      rw [rn_of_last R (g, a) (by show ¬ (a.val + 1 < R.h); omega),
        isRaceRoot_cfgOf, if_pos rfl]
      exact hj

#print axioms ringClean_step
#print axioms ring_natBellmanSuperSolution
#print axioms claimT
#print axioms ringStep_cfgOf
#print axioms D_start
end ShortGapLiteralRingRows

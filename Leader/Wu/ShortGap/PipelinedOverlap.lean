import Leader.Wu.ShortGap.PipelinedRearm

/-!
# Genuinely overlapped pipelining: round `k+1` plays during service `k`

`Leader/Wu/ShortGap/PipelinedRearm.lean` composed a pipelining-aware ghost round
with a denial service that was a pure token walk: during `SERVICE(k)` the
round-`(k+1)` word was not tracked at all, and the exit word was supplied by an
abstract `RoundEntryMap`.  This file removes that idealisation.  The service
state here carries the round-`(k+1)` ghost word and *plays it*:

```
OverlapServiceState := { tokens : Fin m → GapDenialState h,
                         word   : Configuration m,  -- the round-(k+1) word
                         … invariants … }
```

and one scheduler interaction advances the round-`k` carriers by
`multiLocalStep L` **and** resolves the round-`(k+1)` word by
`joinedIncidenceStep P (rearmedOf ring tokens) word e`, under the mask read off
the **pre-step** carriers — the same convention as the round step of the
imported file.  So a root that has already collected both round-`k` denials is
resolving round `k+1` while its neighbours are still draining round-`k`
traffic.  This is the literal pipeline of `TWO_DENIAL_LITERAL_CARRIER.md`
§4(c) ("the system is a pipeline with skew ≤ 1, not a sequence of global
rounds") on the token quotient.

**Three outcomes, and the sidecar.**  A candidate discovered by the overlapped
play is a terminal success of the whole composed process *before* the service
finishes: the `ServiceOutcome.succeed` port, charged `0`, which the imported
file declared but never used.  Otherwise the service continues (`.cont`) or,
once every carrier is discharged, exits (`.exit`) into the round state built
from the **partially played** word.

**The P4 point, proved.**  The P4 remark is that "the last joining root is
still Race at the cut".  Here that is a theorem, and the proof is exactly the
pre-step mask:

* `overlapStepWord_eq_race_of_hops_pos` — if gap `g` is still in transit then
  its left root `g` is missing its clockwise receipt, hence is unjoined, hence
  the mask (read before the interaction) leaves it alone, so the post-step word
  still has `Race` at `g`;
* `overlapStepWord_hasRace` — every active overlapped state therefore steps to
  a word that still has an unresolved root.  In particular the interaction that
  discharges the *last* carrier cannot also resolve the root that this very
  discharge joins: the mask that interaction used was read *before* the
  discharge, when that root was still unjoined.  The corner case "the
  discharging edge resolves the last Race root in the same step" is impossible,
  not merely unhandled.

The structure invariant `unjoinedRace` ("an unjoined root is still `Race` in
the round-`(k+1)` word") is what makes this an induction rather than a one-step
remark; it is preserved by every interaction because receipts are monotone
(`rearmedOf_multiLocalStep`) and unjoined roots are frozen by the restricted
step, and it holds at service entry because the entry word is all-`Race`.

**Budgets.**  The service potential is `n * totalHops tokens` — the played word
does *not* enter it, which is the whole point: round-`(k+1)` progress is free
insurance, not a debt.  `hexit` needs only `choiceRaceReserve word' ≤ m`
(`choiceRaceReserve_le`) because the exit carriers are discharged, giving
`A = n * m`; `hentry` at all-declare carriers with an all-`Race` word gives
`R = n * (m * (2 * h))`.  Composed through
`partialExitEntry_natBellmanSuperSolution` with the round step of the imported
file, the budget from the all-`Race` sequential entry round is again exactly
`2 * (n * m) * (1 + h)`: overlapping costs nothing.

**Quotients still in force (unchanged).**

* The carriers are the abstract one-token-per-gap stop-and-wait walk, not the
  literal rows of `Leader/Wu/ShortGap/LiteralGapRows.lean`: no forgery, no
  staleness, no authentication, no shared-root field bookkeeping beyond
  disjointness of the layout's edge sets, comparison outcome fixed to a denial,
  one uniform gap length `h`, per-gap debt `2 * h` rather than `2 * h - 1`.
* `word` is a ghost object.  This file does **not** prove that a literal
  pipelined execution projects onto it (obligation **P1**) nor that a
  round-`k` candidate cannot be discarded by a later rearm (**P2**).  Those
  refinement obligations remain open; what is now closed on the quotient is the
  overlap itself — the accounting no longer pretends the next round is idle
  while the previous service drains.
* Nothing here claims stabilization or a final leader-election bound.
-/

namespace ShortGapPipelinedOverlap

open FiniteUniformStoppingTree
open PeriodHIncidenceChoice
open ShortGapChoiceStopping
open ShortGapDenialTransport
open ShortGapTwoDenialJoin
open ShortGapJoinedIncidenceBalance
open ShortGapPipelinedRearm
open BalancedFailureRestart
open BalancedFailureRestartPartialExit
open BalancedFailureRestartPartialExitEntry

set_option autoImplicit false

/-! ## The overlapped service state -/

/-- State of the round-`k` denial service while round `k+1` is already being
played on it.

* `tokens` — the round-`k` carriers, one per gap;
* `word` — the round-`(k+1)` ghost word, all-`Race` at service entry;
* `hasActive` — the service is still running: some carrier owes hops;
* `unjoinedRace` — a root that has not yet collected both round-`k` denials is
  still unresolved in round `k+1`.  This is the invariant that makes the
  "still `Race` at the cut" argument an induction;
* `noCandidate` — no candidate has appeared yet (one would have stopped the
  whole composed process through the sidecar port). -/
structure OverlapServiceState {m : Nat} (ring : DirectedRing m) (h : Nat) where
  tokens : Fin m → GapDenialState h
  word : Configuration m
  hasActive : ∃ g, 0 < (tokens g).hops
  unjoinedRace : ∀ i, rearmedOf ring tokens i = false → word i = .race
  noCandidate : ∀ i, ¬ Candidate10 ring word i

/-- The round-`(k+1)` word after one physical interaction of the overlapped
service: the joined-restricted incidence step under the mask read off the
**pre-step** carriers. -/
def overlapStepWord {n h m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (state : OverlapServiceState ring h) (edge : Fin n) : Configuration m :=
  joinedIncidenceStep P (rearmedOf ring state.tokens) state.word edge

/-! ## The pre-step mask keeps a gap's left root unresolved -/

/-- A gap still in transit leaves its left root unjoined. -/
theorem not_rearmed_of_hops_pos {h m : Nat} (ring : DirectedRing m)
    (gap : Fin m → GapDenialState h) (g : Fin m)
    (hg : 0 < (gap g).hops) : rearmedOf ring gap g = false := by
  simp [rearmedOf, rightReceiptOf_eq_false_of_hops_pos gap g hg]

/-- **The P4 lemma, precisely.**  If gap `g` is still in transit at an
overlapped service state, then its left root `g` is missing its clockwise
receipt, hence is unjoined; the mask is read *before* the interaction, so this
root is untouched by that interaction and the post-step round-`(k+1)` word
still shows it as `Race`.

Applied at the interaction that discharges the *last* carrier this says: the
very interaction that joins a root cannot also resolve it, because the mask it
used was read while that root was still unjoined. -/
theorem overlapStepWord_eq_race_of_hops_pos {n h m : Nat}
    (ring : DirectedRing m) (P : Placement n m)
    (state : OverlapServiceState ring h) (edge : Fin n) (g : Fin m)
    (hg : 0 < (state.tokens g).hops) :
    overlapStepWord ring P state edge g = .race := by
  have hnr : rearmedOf ring state.tokens g = false :=
    not_rearmed_of_hops_pos ring state.tokens g hg
  show joinedIncidenceStep P (rearmedOf ring state.tokens) state.word edge g
      = Choice.race
  rw [joinedIncidenceStep_of_unjoined P (rearmedOf ring state.tokens)
    state.word edge g hnr]
  exact state.unjoinedRace g hnr

/-- **No interaction of a running overlapped service can freeze the next
round.**  In particular the exit word of the service always still has an
unresolved root, with no side condition: the corner case in which the
discharging edge also resolves the last `Race` root does not exist. -/
theorem overlapStepWord_hasRace {n h m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (state : OverlapServiceState ring h) (edge : Fin n) :
    HasRace (overlapStepWord ring P state edge) := by
  obtain ⟨g, hg⟩ := state.hasActive
  exact ⟨g, overlapStepWord_eq_race_of_hops_pos ring P state edge g hg⟩

/-- The `unjoinedRace` invariant is preserved by every interaction: receipts
are monotone, so a root unjoined after the step was unjoined before it, and an
unjoined root is frozen by the restricted step. -/
theorem overlap_unjoinedRace_step {n h m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (L : GapLayout n h m)
    (state : OverlapServiceState ring h) (edge : Fin n) :
    ∀ i, rearmedOf ring (multiLocalStep L state.tokens edge) i = false →
      overlapStepWord ring P state edge i = .race := by
  intro i hi
  have hbefore : rearmedOf ring state.tokens i = false := by
    cases hr : rearmedOf ring state.tokens i with
    | false => rfl
    | true =>
        have hafter := rearmedOf_multiLocalStep ring L state.tokens edge i hr
        rw [hafter] at hi
        exact Bool.noConfusion hi
  show joinedIncidenceStep P (rearmedOf ring state.tokens) state.word edge i
      = Choice.race
  rw [joinedIncidenceStep_of_unjoined P (rearmedOf ring state.tokens)
    state.word edge i hbefore]
  exact state.unjoinedRace i hbefore

/-! ## One interaction of the overlapped service -/

/-- One scheduler interaction of the round-`k` denial service with the
round-`(k+1)` word played on top.

* `.succeed` — the overlapped play created a candidate; this is a terminal
  success of the whole composed process, charged `0`, reached *before* the
  service finished;
* `.cont` — some carrier still owes hops;
* `.exit` — every carrier is discharged; the service exits into the round
  state built from the partially played word, which is admissible by
  `overlapStepWord_hasRace` and the failed candidate test. -/
noncomputable def overlapServiceStep {n h m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (L : GapLayout n h m)
    (state : OverlapServiceState ring h) (edge : Fin n) :
    ServiceOutcome (OverlapServiceState ring h)
      (PipelinedRoundState ring h) := by
  classical
  exact
    if hcand : ∃ i, Candidate10 ring (overlapStepWord ring P state edge) i then
      .succeed
    else if hactive :
        ∃ g, 0 < ((multiLocalStep L state.tokens edge) g).hops then
      .cont
        ⟨multiLocalStep L state.tokens edge,
          overlapStepWord ring P state edge, hactive,
          overlap_unjoinedRace_step ring P L state edge,
          fun i hi => hcand ⟨i, hi⟩⟩
    else
      .exit
        ⟨overlapStepWord ring P state edge,
          multiLocalStep L state.tokens edge,
          overlapStepWord_hasRace ring P state edge,
          fun i hi => hcand ⟨i, hi⟩⟩

/-! ## The service Bellman certificate -/

/-- Residual service potential.  The played round-`(k+1)` word
does not appear: its progress is free insurance, not a debt. -/
def overlapServicePotential {n h m : Nat} {ring : DirectedRing m}
    (state : OverlapServiceState ring h) : Nat := n * totalHops state.tokens

private theorem overlapServiceOutcome_le {n h m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (L : GapLayout n h m)
    (state : OverlapServiceState ring h) (edge : Fin n) :
    serviceOutcomePotential (overlapServicePotential (n := n))
        (overlapServiceStep ring P L state edge) ≤
      n * totalHops (multiLocalStep L state.tokens edge) := by
  classical
  simp only [overlapServiceStep]
  split
  · simp [serviceOutcomePotential]
  · split
    · simp [serviceOutcomePotential, overlapServicePotential]
    · simp [serviceOutcomePotential]

/-- **The overlapped service is a scale-one Bellman supersolution** for its
residual-hop potential.  Candidate success and service completion are both
charged `0`; a continuing service pays exactly the advanced carriers, and
`totalHops_childSum` exposes one unit of strict progress among the `n`
children. -/
theorem overlapService_bellman {n h m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (L : GapLayout n h m) :
    ServiceBellman (overlapServiceStep ring P L) 1
      (overlapServicePotential (n := n)) := by
  intro state
  have hdebt := totalHops_childSum L
    (⟨state.tokens, state.hasActive⟩ : MultiGapState h m)
  have hscaled := Nat.mul_le_mul_left n hdebt
  have hchildren :
      (List.ofFn (fun edge : Fin n =>
        serviceOutcomePotential (overlapServicePotential (n := n))
          (overlapServiceStep ring P L state edge))).sum ≤
        n * (List.ofFn (fun edge : Fin n =>
          totalHops (multiLocalStep L state.tokens edge))).sum := by
    calc
      (List.ofFn (fun edge : Fin n =>
          serviceOutcomePotential (overlapServicePotential (n := n))
            (overlapServiceStep ring P L state edge))).sum ≤
          (List.ofFn (fun edge : Fin n =>
            n * totalHops (multiLocalStep L state.tokens edge))).sum :=
        ofFn_sum_le _ _ (fun edge =>
          overlapServiceOutcome_le ring P L state edge)
      _ = n * (List.ofFn (fun edge : Fin n =>
          totalHops (multiLocalStep L state.tokens edge))).sum :=
        ofFn_sum_mul_left n _
  calc
    1 * n + (List.ofFn (fun edge : Fin n =>
        serviceOutcomePotential (overlapServicePotential (n := n))
          (overlapServiceStep ring P L state edge))).sum ≤
        n + n * (List.ofFn (fun edge : Fin n =>
          totalHops (multiLocalStep L state.tokens edge))).sum := by
          simpa using Nat.add_le_add_left hchildren n
    _ = n * (1 + (List.ofFn (fun edge : Fin n =>
          totalHops (multiLocalStep L state.tokens edge))).sum) := by
        rw [Nat.mul_add, Nat.mul_one]
    _ ≤ n * (n * totalHops state.tokens) := hscaled
    _ = n * overlapServicePotential (n := n) state := rfl

/-! ## The exit is admissible -/

private theorem overlap_totalHops_eq_zero {h m : Nat}
    (gap : Fin m → GapDenialState h) (hnone : ¬ ∃ g, 0 < (gap g).hops) :
    totalHops gap = 0 := by
  have h : totalHops gap = (List.ofFn (fun _ : Fin m => (0 : Nat))).sum :=
    ofFn_sum_eq _ _ (fun g => by
      have hg : ¬ 0 < (gap g).hops := fun hpos => hnone ⟨g, hpos⟩
      omega)
  rw [h, ofFn_sum_const, Nat.mul_zero]

/-- **The exit of the overlapped service is an admissible round state.**  It
carries the partially played round-`(k+1)` word and the fully discharged
round-`k` carriers; the word still has an unresolved root (the P4 lemma) and
still has no candidate (a candidate would have taken the sidecar port). -/
theorem overlapService_exit_admissible {n h m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (L : GapLayout n h m)
    (state : OverlapServiceState ring h) (edge : Fin n)
    (r : PipelinedRoundState ring h)
    (hstep : overlapServiceStep ring P L state edge = .exit r) :
    r.word = overlapStepWord ring P state edge ∧
      r.tokens = multiLocalStep L state.tokens edge ∧
      HasRace r.word ∧
      (∀ i, ¬ Candidate10 ring r.word i) ∧
      (∀ g, (r.tokens g).hops = 0) ∧
      totalHops r.tokens = 0 := by
  classical
  simp only [overlapServiceStep] at hstep
  split at hstep
  · simp at hstep
  · split at hstep
    · simp at hstep
    · rename_i hcand hnone
      injection hstep with heq
      subst heq
      have hpoint : ∀ g, ((multiLocalStep L state.tokens edge) g).hops = 0 := by
        intro g
        have hg : ¬ 0 < ((multiLocalStep L state.tokens edge) g).hops :=
          fun hpos => hnone ⟨g, hpos⟩
        omega
      exact ⟨rfl, rfl, overlapStepWord_hasRace ring P state edge,
        fun i hi => hcand ⟨i, hi⟩, hpoint,
        overlap_totalHops_eq_zero _ hnone⟩

/-- At the exit every root has joined round `k+1` (`allDone_iff`), so the
round of `Leader/Wu/ShortGap/PipelinedRearm.lean` continues from the partially
played word as literal sequential bare incidence. -/
theorem overlapService_exit_round_is_sequential {n h m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (L : GapLayout n h m)
    (state : OverlapServiceState ring h) (edge : Fin n)
    (r : PipelinedRoundState ring h)
    (hstep : overlapServiceStep ring P L state edge = .exit r)
    (e : Fin n) : stepWord ring P r e = incidenceStep P r.word e := by
  obtain ⟨_, _, _, _, hall, _⟩ :=
    overlapService_exit_admissible ring P L state edge r hstep
  have hjoined : ∀ i, rearmedOf ring r.tokens i = true :=
    (allDone_iff ring r.tokens).1 hall
  exact joinedIncidenceStep_eq_of_all_joined P (rearmedOf ring r.tokens)
    r.word e (fun i _ => hjoined i)

/-- **`hexit`.**  The exit round state has potential at most `n * m`: its
carriers are discharged, so only the `Race` reserve of the partially played
word contributes, and that is at most `m`. -/
theorem overlapService_exit_le {n h m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (L : GapLayout n h m)
    (state : OverlapServiceState ring h) (edge : Fin n)
    (r : PipelinedRoundState ring h)
    (hstep : overlapServiceStep ring P L state edge = .exit r) :
    pipelinedRoundPotential (n := n) ring (.active r) ≤ n * m := by
  obtain ⟨_, _, _, _, _, hzero⟩ :=
    overlapService_exit_admissible ring P L state edge r hstep
  show n * (choiceRaceReserve r.word + totalHops r.tokens) ≤ n * m
  rw [hzero, Nat.add_zero]
  exact Nat.mul_le_mul_left n (choiceRaceReserve_le r.word)

/-! ## Service entry -/

/-- Service entry after a uniform round failure: every gap restarted at its
launched declaration, the next round's word all-`Race`. -/
def overlapServiceEntry {n h m : Nat} (ring : DirectedRing m)
    (L : GapLayout n h m) (hm : 0 < m) : OverlapServiceState ring h :=
  ⟨fun _ => .declareRight 0 L.hpos, allRaceConfiguration m,
    ⟨⟨0, hm⟩, by
      have := L.hpos
      simp only [GapDenialState.hops]
      omega⟩,
    fun _ _ => rfl,
    allRaceConfiguration_noCandidate ring⟩

/-- **`hentry`.**  The service is entered at potential exactly
`n * (m * (2 * h))`. -/
@[simp] theorem overlapServicePotential_entry {n h m : Nat}
    (ring : DirectedRing m) (L : GapLayout n h m) (hm : 0 < m) :
    overlapServicePotential (n := n) (overlapServiceEntry ring L hm) =
      n * (m * (2 * h)) := by
  simp [overlapServicePotential, overlapServiceEntry]

/-! ## The composed overlapped process -/

/-- The composed overlapped pipelined process: the ghost round of
`Leader/Wu/ShortGap/PipelinedRearm.lean`, whose uniform failure enters the
overlapped service, whose completion exits into the partially played next
round, and which may also stop in success from inside the service. -/
noncomputable def overlapComposedStep {n h m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (L : GapLayout n h m) (hm : 0 < m) :
    RestartState (PipelinedRoundState ring h) (OverlapServiceState ring h) →
      Fin n →
      StopNode (RestartState (PipelinedRoundState ring h)
        (OverlapServiceState ring h)) :=
  partialExitEntryStep (pipelinedRoundStep ring P L)
    (fun _ _ => overlapServiceEntry ring L hm) (overlapServiceStep ring P L)

/-- Composed potential with `A = n * m` and `R = n * (m * (2 * h))`. -/
def overlapComposedPotential {n h m : Nat} (ring : DirectedRing m) :
    StopNode (RestartState (PipelinedRoundState ring h)
      (OverlapServiceState ring h)) → Nat :=
  partialExitPotential (pipelinedRoundPotential (n := n) ring)
    (overlapServicePotential (n := n)) (n * m) (n * (m * (2 * h)))

/-- **The composed overlapped Bellman certificate.** -/
theorem overlapComposed_natBellmanSuperSolution {n h m : Nat}
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m) (hn : 1 < n)
    (L : GapLayout n h m) :
    NatBellmanSuperSolution (overlapComposedStep ring P L (by omega)) 1
      (overlapComposedPotential (n := n) ring) :=
  partialExitEntry_natBellmanSuperSolution (pipelinedRoundStep ring P L)
    (fun _ _ => overlapServiceEntry ring L (by omega))
    (overlapServiceStep ring P L)
    (pipelinedRoundPotential (n := n) ring)
    (overlapServicePotential (n := n))
    (pipelined_natBellmanSuperSolution ring P L)
    (overlapService_bellman ring P L)
    (fun state => pipelined_localBalance ring hm P hn L state)
    (fun state edge r hstep =>
      overlapService_exit_le ring P L state edge r hstep)
    (fun _ _ _ => Nat.le_of_eq
      (overlapServicePotential_entry ring L (by omega)))

/-- The composed overlapped process has no bad terminal. -/
theorem overlapComposedStep_ne_failure {n h m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (L : GapLayout n h m) (hm : 0 < m) :
    ∀ state edge, overlapComposedStep ring P L hm state edge ≠ .failure :=
  partialExitEntryStep_ne_failure (pipelinedRoundStep ring P L)
    (fun _ _ => overlapServiceEntry ring L hm) (overlapServiceStep ring P L)

private theorem budget_eq (n h m : Nat) :
    2 * (n * m) * (1 + h) = 2 * (n * m) + n * (m * (2 * h)) := by
  rw [Nat.mul_add, Nat.mul_one]
  have hswap : n * (m * (2 * h)) = 2 * (n * m) * h := by ac_rfl
  rw [hswap]

/-- **The composed budget.**  From the sequential all-`Race` entry round the
overlapped composed potential is exactly `2 * (n * m) * (1 + h)` — the same
budget as the non-overlapped composition of
`Leader/Wu/ShortGap/PipelinedRearm.lean`.  Playing round `k+1` during service `k`
costs nothing. -/
theorem overlapComposedPotential_entryRoundState {n h m : Nat}
    (ring : DirectedRing m) (hm : 0 < m) :
    overlapComposedPotential (n := n) (h := h) ring
        (.active (.round (entryRoundState ring hm))) =
      2 * (n * m) * (1 + h) := by
  rw [budget_eq]
  simp only [overlapComposedPotential, partialExitPotential,
    pipelinedRoundPotential_entryRoundState ring hm]
  omega

/-- **The composed overlapped complexity bound.** -/
theorem overlapComposed_truncatedCost_le {n h m : Nat}
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m) (hn : 1 < n)
    (L : GapLayout n h m) (T : Nat) :
    truncatedActiveCostNumerator (overlapComposedStep ring P L (by omega))
        (.active (.round (entryRoundState ring (by omega)))) T ≤
      n ^ T * (2 * (n * m) * (1 + h)) := by
  have hsuper := overlapComposed_natBellmanSuperSolution ring hm P hn L
  have hcost := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (overlapComposedStep ring P L (by omega)) 1
    (overlapComposedPotential (n := n) ring) hsuper
    (.active (.round (entryRoundState ring (by omega)))) T
  rw [overlapComposedPotential_entryRoundState ring (by omega)] at hcost
  omega

/-- Reciprocal finite-horizon success tail for the overlapped process.  With
`factor = n`, at least a `1 - 1/n` fraction of scheduler words of length
`n * (2 * n * m * (1 + h))` has already produced a persistent candidate —
counting candidates found by the overlapped play inside a running service,
which reach the same terminal through the sidecar port. -/
theorem overlapComposed_success_one_minus_inv_factor {n h m factor : Nat}
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m) (hn : 1 < n)
    (L : GapLayout n h m) :
    (factor - 1) * n ^ (factor * (2 * (n * m) * (1 + h))) ≤
      factor * successCount (overlapComposedStep ring P L (by omega))
        (.active (.round (entryRoundState ring (by omega))))
        (factor * (2 * (n * m) * (1 + h))) := by
  have hpositive :
      0 < pipelinedRoundPotential (n := n) ring
        (.active (entryRoundState (h := h) ring (by omega))) +
          (n * m + n * (m * (2 * h))) := by
    rw [pipelinedRoundPotential_entryRoundState ring (by omega)]
    have : 0 < n * m := Nat.mul_pos (by omega) (by omega)
    omega
  have htail :=
    pred_mul_pow_le_factor_mul_successCount_partialExitEntry_roundBase
      (pipelinedRoundStep ring P L)
      (fun _ _ => overlapServiceEntry ring L (by omega : 0 < m))
      (overlapServiceStep ring P L)
      (entryRoundState (h := h) ring (by omega))
      (pipelinedRoundPotential (n := n) ring)
      (overlapServicePotential (n := n))
      (pipelined_natBellmanSuperSolution ring P L)
      (overlapService_bellman ring P L)
      (fun state => pipelined_localBalance ring hm P hn L state)
      (fun state edge r hstep =>
        overlapService_exit_le ring P L state edge r hstep)
      (fun _ _ _ => Nat.le_of_eq
        (overlapServicePotential_entry ring L (by omega)))
      hpositive (factor := factor)
  rw [pipelinedRoundPotential_entryRoundState ring (by omega)] at htail
  rw [budget_eq]
  have hshape : n * m + (n * m + n * (m * (2 * h))) =
      2 * (n * m) + n * (m * (2 * h)) := by omega
  rw [hshape] at htail
  exact htail

#print axioms not_rearmed_of_hops_pos
#print axioms overlapStepWord_eq_race_of_hops_pos
#print axioms overlapStepWord_hasRace
#print axioms overlap_unjoinedRace_step
#print axioms overlapService_bellman
#print axioms overlapService_exit_admissible
#print axioms overlapService_exit_round_is_sequential
#print axioms overlapService_exit_le
#print axioms overlapComposed_natBellmanSuperSolution
#print axioms overlapComposedPotential_entryRoundState
#print axioms overlapComposed_truncatedCost_le
#print axioms overlapComposed_success_one_minus_inv_factor

end ShortGapPipelinedOverlap

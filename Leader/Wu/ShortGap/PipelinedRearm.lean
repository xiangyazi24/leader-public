import Leader.Wu.ShortGap.JoinedIncidenceBalance
import Leader.Wu.ShortGap.TwoDenialJoin
import Leader.Core.PartialExitEntryRestart

/-!
# Pipelined ghost round: a derived joined mask on top of the token walk

This file instantiates the abstract *joined-restricted* incidence quotient of
`Leader/Wu/ShortGap/JoinedIncidenceBalance.lean` with a **derived** join predicate
taken from the explicit denial token walk of
`Leader/Wu/ShortGap/DenialTransport.lean` and its receipt projection in
`Leader/Wu/ShortGap/TwoDenialJoin.lean`.  It is stage one of hypothesis H9(a) of
`TWO_DENIAL_LITERAL_CARRIER.md` §4(c)/§5 and of obligations P3/P4.

**The state.**  One ghost round `k` is a pair

* `word : Configuration m` — the round-`k` ghost word `W_k`; `Race` means
  "root not yet resolved in round `k`";
* `tokens : Fin m → GapDenialState h` — the round-`(k-1)` denial service, one
  stop-and-wait carrier per gap, laid out on the scheduler edges by a
  `GapLayout n h m`.

The join predicate is **not an input**: it is the derived receipt conjunction
`joined i = rearmedOf ring tokens i`, i.e. root `i` holds both round-`(k-1)`
denials (its clockwise gap discharged and the gap ending at it in its
compare/deny phase).  One scheduler interaction advances the round-`(k-1)`
tokens by `multiLocalStep` **and** resolves the round-`k` word by
`joinedIncidenceStep` under the mask read off the *pre-step* tokens: a root
that only becomes joined by this very interaction is not resolved by it.

**What is proved.**

* `rearmed_monotone_step` (P4-lite): the derived mask never goes
  `true → false`, so the ghost round only ever gains resolvable roots.
* `pipelined_localBalance`: at every active pipelined state, immediate
  uniform-failure mass is at most immediate candidate mass.  This is
  the §4 case analysis carried out literally: if some edge freezes the
  word, every unresolved root had already joined and
  `joinedGoodEdgeCount_ge_joinedBadEdgeCount` (hence
  `goodEdgeCount_ge_badEdgeCount`) applies verbatim; otherwise the failure
  mass is `0`.
* `pipelined_natBellmanSuperSolution`: the combined potential
  `Φ = n * (choiceRaceReserve word + totalHops tokens)` is a scale-one
  `NatBellmanSuperSolution` for the stopped pipelined step.  The proof case
  splits exactly on the obstruction isolated in the imported file: with a
  *joined* Race root, `joinedReserve_childSum` pays the interaction; with no
  joined Race root, `joinedReserve_childSum_eq_of_no_joined_race` says the
  word contributes nothing and `totalHops_childSum` pays instead — the bridge
  being `exists_hops_pos_of_not_rearmed`, which turns "some unresolved root is
  unjoined" into "some gap still owes hops".
* Start values: an all-Race word over freshly launched declarations has
  `Φ = n * (m + m * (2 * h))`; an all-Race word over discharged tokens has
  `Φ = n * m` and its step is literally the sequential `incidenceStep`
  (`stepWord_of_allDischarged`), recovering the round of
  `ShortGapChoiceStopping`.
* Composition through `partialExitEntry_natBellmanSuperSolution`: a uniform
  round-`k` failure enters the round-`k` denial service at the fresh
  all-declare layout (`resetEntry`), the service is the token walk itself, and
  its completion exits into an *arbitrary admissible* round-`(k+1)` state
  supplied by a `RoundEntryMap` — the "bounded arbitrary return state".
  The exit bound `A = n * m` is `choiceRaceReserve_le`; the entry
  bound is `R = n * (m * (2 * h))`.  The composed budget at the entry round is
  exactly `2 * (n * m) * (1 + h)`.

**Quotients still in force (nothing here weakens them).**

* The tokens are the abstract one-carrier-per-gap walk, not the literal rows
  of `Leader/Wu/ShortGap/LiteralGapRows.lean`: no forgery, no staleness, no
  authentication, no shared-root field bookkeeping beyond the disjointness of
  the `GapLayout` edge sets, and the comparison outcome is fixed to a denial.
* One uniform gap length `h` for all `m` gaps; the debt is the `2 * h`
  out-and-back count, not the literal `2 * h - 1`.
* `word` is a ghost object.  This file does **not** prove that a literal
  pipelined execution projects onto it (obligation P1) nor that a round-`k`
  candidate cannot be discarded by a later rearm (P2).  Those are the
  refinement obligations; the accounting theorem proved here is what they
  would feed.
* The composed process alternates the two *accounting* modes.  Its round
  certificate is proved for an arbitrary token state (arbitrary residual
  service debt), and its service exit is an arbitrary admissible word, which
  is what makes the certificate pipelining-aware; but the composed step
  itself does not model a sidecar candidate discovered during service (the
  `ServiceOutcome.succeed` port is available and charged `0`, and is simply
  not used here).
* Nothing here claims stabilization or a final leader-election bound.
-/

namespace ShortGapPipelinedRearm

open FiniteUniformStoppingTree
open PeriodHIncidenceChoice
open ShortGapChoiceStopping
open ShortGapDenialTransport
open ShortGapTwoDenialJoin
open ShortGapJoinedIncidenceBalance
open BalancedFailureRestart
open BalancedFailureRestartPartialExit
open BalancedFailureRestartPartialExitEntry

set_option autoImplicit false

/-! ## The pipelined ghost-round state -/

/-- One ghost round `k`: the round-`k` word together with the round-`(k-1)`
denial carriers whose completion is what lets a root enter round `k`.  The
round is active: it still has an unresolved root and has not yet produced a
persistent oriented candidate. -/
structure PipelinedRoundState {m : Nat} (ring : DirectedRing m) (h : Nat) where
  word : Configuration m
  tokens : Fin m → GapDenialState h
  hasRace : HasRace word
  noCandidate : ∀ i, ¬ Candidate10 ring word i

/-- The derived join predicate: root `i` has both round-`(k-1)` denials.  This
is read off the carriers, never supplied. -/
def PipelinedRoundState.joined {m h : Nat} {ring : DirectedRing m}
    (state : PipelinedRoundState ring h) : Fin m → Bool :=
  rearmedOf ring state.tokens

/-! ## Unjoined roots certify residual service debt -/

/-- An undischarged gap still owes hops. -/
theorem hops_pos_of_not_discharged {h : Nat} (s : GapDenialState h)
    (hs : isDischarged s = false) : 0 < s.hops := by
  have hne : ¬ s.hops = 0 := by
    intro hzero
    have hd := (isDischarged_iff_hops s).2 hzero
    rw [hd] at hs
    exact Bool.noConfusion hs
  omega

/-- A gap that has not yet reached its compare/deny phase still owes hops. -/
theorem hops_pos_of_not_denying {h : Nat} (s : GapDenialState h)
    (hs : isDenying s = false) : 0 < s.hops := by
  refine hops_pos_of_not_discharged s ?_
  cases hd : isDischarged s with
  | false => rfl
  | true =>
      have hn := isDenying_of_isDischarged s hd
      rw [hn] at hs
      exact Bool.noConfusion hs

/-- **Bridge lemma.**  An unjoined root certifies that some gap of the
transport is still in transit.  This is what pays a pipelined interaction when
the ghost word itself cannot move: a root that has not rearmed is missing one
of its two receipts, and a missing receipt is an undischarged (respectively
not-yet-denying) gap, hence positive remaining hops. -/
theorem exists_hops_pos_of_not_rearmed {h m : Nat} (ring : DirectedRing m)
    (gap : Fin m → GapDenialState h) (i : Fin m)
    (hi : rearmedOf ring gap i = false) : ∃ g, 0 < (gap g).hops := by
  cases hr : rightReceiptOf gap i with
  | false => exact ⟨i, hops_pos_of_not_discharged (gap i) hr⟩
  | true =>
      have hl : leftReceiptOf ring gap i = false := by
        simp only [rearmedOf, hr, Bool.true_and] at hi
        exact hi
      exact ⟨ring.leftNeighbor i,
        hops_pos_of_not_denying (gap (ring.leftNeighbor i)) hl⟩

/-! ## One pipelined interaction -/

/-- The round-`k` word after one physical interaction: the joined-restricted
incidence step under the mask read off the **pre-step** carriers. -/
def stepWord {n h m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (state : PipelinedRoundState ring h) (edge : Fin n) : Configuration m :=
  joinedIncidenceStep P (rearmedOf ring state.tokens) state.word edge

/-- One scheduler interaction of the pipelined ghost round.  The same
interaction advances every gap carrier of round `k-1` and resolves the
round-`k` word at the roots that had already joined.  The round stops at its
first persistent candidate (success) or at a candidate-free complete
resolution (failure, necessarily one of the two uniform words). -/
noncomputable def pipelinedRoundStep {n h m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (L : GapLayout n h m)
    (state : PipelinedRoundState ring h) (edge : Fin n) :
    StopNode (PipelinedRoundState ring h) := by
  classical
  exact
    if hcand : ∃ i, Candidate10 ring (stepWord ring P state edge) i then
      .success
    else if hrace : HasRace (stepWord ring P state edge) then
      .active
        ⟨stepWord ring P state edge, multiLocalStep L state.tokens edge,
          hrace, fun i hi => hcand ⟨i, hi⟩⟩
    else .failure

theorem pipelinedRoundStep_eq_success_iff {n h m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (L : GapLayout n h m)
    (state : PipelinedRoundState ring h) (edge : Fin n) :
    pipelinedRoundStep ring P L state edge = .success ↔
      ∃ i, Candidate10 ring (stepWord ring P state edge) i := by
  classical
  by_cases hcand : ∃ i, Candidate10 ring (stepWord ring P state edge) i
  · simp [pipelinedRoundStep, hcand]
  · constructor
    · intro hstep
      by_cases hrace : HasRace (stepWord ring P state edge)
      · simp [pipelinedRoundStep, hcand, hrace] at hstep
      · simp [pipelinedRoundStep, hcand, hrace] at hstep
    · intro hc
      exact (hcand hc).elim

theorem pipelinedRoundStep_eq_failure_iff {n h m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (L : GapLayout n h m)
    (state : PipelinedRoundState ring h) (edge : Fin n) :
    pipelinedRoundStep ring P L state edge = .failure ↔
      (∀ i, ¬ Candidate10 ring (stepWord ring P state edge) i) ∧
        Frozen (stepWord ring P state edge) := by
  classical
  rw [← not_hasRace_iff_frozen]
  by_cases hcand : ∃ i, Candidate10 ring (stepWord ring P state edge) i
  · constructor
    · intro hstep
      simp [pipelinedRoundStep, hcand] at hstep
    · intro hright
      obtain ⟨i, hi⟩ := hcand
      exact (hright.1 i hi).elim
  · by_cases hrace : HasRace (stepWord ring P state edge)
    · simp [pipelinedRoundStep, hcand, hrace]
    · have hno : ∀ i, ¬ Candidate10 ring (stepWord ring P state edge) i := by
        intro i hi
        exact hcand ⟨i, hi⟩
      simp [pipelinedRoundStep, hrace, hno]

/-- The active child of a pipelined interaction carries the advanced
carriers. -/
theorem pipelinedRoundStep_active_tokens {n h m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (L : GapLayout n h m)
    (state : PipelinedRoundState ring h) (edge : Fin n)
    (child : PipelinedRoundState ring h)
    (hstep : pipelinedRoundStep ring P L state edge = .active child) :
    child.tokens = multiLocalStep L state.tokens edge := by
  classical
  simp only [pipelinedRoundStep] at hstep
  split at hstep
  · simp at hstep
  · split at hstep
    · injection hstep with heq
      rw [← heq]
    · simp at hstep

/-- The active child of a pipelined interaction carries the stepped word. -/
theorem pipelinedRoundStep_active_word {n h m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (L : GapLayout n h m)
    (state : PipelinedRoundState ring h) (edge : Fin n)
    (child : PipelinedRoundState ring h)
    (hstep : pipelinedRoundStep ring P L state edge = .active child) :
    child.word = stepWord ring P state edge := by
  classical
  simp only [pipelinedRoundStep] at hstep
  split at hstep
  · simp at hstep
  · split at hstep
    · injection hstep with heq
      rw [← heq]
    · simp at hstep

/-! ## P4-lite: the derived mask is monotone -/

/-- Receipts are never withdrawn by the transport, so the derived join
predicate never goes `true → false`. -/
theorem rearmed_monotone {n h m : Nat} (ring : DirectedRing m)
    (L : GapLayout n h m) (gap : Fin m → GapDenialState h) (edge : Fin n)
    (i : Fin m) (hi : rearmedOf ring gap i = true) :
    rearmedOf ring (multiLocalStep L gap edge) i = true :=
  rearmedOf_multiLocalStep ring L gap edge i hi

/-- **P4-lite for the pipelined process.**  A root that had joined round `k`
is still joined at the child state of every scheduler interaction.  Hence the
mask used by the child's `joinedIncidenceStep` dominates the parent's: the
ghost round only ever gains resolvable roots. -/
theorem rearmed_monotone_step {n h m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (L : GapLayout n h m)
    (state : PipelinedRoundState ring h) (edge : Fin n)
    (child : PipelinedRoundState ring h)
    (hstep : pipelinedRoundStep ring P L state edge = .active child)
    (i : Fin m) (hi : state.joined i = true) : child.joined i = true := by
  have htokens :=
    pipelinedRoundStep_active_tokens ring P L state edge child hstep
  show rearmedOf ring child.tokens i = true
  rw [htokens]
  exact rearmed_monotone ring L state.tokens edge i hi

/-! ## Local balance survives pipelining exactly -/

private theorem pipelined_successSum_eq_joinedGoodEdgeCount {n h m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (L : GapLayout n h m)
    (state : PipelinedRoundState ring h) :
    (List.ofFn (fun edge : Fin n =>
      successWeight (pipelinedRoundStep ring P L state edge))).sum =
        joinedGoodEdgeCount ring P (rearmedOf ring state.tokens)
          state.word := by
  classical
  unfold joinedGoodEdgeCount
  apply ofFn_sum_eq
  intro edge
  by_cases hgood :
      JoinedCreatesCandidate ring P (rearmedOf ring state.tokens)
        state.word edge
  · have hsuccess :=
      (pipelinedRoundStep_eq_success_iff ring P L state edge).mpr hgood
    simp [successWeight, hsuccess, joinedGoodEdge, hgood]
  · have hnot : pipelinedRoundStep ring P L state edge ≠ .success :=
      fun hh => hgood
        ((pipelinedRoundStep_eq_success_iff ring P L state edge).mp hh)
    cases hstep : pipelinedRoundStep ring P L state edge <;>
      simp_all [successWeight, joinedGoodEdge]

/-- A failed pipelined round ends in one of the two uniform frozen words. -/
theorem pipelined_failure_uniform {n h m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (L : GapLayout n h m)
    (state : PipelinedRoundState ring h) (edge : Fin n)
    (hfailure : pipelinedRoundStep ring P L state edge = .failure) :
    UniformFrozenBase (stepWord ring P state edge) := by
  have hterminal :=
    (pipelinedRoundStep_eq_failure_iff ring P L state edge).mp hfailure
  rcases frozen_candidate_or_uniform ring _ hterminal.2 with
      hcandidate | huniform
  · obtain ⟨candidate, hcandidate⟩ := hcandidate
    exact (hterminal.1 candidate hcandidate).elim
  · exact huniform

/-- A previously resolved root pins the value of every failed pipelined
round: the failing edge is a restricted bad edge for that base. -/
theorem pipelined_failure_restoresBase {n h m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (L : GapLayout n h m)
    (state : PipelinedRoundState ring h) (b : FrozenValue) (fixed : Fin m)
    (hfixed : state.word fixed = b.toChoice) (edge : Fin n)
    (hfailure : pipelinedRoundStep ring P L state edge = .failure) :
    JoinedRestoresBase b P (rearmedOf ring state.tokens) state.word edge := by
  have hne : state.word fixed ≠ .race := by
    cases b <;> simp [hfixed, FrozenValue.toChoice]
  have hpres : stepWord ring P state edge fixed = state.word fixed :=
    joinedIncidenceStep_of_ne_race P (rearmedOf ring state.tokens)
      state.word edge fixed hne
  have huniform := pipelined_failure_uniform ring P L state edge hfailure
  cases b with
  | in0 =>
      rcases huniform with hin0 | hout1
      · intro i
        exact hin0 i
      · have hcontra := hout1 fixed
        rw [hpres, hfixed] at hcontra
        exact Choice.noConfusion hcontra
  | out1 =>
      rcases huniform with hin0 | hout1
      · have hcontra := hin0 fixed
        rw [hpres, hfixed] at hcontra
        exact Choice.noConfusion hcontra
      · intro i
        exact hout1 i

private theorem pipelined_baseOrRace_of_failure {n h m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (L : GapLayout n h m)
    (state : PipelinedRoundState ring h) (b : FrozenValue) (fixed : Fin m)
    (hfixed : state.word fixed = b.toChoice) (edge : Fin n)
    (hfailure : pipelinedRoundStep ring P L state edge = .failure) :
    BaseOrRace b state.word := by
  have hrestore := pipelined_failure_restoresBase ring P L state b fixed
    hfixed edge hfailure
  intro i
  by_cases hi : state.word i = .race
  · exact Or.inl hi
  · right
    have hpres : stepWord ring P state edge i = state.word i :=
      joinedIncidenceStep_of_ne_race P (rearmedOf ring state.tokens)
        state.word edge i hi
    exact hpres.symm.trans (hrestore i)

private theorem pipelined_failureSum_eq_zero_of_noFailure {n h m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (L : GapLayout n h m)
    (state : PipelinedRoundState ring h)
    (hnoFailure : ∀ edge,
      pipelinedRoundStep ring P L state edge ≠ .failure) :
    (List.ofFn (fun edge : Fin n =>
      failureWeight (pipelinedRoundStep ring P L state edge))).sum = 0 := by
  calc
    (List.ofFn (fun edge : Fin n =>
        failureWeight (pipelinedRoundStep ring P L state edge))).sum =
        (List.ofFn (fun _ : Fin n => 0)).sum := by
          apply ofFn_sum_eq
          intro edge
          cases hstep : pipelinedRoundStep ring P L state edge <;>
            simp_all [failureWeight]
    _ = 0 := by rw [ofFn_sum_const, Nat.mul_zero]

private theorem pipelined_localBalance_of_fixed {n h m : Nat}
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m) (hn : 1 < n)
    (L : GapLayout n h m) (state : PipelinedRoundState ring h)
    (b : FrozenValue) (fixed : Fin m)
    (hfixed : state.word fixed = b.toChoice) (failedEdge : Fin n)
    (hfailed : pipelinedRoundStep ring P L state failedEdge = .failure) :
    (List.ofFn (fun edge : Fin n =>
      failureWeight (pipelinedRoundStep ring P L state edge))).sum ≤
        (List.ofFn (fun edge : Fin n =>
          successWeight (pipelinedRoundStep ring P L state edge))).sum := by
  classical
  have hbase := pipelined_baseOrRace_of_failure ring P L state b fixed hfixed
    failedEdge hfailed
  calc
    (List.ofFn (fun edge : Fin n =>
        failureWeight (pipelinedRoundStep ring P L state edge))).sum ≤
        joinedBadEdgeCount b P (rearmedOf ring state.tokens)
          state.word := by
          unfold joinedBadEdgeCount
          apply ofFn_sum_le
          intro edge
          cases hstep : pipelinedRoundStep ring P L state edge with
          | active child => simp [failureWeight]
          | success => simp [failureWeight]
          | failure =>
              have hrestore := pipelined_failure_restoresBase ring P L state b
                fixed hfixed edge hstep
              simp [failureWeight, joinedBadEdge, hrestore]
    _ ≤ joinedGoodEdgeCount ring P (rearmedOf ring state.tokens)
          state.word :=
      joinedGoodEdgeCount_ge_joinedBadEdgeCount ring hm P hn b
        (rearmedOf ring state.tokens) state.word hbase state.hasRace
    _ = (List.ofFn (fun edge : Fin n =>
        successWeight (pipelinedRoundStep ring P L state edge))).sum :=
      (pipelined_successSum_eq_joinedGoodEdgeCount ring P L state).symm

/-- **Pipelined local balance.**  At every active pipelined state the
immediate uniform-failure mass is at most the immediate candidate-creation
mass.

Three cases, exactly the ones isolated in the §4 case analysis.  If the word is mixed
and some edge fails, a resolved root pins the uniform base and the restricted
balance of `ShortGapJoinedIncidenceBalance` applies — which itself splits on
whether every unresolved root had joined (then the restricted step *is*
`incidenceStep` and the sequential theorem applies verbatim) or not (then the
restricted failure mass is zero).  If no edge fails, the failure mass is `0`.
If the word is all-Race, a frozen restricted step forces every root to have
joined, so the step is the bare incidence step and cannot freeze without
creating a candidate. -/
theorem pipelined_localBalance {n h m : Nat} (ring : DirectedRing m)
    (hm : 1 < m) (P : Placement n m) (hn : 1 < n) (L : GapLayout n h m)
    (state : PipelinedRoundState ring h) :
    (List.ofFn (fun edge : Fin n =>
      failureWeight (pipelinedRoundStep ring P L state edge))).sum ≤
        (List.ofFn (fun edge : Fin n =>
          successWeight (pipelinedRoundStep ring P L state edge))).sum := by
  classical
  by_cases hnonRace : HasNonRace state.word
  · obtain ⟨fixed, hfixed⟩ := hnonRace
    by_cases hfailure : ∃ edge,
        pipelinedRoundStep ring P L state edge = .failure
    · obtain ⟨failedEdge, hfailed⟩ := hfailure
      cases hvalue : state.word fixed with
      | race => exact (hfixed hvalue).elim
      | in0 =>
          exact pipelined_localBalance_of_fixed ring hm P hn L state
            .in0 fixed (by simpa [FrozenValue.toChoice] using hvalue)
            failedEdge hfailed
      | out1 =>
          exact pipelined_localBalance_of_fixed ring hm P hn L state
            .out1 fixed (by simpa [FrozenValue.toChoice] using hvalue)
            failedEdge hfailed
    · rw [pipelined_failureSum_eq_zero_of_noFailure ring P L state
          (fun edge hh => hfailure ⟨edge, hh⟩)]
      exact Nat.zero_le _
  · have hallRace : ∀ i, state.word i = .race := by
      intro i
      cases hvalue : state.word i with
      | race => rfl
      | in0 => exact (hnonRace ⟨i, by simp [hvalue]⟩).elim
      | out1 => exact (hnonRace ⟨i, by simp [hvalue]⟩).elim
    have hnoFailure : ∀ edge,
        pipelinedRoundStep ring P L state edge ≠ .failure := by
      intro edge hfail
      have hterminal :=
        (pipelinedRoundStep_eq_failure_iff ring P L state edge).mp hfail
      have hjoined : ∀ i, state.word i = .race →
          rearmedOf ring state.tokens i = true :=
        all_joined_of_frozen P (rearmedOf ring state.tokens) state.word edge
          hterminal.2
      have heq : stepWord ring P state edge =
          incidenceStep P state.word edge :=
        joinedIncidenceStep_eq_of_all_joined P (rearmedOf ring state.tokens)
          state.word edge hjoined
      have hno := hterminal.1
      have hfrozen := hterminal.2
      rw [heq] at hno hfrozen
      obtain ⟨candidate, hcandidate⟩ :=
        allRace_incidence_frozen_hasCandidate ring hm P state.word hallRace
          edge hfrozen
      exact hno candidate hcandidate
    rw [pipelined_failureSum_eq_zero_of_noFailure ring P L state hnoFailure]
    exact Nat.zero_le _

/-! ## The combined pipelined potential -/

/-- Combined potential: `n` times the round-`k` Race reserve plus
the residual round-`(k-1)` carrier hops.  Neither summand ever increases and
at least one strictly decreases on some scheduler child. -/
def pipelinedRoundPotential {n h m : Nat} (ring : DirectedRing m) :
    StopNode (PipelinedRoundState ring h) → Nat
  | .active state => n * (choiceRaceReserve state.word + totalHops state.tokens)
  | .success => 0
  | .failure => 0

private theorem pipelinedRoundPotential_step_le {n h m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (L : GapLayout n h m)
    (state : PipelinedRoundState ring h) (edge : Fin n) :
    pipelinedRoundPotential (n := n) ring
        (pipelinedRoundStep ring P L state edge) ≤
      n * (choiceRaceReserve (stepWord ring P state edge) +
        totalHops (multiLocalStep L state.tokens edge)) := by
  classical
  simp only [pipelinedRoundStep]
  split
  · simp [pipelinedRoundPotential]
  · split
    · simp [pipelinedRoundPotential]
    · simp [pipelinedRoundPotential]

/-- **The pipelined child-sum inequality.**  One unit of strict progress is
exposed among the `n` scheduler children of every active pipelined state.

The case split is exactly the obstruction of
`ShortGapJoinedIncidenceBalance`: with a joined unresolved root, that root's
outgoing port lowers the Race reserve (`joinedReserve_childSum`) while the
carriers never gain hops; with no joined unresolved root the restricted step
is a literal stutter and the reserve child-sum saturates
(`joinedReserve_childSum_eq_of_no_joined_race`), but then the state's own Race
witness is unjoined, so `exists_hops_pos_of_not_rearmed` produces an
in-transit gap and `totalHops_childSum` pays the interaction instead. -/
theorem pipelined_childSum {n h m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (L : GapLayout n h m)
    (state : PipelinedRoundState ring h) :
    1 + (List.ofFn (fun edge : Fin n =>
      choiceRaceReserve (stepWord ring P state edge) +
        totalHops (multiLocalStep L state.tokens edge))).sum ≤
      n * (choiceRaceReserve state.word + totalHops state.tokens) := by
  classical
  have hsplit :
      (List.ofFn (fun edge : Fin n =>
        choiceRaceReserve (stepWord ring P state edge) +
          totalHops (multiLocalStep L state.tokens edge))).sum =
        (List.ofFn (fun edge : Fin n =>
          choiceRaceReserve (stepWord ring P state edge))).sum +
        (List.ofFn (fun edge : Fin n =>
          totalHops (multiLocalStep L state.tokens edge))).sum :=
    ofFn_sum_add _ _
  have hexpand :
      n * (choiceRaceReserve state.word + totalHops state.tokens) =
        n * choiceRaceReserve state.word + n * totalHops state.tokens :=
    Nat.mul_add _ _ _
  by_cases hjoined :
      ∃ i, state.word i = .race ∧ rearmedOf ring state.tokens i = true
  · have hword : 1 + (List.ofFn (fun edge : Fin n =>
          choiceRaceReserve (stepWord ring P state edge))).sum ≤
            n * choiceRaceReserve state.word :=
      joinedReserve_childSum P (rearmedOf ring state.tokens)
        state.word hjoined
    have htokens :
        (List.ofFn (fun edge : Fin n =>
          totalHops (multiLocalStep L state.tokens edge))).sum ≤
          n * totalHops state.tokens := by
      calc
        (List.ofFn (fun edge : Fin n =>
            totalHops (multiLocalStep L state.tokens edge))).sum ≤
            (List.ofFn (fun _ : Fin n => totalHops state.tokens)).sum :=
          ofFn_sum_le _ _
            (fun edge => totalHops_multiLocalStep_le L state.tokens edge)
        _ = n * totalHops state.tokens := ofFn_sum_const _ _
    rw [hsplit, hexpand]
    omega
  · have hnone : ∀ i, state.word i = .race →
        rearmedOf ring state.tokens i = false := by
      intro i hi
      cases hr : rearmedOf ring state.tokens i with
      | false => rfl
      | true => exact absurd ⟨i, hi, hr⟩ hjoined
    have hword : (List.ofFn (fun edge : Fin n =>
          choiceRaceReserve (stepWord ring P state edge))).sum =
            n * choiceRaceReserve state.word :=
      joinedReserve_childSum_eq_of_no_joined_race P
        (rearmedOf ring state.tokens) state.word hnone
    obtain ⟨witness, hwitness⟩ := state.hasRace
    obtain ⟨g, hg⟩ := exists_hops_pos_of_not_rearmed ring state.tokens witness
      (hnone witness hwitness)
    have htokens : 1 + (List.ofFn (fun edge : Fin n =>
          totalHops (multiLocalStep L state.tokens edge))).sum ≤
            n * totalHops state.tokens :=
      totalHops_childSum L (⟨state.tokens, ⟨g, hg⟩⟩ : MultiGapState h m)
    rw [hsplit, hexpand, hword]
    omega

/-- **The pipelined Bellman certificate.**  The combined potential
`Φ = n * (Race reserve of the round-k word + residual round-(k-1) hops)` is a
scale-one `NatBellmanSuperSolution` for the stopped pipelined round. -/
theorem pipelined_natBellmanSuperSolution {n h m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (L : GapLayout n h m) :
    NatBellmanSuperSolution (pipelinedRoundStep ring P L) 1
      (pipelinedRoundPotential (n := n) ring) := by
  refine ⟨rfl, rfl, ?_⟩
  intro state
  have hdebt := pipelined_childSum ring P L state
  have hscaled := Nat.mul_le_mul_left n hdebt
  have hchildren :
      (List.ofFn (fun edge : Fin n =>
        pipelinedRoundPotential (n := n) ring
          (pipelinedRoundStep ring P L state edge))).sum ≤
        n * (List.ofFn (fun edge : Fin n =>
          choiceRaceReserve (stepWord ring P state edge) +
            totalHops (multiLocalStep L state.tokens edge))).sum := by
    calc
      (List.ofFn (fun edge : Fin n =>
          pipelinedRoundPotential (n := n) ring
            (pipelinedRoundStep ring P L state edge))).sum ≤
          (List.ofFn (fun edge : Fin n =>
            n * (choiceRaceReserve (stepWord ring P state edge) +
              totalHops (multiLocalStep L state.tokens edge)))).sum := by
            apply ofFn_sum_le
            intro edge
            exact pipelinedRoundPotential_step_le ring P L state edge
      _ = n * (List.ofFn (fun edge : Fin n =>
          choiceRaceReserve (stepWord ring P state edge) +
            totalHops (multiLocalStep L state.tokens edge))).sum :=
        ofFn_sum_mul_left n _
  calc
    1 * n + (List.ofFn (fun edge : Fin n =>
        pipelinedRoundPotential (n := n) ring
          (pipelinedRoundStep ring P L state edge))).sum ≤
        n + n * (List.ofFn (fun edge : Fin n =>
          choiceRaceReserve (stepWord ring P state edge) +
            totalHops (multiLocalStep L state.tokens edge))).sum := by
          simpa using Nat.add_le_add_left hchildren n
    _ = n * (1 + (List.ofFn (fun edge : Fin n =>
          choiceRaceReserve (stepWord ring P state edge) +
            totalHops (multiLocalStep L state.tokens edge))).sum) := by
        rw [Nat.mul_add, Nat.mul_one]
    _ ≤ n * (n * (choiceRaceReserve state.word +
          totalHops state.tokens)) := hscaled
    _ = n * pipelinedRoundPotential (n := n) ring (.active state) := rfl

/-! ## Start values -/

/-- Every gap discharged: the terminal carrier state of a completed denial
service. -/
def allDischarged (h m : Nat) : Fin m → GapDenialState h :=
  fun _ => .denyLeft 0 (Nat.zero_le h)

@[simp] theorem totalHops_allDischarged (h m : Nat) :
    totalHops (allDischarged h m) = 0 := by
  unfold totalHops allDischarged
  calc
    (List.ofFn (fun _ : Fin m =>
        (GapDenialState.denyLeft (h := h) 0 (Nat.zero_le h)).hops)).sum =
        (List.ofFn (fun _ : Fin m => 0)).sum := by
          apply ofFn_sum_eq
          intro g
          rfl
    _ = 0 := by rw [ofFn_sum_const, Nat.mul_zero]

@[simp] theorem rearmedOf_allDischarged {h m : Nat} (ring : DirectedRing m)
    (i : Fin m) : rearmedOf ring (allDischarged h m) i = true := rfl

/-- A discharged carrier state is a fixed point of the transport. -/
theorem multiLocalStep_allDischarged {n h m : Nat} (L : GapLayout n h m)
    (edge : Fin n) :
    multiLocalStep L (allDischarged h m) edge = allDischarged h m := by
  funext g
  simp [multiLocalStep, allDischarged, GapDenialState.localStep,
    GapDenialState.advanceEdge]

/-- With every carrier discharged, every root has joined and the pipelined
word step is literally the sequential bare incidence step: the ghost round
degenerates to the round of `ShortGapChoiceStopping`. -/
theorem stepWord_of_allDischarged {n h m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (state : PipelinedRoundState ring h)
    (htokens : state.tokens = allDischarged h m) (edge : Fin n) :
    stepWord ring P state edge = incidenceStep P state.word edge := by
  unfold stepWord
  rw [htokens]
  exact joinedIncidenceStep_eq_of_all_joined P
    (rearmedOf ring (allDischarged h m)) state.word edge
    (fun i _ => rearmedOf_allDischarged ring i)

/-- Fresh pipelined entry: every root unresolved in round `k`, every gap of
round `k-1` still at its launched declaration. -/
def freshRoundState {m : Nat} (ring : DirectedRing m) {h : Nat}
    (hm : 0 < m) (hpos : 0 < h) : PipelinedRoundState ring h :=
  ⟨allRaceConfiguration m, fun _ => .declareRight 0 hpos,
    allRaceConfiguration_hasRace hm, allRaceConfiguration_noCandidate ring⟩

/-- Sequential entry: every root unresolved in round `k`, every round-`(k-1)`
denial already discharged. -/
def entryRoundState {m : Nat} (ring : DirectedRing m) {h : Nat}
    (hm : 0 < m) : PipelinedRoundState ring h :=
  ⟨allRaceConfiguration m, allDischarged h m,
    allRaceConfiguration_hasRace hm, allRaceConfiguration_noCandidate ring⟩

/-- Start bound with a full residual denial service: `n * (m + 2*h*m)`. -/
@[simp] theorem pipelinedRoundPotential_freshRoundState {n h m : Nat}
    (ring : DirectedRing m) (hm : 0 < m) (hpos : 0 < h) :
    pipelinedRoundPotential (n := n) ring
        (.active (freshRoundState ring hm hpos)) =
      n * (m + m * (2 * h)) := by
  simp [pipelinedRoundPotential, freshRoundState, choiceRaceReserve_allRace]

/-- Start bound with no residual denial service: `n * m`, the sequential
round potential of `ShortGapChoiceStopping`. -/
@[simp] theorem pipelinedRoundPotential_entryRoundState {n h m : Nat}
    (ring : DirectedRing m) (hm : 0 < m) :
    pipelinedRoundPotential (n := n) ring
        (.active (entryRoundState (h := h) ring hm)) = n * m := by
  simp [pipelinedRoundPotential, entryRoundState, choiceRaceReserve_allRace]

/-! ## The round-`k` denial service and its admissible exits -/

/-- An admissible round-`(k+1)` entry read off the completed round-`k`
carriers.  Its word may be an arbitrary *partially played* next round: only
"still has an unresolved root" and "no candidate yet" are required, which is
the bounded arbitrary return state.  The `Race` reserve is then bounded by
`m` automatically, which is the `hexit` hypothesis of the composition. -/
structure RoundEntryMap {m : Nat} (ring : DirectedRing m) (h : Nat) where
  word : (Fin m → GapDenialState h) → Configuration m
  hasRace : ∀ gap, HasRace (word gap)
  noCandidate : ∀ gap i, ¬ Candidate10 ring (word gap) i

/-- The round state an admissible entry produces on the completed carriers. -/
def RoundEntryMap.state {m h : Nat} {ring : DirectedRing m}
    (E : RoundEntryMap ring h) (gap : Fin m → GapDenialState h) :
    PipelinedRoundState ring h :=
  ⟨E.word gap, gap, E.hasRace gap, E.noCandidate gap⟩

/-- The canonical admissible entry: every root rearms to `Race`. -/
def allRaceEntryMap {m : Nat} (ring : DirectedRing m) (h : Nat) (hm : 0 < m) :
    RoundEntryMap ring h where
  word := fun _ => allRaceConfiguration m
  hasRace := fun _ => allRaceConfiguration_hasRace hm
  noCandidate := fun _ => allRaceConfiguration_noCandidate ring

/-- One scheduler interaction of the round-`k` denial service: the token walk
of `ShortGapDenialTransport`, exiting into an admissible round-`(k+1)` state
as soon as every gap is discharged.  The sidecar success port of the
composition interface is available but unused here. -/
noncomputable def pipelinedServiceStep {n h m : Nat} {ring : DirectedRing m}
    (L : GapLayout n h m) (E : RoundEntryMap ring h)
    (state : MultiGapState h m) (edge : Fin n) :
    ServiceOutcome (MultiGapState h m) (PipelinedRoundState ring h) := by
  classical
  exact
    if hnext : ∃ g, 0 < ((multiLocalStep L state.gap edge) g).hops then
      .cont ⟨multiLocalStep L state.gap edge, hnext⟩
    else .exit (E.state (multiLocalStep L state.gap edge))

/-- Residual service potential. -/
def pipelinedServicePotential {n h m : Nat} (state : MultiGapState h m) :
    Nat := n * totalHops state.gap

private theorem pipelinedServiceOutcome_le {n h m : Nat}
    {ring : DirectedRing m} (L : GapLayout n h m) (E : RoundEntryMap ring h)
    (state : MultiGapState h m) (edge : Fin n) :
    serviceOutcomePotential (pipelinedServicePotential (n := n))
        (pipelinedServiceStep L E state edge) ≤
      n * totalHops (multiLocalStep L state.gap edge) := by
  classical
  simp only [pipelinedServiceStep]
  split
  · simp [serviceOutcomePotential, pipelinedServicePotential]
  · simp [serviceOutcomePotential]

/-- The round-`k` denial service is a scale-one Bellman supersolution for its
own residual-hop potential.  This is `multiGap_natBellmanSuperSolution` read
through the partial-exit service interface. -/
theorem pipelinedService_bellman {n h m : Nat} {ring : DirectedRing m}
    (L : GapLayout n h m) (E : RoundEntryMap ring h) :
    ServiceBellman (pipelinedServiceStep L E) 1
      (pipelinedServicePotential (n := n)) := by
  intro state
  have hdebt := totalHops_childSum L state
  have hscaled := Nat.mul_le_mul_left n hdebt
  have hchildren :
      (List.ofFn (fun edge : Fin n =>
        serviceOutcomePotential (pipelinedServicePotential (n := n))
          (pipelinedServiceStep L E state edge))).sum ≤
        n * (List.ofFn (fun edge : Fin n =>
          totalHops (multiLocalStep L state.gap edge))).sum := by
    calc
      (List.ofFn (fun edge : Fin n =>
          serviceOutcomePotential (pipelinedServicePotential (n := n))
            (pipelinedServiceStep L E state edge))).sum ≤
          (List.ofFn (fun edge : Fin n =>
            n * totalHops (multiLocalStep L state.gap edge))).sum :=
        ofFn_sum_le _ _ (fun edge =>
          pipelinedServiceOutcome_le L E state edge)
      _ = n * (List.ofFn (fun edge : Fin n =>
          totalHops (multiLocalStep L state.gap edge))).sum :=
        ofFn_sum_mul_left n _
  calc
    1 * n + (List.ofFn (fun edge : Fin n =>
        serviceOutcomePotential (pipelinedServicePotential (n := n))
          (pipelinedServiceStep L E state edge))).sum ≤
        n + n * (List.ofFn (fun edge : Fin n =>
          totalHops (multiLocalStep L state.gap edge))).sum := by
          simpa using Nat.add_le_add_left hchildren n
    _ = n * (1 + (List.ofFn (fun edge : Fin n =>
          totalHops (multiLocalStep L state.gap edge))).sum) := by
        rw [Nat.mul_add, Nat.mul_one]
    _ ≤ n * (n * totalHops state.gap) := hscaled
    _ = n * pipelinedServicePotential (n := n) state := rfl

private theorem totalHops_eq_zero_of_no_active {h m : Nat}
    (gap : Fin m → GapDenialState h)
    (hnone : ¬ ∃ g, 0 < (gap g).hops) : totalHops gap = 0 := by
  unfold totalHops
  calc
    (List.ofFn (fun g : Fin m => (gap g).hops)).sum =
        (List.ofFn (fun _ : Fin m => 0)).sum := by
          apply ofFn_sum_eq
          intro g
          have : ¬ 0 < (gap g).hops := fun hg => hnone ⟨g, hg⟩
          omega
    _ = 0 := by rw [ofFn_sum_const, Nat.mul_zero]

/-- **`hexit`.**  Every admissible round the service can exit into has
potential at most `n * m`: its carriers are discharged, so only the `Race`
reserve of the next word contributes, and that is at most `m`. -/
theorem pipelinedService_exit_le {n h m : Nat} {ring : DirectedRing m}
    (L : GapLayout n h m) (E : RoundEntryMap ring h)
    (state : MultiGapState h m) (edge : Fin n)
    (r : PipelinedRoundState ring h)
    (hstep : pipelinedServiceStep L E state edge = .exit r) :
    pipelinedRoundPotential (n := n) ring (.active r) ≤ n * m := by
  classical
  simp only [pipelinedServiceStep] at hstep
  split at hstep
  · simp at hstep
  · rename_i hnone
    injection hstep with heq
    have hzero : totalHops (multiLocalStep L state.gap edge) = 0 :=
      totalHops_eq_zero_of_no_active _ hnone
    rw [← heq]
    show n * (choiceRaceReserve (E.state (multiLocalStep L state.gap edge)).word
      + totalHops (E.state (multiLocalStep L state.gap edge)).tokens) ≤ n * m
    show n * (choiceRaceReserve (E.word (multiLocalStep L state.gap edge))
      + totalHops (multiLocalStep L state.gap edge)) ≤ n * m
    rw [hzero, Nat.add_zero]
    exact Nat.mul_le_mul_left n
      (choiceRaceReserve_le (E.word (multiLocalStep L state.gap edge)))

/-- **`hentry`.**  A uniform round failure restarts every gap at its launched
declaration, so the service is entered at potential exactly
`n * (m * (2 * h))`. -/
@[simp] theorem pipelinedServicePotential_allDeclareStart {n h m : Nat}
    (L : GapLayout n h m) (hm : 0 < m) :
    pipelinedServicePotential (n := n) (allDeclareStart L hm) =
      n * (m * (2 * h)) := by
  simp [pipelinedServicePotential, allDeclareStart]

/-! ## The composed pipelined process -/

/-- The composed pipelined process: a ghost round whose uniform failure enters
its own denial service, whose service completion exits into an admissible
partially played next round. -/
noncomputable def pipelinedComposedStep {n h m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (L : GapLayout n h m) (E : RoundEntryMap ring h)
    (hm : 0 < m) :
    RestartState (PipelinedRoundState ring h) (MultiGapState h m) → Fin n →
      StopNode (RestartState (PipelinedRoundState ring h)
        (MultiGapState h m)) :=
  partialExitEntryStep (pipelinedRoundStep ring P L)
    (fun _ _ => allDeclareStart L hm) (pipelinedServiceStep L E)

/-- Composed potential with `A = n * m` and `R = n * (m * (2 * h))`. -/
def pipelinedComposedPotential {n h m : Nat} (ring : DirectedRing m) :
    StopNode (RestartState (PipelinedRoundState ring h)
      (MultiGapState h m)) → Nat :=
  partialExitPotential (pipelinedRoundPotential (n := n) ring)
    (pipelinedServicePotential (n := n)) (n * m) (n * (m * (2 * h)))

/-- **The composed pipelined Bellman certificate.** -/
theorem pipelinedComposed_natBellmanSuperSolution {n h m : Nat}
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m) (hn : 1 < n)
    (L : GapLayout n h m) (E : RoundEntryMap ring h) :
    NatBellmanSuperSolution
      (pipelinedComposedStep ring P L E (by omega)) 1
      (pipelinedComposedPotential (n := n) ring) :=
  partialExitEntry_natBellmanSuperSolution (pipelinedRoundStep ring P L)
    (fun _ _ => allDeclareStart L (by omega)) (pipelinedServiceStep L E)
    (pipelinedRoundPotential (n := n) ring)
    (pipelinedServicePotential (n := n))
    (pipelined_natBellmanSuperSolution ring P L)
    (pipelinedService_bellman L E)
    (fun state => pipelined_localBalance ring hm P hn L state)
    (fun state edge r hstep =>
      pipelinedService_exit_le L E state edge r hstep)
    (fun _ _ _ => Nat.le_of_eq
      (pipelinedServicePotential_allDeclareStart L (by omega)))

/-- The composed process has no bad terminal. -/
theorem pipelinedComposedStep_ne_failure {n h m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (L : GapLayout n h m)
    (E : RoundEntryMap ring h) (hm : 0 < m) :
    ∀ state edge, pipelinedComposedStep ring P L E hm state edge ≠ .failure :=
  partialExitEntryStep_ne_failure (pipelinedRoundStep ring P L)
    (fun _ _ => allDeclareStart L hm) (pipelinedServiceStep L E)

private theorem budget_eq (n h m : Nat) :
    2 * (n * m) * (1 + h) = 2 * (n * m) + n * (m * (2 * h)) := by
  rw [Nat.mul_add, Nat.mul_one]
  have hswap : n * (m * (2 * h)) = 2 * (n * m) * h := by ac_rfl
  rw [hswap]

/-- **The composed budget.**  From the sequential entry round the composed
potential is exactly `2 * (n * m) * (1 + h)`: two copies of `n * m` for the
balanced ghost round and `2 * n * m * h` for every carrier hop of the `m` gaps
of length `h`.  This is the `2 * A + R` shape of
`partialExitPotential_roundBase_le`, now with a state-dependent entry and an
arbitrary admissible exit. -/
theorem pipelinedComposedPotential_entryRoundState {n h m : Nat}
    (ring : DirectedRing m) (hm : 0 < m) :
    pipelinedComposedPotential (n := n) (h := h) ring
        (.active (.round (entryRoundState ring hm))) =
      2 * (n * m) * (1 + h) := by
  rw [budget_eq]
  simp only [pipelinedComposedPotential, partialExitPotential,
    pipelinedRoundPotential_entryRoundState ring hm]
  omega

/-- **The composed complexity bound.**  Truncated expected work of the
complete pipelined process, from the sequential entry round, is at most
`2 * n * m * (1 + h)` — the same budget the strictly alternating token-walk
composition of `ShortGapDenialTransport` reaches, now proved for a round
certificate that tolerates arbitrary residual denial debt at entry and an
arbitrary partially played word at exit. -/
theorem pipelinedComposed_truncatedCost_le {n h m : Nat}
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m) (hn : 1 < n)
    (L : GapLayout n h m) (E : RoundEntryMap ring h) (T : Nat) :
    truncatedActiveCostNumerator
        (pipelinedComposedStep ring P L E (by omega))
        (.active (.round (entryRoundState ring (by omega)))) T ≤
      n ^ T * (2 * (n * m) * (1 + h)) := by
  have hsuper := pipelinedComposed_natBellmanSuperSolution ring hm P hn L E
  have hcost := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (pipelinedComposedStep ring P L E (by omega)) 1
    (pipelinedComposedPotential (n := n) ring) hsuper
    (.active (.round (entryRoundState ring (by omega)))) T
  rw [pipelinedComposedPotential_entryRoundState ring (by omega)] at hcost
  omega

/-- The same bound at the canonical exit map, where service completion rearms
every root to `Race`.  This instantiates every interface of the file at a
concrete admissible entry, so none of the statements above is vacuous. -/
theorem allRaceEntry_pipelinedComposed_truncatedCost_le {n h m : Nat}
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m) (hn : 1 < n)
    (L : GapLayout n h m) (T : Nat) :
    truncatedActiveCostNumerator
        (pipelinedComposedStep ring P L
          (allRaceEntryMap ring h (by omega)) (by omega))
        (.active (.round (entryRoundState ring (by omega)))) T ≤
      n ^ T * (2 * (n * m) * (1 + h)) :=
  pipelinedComposed_truncatedCost_le ring hm P hn L
    (allRaceEntryMap ring h (by omega)) T

/-- Reciprocal finite-horizon success tail for the complete pipelined process.
With `factor = n`, at least a `1 - 1/n` fraction of scheduler words of length
`n * (2 * n * m * (1 + h))` has already produced a persistent candidate. -/
theorem pipelinedComposed_success_one_minus_inv_factor {n h m factor : Nat}
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m) (hn : 1 < n)
    (L : GapLayout n h m) (E : RoundEntryMap ring h) :
    (factor - 1) * n ^ (factor * (2 * (n * m) * (1 + h))) ≤
      factor * successCount (pipelinedComposedStep ring P L E (by omega))
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
      (fun _ _ => allDeclareStart L (by omega : 0 < m))
      (pipelinedServiceStep L E)
      (entryRoundState (h := h) ring (by omega))
      (pipelinedRoundPotential (n := n) ring)
      (pipelinedServicePotential (n := n))
      (pipelined_natBellmanSuperSolution ring P L)
      (pipelinedService_bellman L E)
      (fun state => pipelined_localBalance ring hm P hn L state)
      (fun state edge r hstep =>
        pipelinedService_exit_le L E state edge r hstep)
      (fun _ _ _ => Nat.le_of_eq
        (pipelinedServicePotential_allDeclareStart L (by omega)))
      hpositive (factor := factor)
  rw [pipelinedRoundPotential_entryRoundState ring (by omega)] at htail
  rw [budget_eq]
  have hshape : n * m + (n * m + n * (m * (2 * h))) =
      2 * (n * m) + n * (m * (2 * h)) := by omega
  rw [hshape] at htail
  exact htail

#print axioms rearmed_monotone_step
#print axioms pipelined_localBalance
#print axioms pipelined_childSum
#print axioms pipelined_natBellmanSuperSolution
#print axioms pipelinedService_bellman
#print axioms pipelinedComposed_natBellmanSuperSolution
#print axioms pipelinedComposedPotential_entryRoundState
#print axioms pipelinedComposed_truncatedCost_le
#print axioms allRaceEntry_pipelinedComposed_truncatedCost_le
#print axioms pipelinedComposed_success_one_minus_inv_factor

end ShortGapPipelinedRearm

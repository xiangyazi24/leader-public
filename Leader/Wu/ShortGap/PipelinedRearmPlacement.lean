import Leader.Wu.ShortGap.PipelinedRearm
import Leader.Wu.ShortGap.DenialTransportPlacement
import Leader.Wu.ShortGap.GapTiling

/-!
# Pipelined ghost rounds on placement-derived gaps of variable length

`Leader/Wu/ShortGap/PipelinedRearm.lean` ran the pipelined ghost round over `m`
gaps of one common length `h` whose edge sets were supplied abstractly by a
`GapLayout n h m`.  This file lifts that instantiation twice.

1. **Variable lengths.**  The carriers become the dependent family
   `tokens : (g : Fin m) → GapDenialState (L.len g)` of a
   `VarGapLayout n m`, stepped by `varLocalStep` with debt `varTotalHops`.
   `ShortGapTwoDenialJoin`'s receipt projection is fixed-`h`, so the three
   projections are redefined here over the dependent family
   (`varRightReceiptOf`, `varLeftReceiptOf`, `varRearmedOf`); the two phase
   predicates `isDischarged` and `isDenying` and their step-monotonicity
   lemmas are `h`-generic and are reused verbatim.  The derived join mask, the
   bridge lemma "unjoined root ⇒ some gap still owes hops", the local balance,
   and the scale-one Bellman certificate for
   `Φ = n * (choiceRaceReserve word + varTotalHops tokens)` all go through with
   the same case split as the fixed-length file.
2. **Placement-derived gaps.**  Under `RootsOrdered ring P` the gaps of
   `placementLayout ring P hord hm` have length
   `gapLen ring P g = cwDist (P.root g) (P.root (ring.rightNeighbor g))` and
   tile the physical ring: `gapLen_sum_eq` of
   `Leader/Wu/ShortGap/GapTiling.lean` gives `L.totalLength = n`, so the composed
   budget `2*(n*m) + 2*n*L.totalLength` becomes `2*n*(m+n)`.

**Budgets.**  With `A = n * m` (exit: `choiceRaceReserve_le`, discharged
carriers) and `R = n * (2 * L.totalLength)` (entry: every gap restarted at its
launched declaration), the composed potential at the sequential entry round is
exactly `2*(n*m) + 2*n*L.totalLength`, hence `2*n*(m+n)` for the
placement-derived layout.  Uniform lengths `h` with `m * h = n` recover
`2*(n*m)*(1+h)` of the fixed-length file
(`ShortGapDenialTransportPlacement.tiling_budget_eq_uniform_budget`).

**Quotients still in force (unchanged from the fixed-length file).**

* The carriers are the abstract one-token-per-gap stop-and-wait walk, not the
  literal rows of `Leader/Wu/ShortGap/LiteralGapRows.lean`: no forgery, no
  staleness, no authentication, no shared-root field bookkeeping beyond
  disjointness of the layout's edge sets, and the comparison outcome is fixed
  to a denial.  The per-gap debt is the `2 * len g` out-and-back count, not
  the literal `2 * len g - 1`.
* `word` is a ghost object.  This file does **not** prove that a literal
  pipelined execution projects onto it (obligation P1) nor that a
  round-`k` candidate cannot be discarded by a later rearm (P2).  Those
  refinement obligations are exactly what the accounting theorem here would
  consume.
* The composed process alternates the two *accounting* modes.  Its round
  certificate holds at an arbitrary residual carrier state and its service
  exits into an arbitrary admissible partially played next word, which is what
  makes it pipelining-aware; the `ServiceOutcome.succeed` sidecar port is
  available, charged `0`, and unused.
* `RootsOrdered ring P` is a hypothesis on the placement, imported as such
  from `ShortGapDenialTransportPlacement`; it is not derived here.
* Nothing here claims stabilization or a final leader-election bound.
-/

namespace ShortGapPipelinedRearmPlacement

open FiniteUniformStoppingTree
open PeriodHIncidenceChoice
open ShortGapChoiceStopping
open ShortGapDenialTransport
open ShortGapTwoDenialJoin
open ShortGapJoinedIncidenceBalance
open ShortGapPipelinedRearm
open ShortGapDenialTransportPlacement
open ShortGapGapTiling
open BalancedFailureRestart
open BalancedFailureRestartPartialExit
open BalancedFailureRestartPartialExitEntry

set_option autoImplicit false

/-! ## Receipt projections of a variable-length carrier family

`ShortGapTwoDenialJoin` defines these for a fixed common length; the phase
predicates `isDischarged` / `isDenying` are `h`-generic, so only the three
projections need redefining over the dependent family. -/

/-- Root `i`'s clockwise receipt: gap `i` has been discharged. -/
def varRightReceiptOf {n m : Nat} (L : VarGapLayout n m)
    (gap : (g : Fin m) → GapDenialState (L.len g)) (i : Fin m) : Bool :=
  isDischarged (gap i)

/-- Root `j`'s counterclockwise receipt: the gap ending at `j` has reached its
compare/deny phase. -/
def varLeftReceiptOf {n m : Nat} (ring : DirectedRing m)
    (L : VarGapLayout n m)
    (gap : (g : Fin m) → GapDenialState (L.len g)) (j : Fin m) : Bool :=
  isDenying (gap (ring.leftNeighbor j))

/-- Root `i` may rearm: both receipts present.  This is the derived join
predicate of the ghost round. -/
def varRearmedOf {n m : Nat} (ring : DirectedRing m) (L : VarGapLayout n m)
    (gap : (g : Fin m) → GapDenialState (L.len g)) (i : Fin m) : Bool :=
  varRightReceiptOf L gap i && varLeftReceiptOf ring L gap i

theorem varRightReceiptOf_varLocalStep {n m : Nat} (L : VarGapLayout n m)
    (gap : (g : Fin m) → GapDenialState (L.len g)) (e : Fin n) (i : Fin m)
    (hi : varRightReceiptOf L gap i = true) :
    varRightReceiptOf L (varLocalStep L gap e) i = true :=
  isDischarged_localStep (L.edgeAt i) (gap i) e hi

theorem varLeftReceiptOf_varLocalStep {n m : Nat} (ring : DirectedRing m)
    (L : VarGapLayout n m)
    (gap : (g : Fin m) → GapDenialState (L.len g)) (e : Fin n) (j : Fin m)
    (hj : varLeftReceiptOf ring L gap j = true) :
    varLeftReceiptOf ring L (varLocalStep L gap e) j = true :=
  isDenying_localStep (L.edgeAt (ring.leftNeighbor j))
    (gap (ring.leftNeighbor j)) e hj

/-- Receipts, hence rearm permissions, are never withdrawn by the transport. -/
theorem varRearmedOf_varLocalStep {n m : Nat} (ring : DirectedRing m)
    (L : VarGapLayout n m)
    (gap : (g : Fin m) → GapDenialState (L.len g)) (e : Fin n) (i : Fin m)
    (hi : varRearmedOf ring L gap i = true) :
    varRearmedOf ring L (varLocalStep L gap e) i = true := by
  simp only [varRearmedOf, Bool.and_eq_true] at hi ⊢
  exact ⟨varRightReceiptOf_varLocalStep L gap e i hi.1,
    varLeftReceiptOf_varLocalStep ring L gap e i hi.2⟩

/-- **Bridge lemma, variable lengths.**  An unjoined root certifies that some
gap of the transport is still in transit: it is missing a receipt, and a
missing receipt is an undischarged (respectively not-yet-denying) gap.  The
two `hops`-positivity lemmas are `h`-generic and reused from
`Leader/Wu/ShortGap/PipelinedRearm.lean`. -/
theorem var_exists_hops_pos_of_not_rearmed {n m : Nat} (ring : DirectedRing m)
    (L : VarGapLayout n m)
    (gap : (g : Fin m) → GapDenialState (L.len g)) (i : Fin m)
    (hi : varRearmedOf ring L gap i = false) : ∃ g, 0 < (gap g).hops := by
  cases hr : varRightReceiptOf L gap i with
  | false => exact ⟨i, hops_pos_of_not_discharged (gap i) hr⟩
  | true =>
      have hl : varLeftReceiptOf ring L gap i = false := by
        simp only [varRearmedOf, hr, Bool.true_and] at hi
        exact hi
      exact ⟨ring.leftNeighbor i,
        hops_pos_of_not_denying (gap (ring.leftNeighbor i)) hl⟩

/-! ## The variable-length pipelined ghost-round state -/

/-- One ghost round `k` over a variable-length layout: the round-`k` word
together with the round-`(k-1)` denial carriers, one per gap, each of its own
physical length. -/
structure VarPipelinedRoundState {n m : Nat} (ring : DirectedRing m)
    (L : VarGapLayout n m) where
  word : Configuration m
  tokens : (g : Fin m) → GapDenialState (L.len g)
  hasRace : HasRace word
  noCandidate : ∀ i, ¬ Candidate10 ring word i

/-- The derived join predicate of a pipelined state. -/
def VarPipelinedRoundState.joined {n m : Nat} {ring : DirectedRing m}
    {L : VarGapLayout n m} (state : VarPipelinedRoundState ring L) :
    Fin m → Bool :=
  varRearmedOf ring L state.tokens

/-- The round-`k` word after one physical interaction: the joined-restricted
incidence step under the mask read off the **pre-step** carriers. -/
def varStepWord {n m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (L : VarGapLayout n m) (state : VarPipelinedRoundState ring L)
    (edge : Fin n) : Configuration m :=
  joinedIncidenceStep P (varRearmedOf ring L state.tokens) state.word edge

/-- One scheduler interaction of the variable-length pipelined ghost round:
the same interaction advances every gap carrier of round `k-1` and resolves
the round-`k` word at the roots that had already joined. -/
noncomputable def varPipelinedRoundStep {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (L : VarGapLayout n m)
    (state : VarPipelinedRoundState ring L) (edge : Fin n) :
    StopNode (VarPipelinedRoundState ring L) := by
  classical
  exact
    if hcand : ∃ i, Candidate10 ring (varStepWord ring P L state edge) i then
      .success
    else if hrace : HasRace (varStepWord ring P L state edge) then
      .active
        ⟨varStepWord ring P L state edge, varLocalStep L state.tokens edge,
          hrace, fun i hi => hcand ⟨i, hi⟩⟩
    else .failure

theorem varPipelinedRoundStep_eq_success_iff {n m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (L : VarGapLayout n m)
    (state : VarPipelinedRoundState ring L) (edge : Fin n) :
    varPipelinedRoundStep ring P L state edge = .success ↔
      ∃ i, Candidate10 ring (varStepWord ring P L state edge) i := by
  classical
  by_cases hcand : ∃ i, Candidate10 ring (varStepWord ring P L state edge) i
  · simp [varPipelinedRoundStep, hcand]
  · constructor
    · intro hstep
      by_cases hrace : HasRace (varStepWord ring P L state edge)
      · simp [varPipelinedRoundStep, hcand, hrace] at hstep
      · simp [varPipelinedRoundStep, hcand, hrace] at hstep
    · intro hc
      exact (hcand hc).elim

theorem varPipelinedRoundStep_eq_failure_iff {n m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (L : VarGapLayout n m)
    (state : VarPipelinedRoundState ring L) (edge : Fin n) :
    varPipelinedRoundStep ring P L state edge = .failure ↔
      (∀ i, ¬ Candidate10 ring (varStepWord ring P L state edge) i) ∧
        Frozen (varStepWord ring P L state edge) := by
  classical
  rw [← not_hasRace_iff_frozen]
  by_cases hcand : ∃ i, Candidate10 ring (varStepWord ring P L state edge) i
  · constructor
    · intro hstep
      simp [varPipelinedRoundStep, hcand] at hstep
    · intro hright
      obtain ⟨i, hi⟩ := hcand
      exact (hright.1 i hi).elim
  · by_cases hrace : HasRace (varStepWord ring P L state edge)
    · simp [varPipelinedRoundStep, hcand, hrace]
    · have hno : ∀ i, ¬ Candidate10 ring
          (varStepWord ring P L state edge) i := by
        intro i hi
        exact hcand ⟨i, hi⟩
      simp [varPipelinedRoundStep, hrace, hno]

theorem varPipelinedRoundStep_active_tokens {n m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (L : VarGapLayout n m)
    (state : VarPipelinedRoundState ring L) (edge : Fin n)
    (child : VarPipelinedRoundState ring L)
    (hstep : varPipelinedRoundStep ring P L state edge = .active child) :
    child.tokens = varLocalStep L state.tokens edge := by
  classical
  simp only [varPipelinedRoundStep] at hstep
  split at hstep
  · simp at hstep
  · split at hstep
    · injection hstep with heq
      rw [← heq]
    · simp at hstep

theorem varPipelinedRoundStep_active_word {n m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (L : VarGapLayout n m)
    (state : VarPipelinedRoundState ring L) (edge : Fin n)
    (child : VarPipelinedRoundState ring L)
    (hstep : varPipelinedRoundStep ring P L state edge = .active child) :
    child.word = varStepWord ring P L state edge := by
  classical
  simp only [varPipelinedRoundStep] at hstep
  split at hstep
  · simp at hstep
  · split at hstep
    · injection hstep with heq
      rw [← heq]
    · simp at hstep

/-- **P4-lite, variable lengths.**  A root that had joined round `k` is still
joined at the child state of every scheduler interaction. -/
theorem varRearmed_monotone_step {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (L : VarGapLayout n m)
    (state : VarPipelinedRoundState ring L) (edge : Fin n)
    (child : VarPipelinedRoundState ring L)
    (hstep : varPipelinedRoundStep ring P L state edge = .active child)
    (i : Fin m) (hi : state.joined i = true) : child.joined i = true := by
  have htokens :=
    varPipelinedRoundStep_active_tokens ring P L state edge child hstep
  show varRearmedOf ring L child.tokens i = true
  rw [htokens]
  exact varRearmedOf_varLocalStep ring L state.tokens edge i hi

/-! ## Local balance -/

private theorem varPipelined_successSum_eq_joinedGoodEdgeCount {n m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (L : VarGapLayout n m)
    (state : VarPipelinedRoundState ring L) :
    (List.ofFn (fun edge : Fin n =>
      successWeight (varPipelinedRoundStep ring P L state edge))).sum =
        joinedGoodEdgeCount ring P (varRearmedOf ring L state.tokens)
          state.word := by
  classical
  unfold joinedGoodEdgeCount
  apply ofFn_sum_eq
  intro edge
  by_cases hgood :
      JoinedCreatesCandidate ring P (varRearmedOf ring L state.tokens)
        state.word edge
  · have hsuccess :=
      (varPipelinedRoundStep_eq_success_iff ring P L state edge).mpr hgood
    simp [successWeight, hsuccess, joinedGoodEdge, hgood]
  · have hnot : varPipelinedRoundStep ring P L state edge ≠ .success :=
      fun hh => hgood
        ((varPipelinedRoundStep_eq_success_iff ring P L state edge).mp hh)
    cases hstep : varPipelinedRoundStep ring P L state edge <;>
      simp_all [successWeight, joinedGoodEdge]

theorem varPipelined_failure_uniform {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (L : VarGapLayout n m)
    (state : VarPipelinedRoundState ring L) (edge : Fin n)
    (hfailure : varPipelinedRoundStep ring P L state edge = .failure) :
    UniformFrozenBase (varStepWord ring P L state edge) := by
  have hterminal :=
    (varPipelinedRoundStep_eq_failure_iff ring P L state edge).mp hfailure
  rcases frozen_candidate_or_uniform ring _ hterminal.2 with
      hcandidate | huniform
  · obtain ⟨candidate, hcandidate⟩ := hcandidate
    exact (hterminal.1 candidate hcandidate).elim
  · exact huniform

theorem varPipelined_failure_restoresBase {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (L : VarGapLayout n m)
    (state : VarPipelinedRoundState ring L) (b : FrozenValue) (fixed : Fin m)
    (hfixed : state.word fixed = b.toChoice) (edge : Fin n)
    (hfailure : varPipelinedRoundStep ring P L state edge = .failure) :
    JoinedRestoresBase b P (varRearmedOf ring L state.tokens)
      state.word edge := by
  have hne : state.word fixed ≠ .race := by
    cases b <;> simp [hfixed, FrozenValue.toChoice]
  have hpres : varStepWord ring P L state edge fixed = state.word fixed :=
    joinedIncidenceStep_of_ne_race P (varRearmedOf ring L state.tokens)
      state.word edge fixed hne
  have huniform := varPipelined_failure_uniform ring P L state edge hfailure
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

private theorem varPipelined_baseOrRace_of_failure {n m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (L : VarGapLayout n m)
    (state : VarPipelinedRoundState ring L) (b : FrozenValue) (fixed : Fin m)
    (hfixed : state.word fixed = b.toChoice) (edge : Fin n)
    (hfailure : varPipelinedRoundStep ring P L state edge = .failure) :
    BaseOrRace b state.word := by
  have hrestore := varPipelined_failure_restoresBase ring P L state b fixed
    hfixed edge hfailure
  intro i
  by_cases hi : state.word i = .race
  · exact Or.inl hi
  · right
    have hpres : varStepWord ring P L state edge i = state.word i :=
      joinedIncidenceStep_of_ne_race P (varRearmedOf ring L state.tokens)
        state.word edge i hi
    exact hpres.symm.trans (hrestore i)

private theorem varPipelined_failureSum_eq_zero_of_noFailure {n m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (L : VarGapLayout n m)
    (state : VarPipelinedRoundState ring L)
    (hnoFailure : ∀ edge,
      varPipelinedRoundStep ring P L state edge ≠ .failure) :
    (List.ofFn (fun edge : Fin n =>
      failureWeight (varPipelinedRoundStep ring P L state edge))).sum = 0 := by
  calc
    (List.ofFn (fun edge : Fin n =>
        failureWeight (varPipelinedRoundStep ring P L state edge))).sum =
        (List.ofFn (fun _ : Fin n => 0)).sum := by
          apply ofFn_sum_eq
          intro edge
          cases hstep : varPipelinedRoundStep ring P L state edge <;>
            simp_all [failureWeight]
    _ = 0 := by rw [ofFn_sum_const, Nat.mul_zero]

private theorem varPipelined_localBalance_of_fixed {n m : Nat}
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m) (hn : 1 < n)
    (L : VarGapLayout n m) (state : VarPipelinedRoundState ring L)
    (b : FrozenValue) (fixed : Fin m)
    (hfixed : state.word fixed = b.toChoice) (failedEdge : Fin n)
    (hfailed : varPipelinedRoundStep ring P L state failedEdge = .failure) :
    (List.ofFn (fun edge : Fin n =>
      failureWeight (varPipelinedRoundStep ring P L state edge))).sum ≤
        (List.ofFn (fun edge : Fin n =>
          successWeight (varPipelinedRoundStep ring P L state edge))).sum := by
  classical
  have hbase := varPipelined_baseOrRace_of_failure ring P L state b fixed
    hfixed failedEdge hfailed
  calc
    (List.ofFn (fun edge : Fin n =>
        failureWeight (varPipelinedRoundStep ring P L state edge))).sum ≤
        joinedBadEdgeCount b P (varRearmedOf ring L state.tokens)
          state.word := by
          unfold joinedBadEdgeCount
          apply ofFn_sum_le
          intro edge
          cases hstep : varPipelinedRoundStep ring P L state edge with
          | active child => simp [failureWeight]
          | success => simp [failureWeight]
          | failure =>
              have hrestore := varPipelined_failure_restoresBase ring P L state
                b fixed hfixed edge hstep
              simp [failureWeight, joinedBadEdge, hrestore]
    _ ≤ joinedGoodEdgeCount ring P (varRearmedOf ring L state.tokens)
          state.word :=
      joinedGoodEdgeCount_ge_joinedBadEdgeCount ring hm P hn b
        (varRearmedOf ring L state.tokens) state.word hbase state.hasRace
    _ = (List.ofFn (fun edge : Fin n =>
        successWeight (varPipelinedRoundStep ring P L state edge))).sum :=
      (varPipelined_successSum_eq_joinedGoodEdgeCount ring P L state).symm

/-- **Pipelined local balance, variable lengths.**  At every active pipelined
state the immediate uniform-failure mass is at most the immediate
candidate-creation mass.  Same three cases as the fixed-length file: a mixed
word with a failing edge reduces to the restricted balance (which itself
splits on whether every unresolved root had joined); no failing edge gives
mass `0`; an all-Race word cannot freeze without creating a candidate, because
a frozen restricted step forces every root to have joined and hence to be
stepped by the bare `incidenceStep`. -/
theorem varPipelined_localBalance {n m : Nat} (ring : DirectedRing m)
    (hm : 1 < m) (P : Placement n m) (hn : 1 < n) (L : VarGapLayout n m)
    (state : VarPipelinedRoundState ring L) :
    (List.ofFn (fun edge : Fin n =>
      failureWeight (varPipelinedRoundStep ring P L state edge))).sum ≤
        (List.ofFn (fun edge : Fin n =>
          successWeight (varPipelinedRoundStep ring P L state edge))).sum := by
  classical
  by_cases hnonRace : HasNonRace state.word
  · obtain ⟨fixed, hfixed⟩ := hnonRace
    by_cases hfailure : ∃ edge,
        varPipelinedRoundStep ring P L state edge = .failure
    · obtain ⟨failedEdge, hfailed⟩ := hfailure
      cases hvalue : state.word fixed with
      | race => exact (hfixed hvalue).elim
      | in0 =>
          exact varPipelined_localBalance_of_fixed ring hm P hn L state
            .in0 fixed (by simpa [FrozenValue.toChoice] using hvalue)
            failedEdge hfailed
      | out1 =>
          exact varPipelined_localBalance_of_fixed ring hm P hn L state
            .out1 fixed (by simpa [FrozenValue.toChoice] using hvalue)
            failedEdge hfailed
    · rw [varPipelined_failureSum_eq_zero_of_noFailure ring P L state
          (fun edge hh => hfailure ⟨edge, hh⟩)]
      exact Nat.zero_le _
  · have hallRace : ∀ i, state.word i = .race := by
      intro i
      cases hvalue : state.word i with
      | race => rfl
      | in0 => exact (hnonRace ⟨i, by simp [hvalue]⟩).elim
      | out1 => exact (hnonRace ⟨i, by simp [hvalue]⟩).elim
    have hnoFailure : ∀ edge,
        varPipelinedRoundStep ring P L state edge ≠ .failure := by
      intro edge hfail
      have hterminal :=
        (varPipelinedRoundStep_eq_failure_iff ring P L state edge).mp hfail
      have hjoined : ∀ i, state.word i = .race →
          varRearmedOf ring L state.tokens i = true :=
        all_joined_of_frozen P (varRearmedOf ring L state.tokens) state.word
          edge hterminal.2
      have heq : varStepWord ring P L state edge =
          incidenceStep P state.word edge :=
        joinedIncidenceStep_eq_of_all_joined P
          (varRearmedOf ring L state.tokens) state.word edge hjoined
      have hno := hterminal.1
      have hfrozen := hterminal.2
      rw [heq] at hno hfrozen
      obtain ⟨candidate, hcandidate⟩ :=
        allRace_incidence_frozen_hasCandidate ring hm P state.word hallRace
          edge hfrozen
      exact hno candidate hcandidate
    rw [varPipelined_failureSum_eq_zero_of_noFailure ring P L state hnoFailure]
    exact Nat.zero_le _

/-! ## The combined variable-length potential -/

/-- Combined potential: `n` times the round-`k` Race reserve plus
the residual round-`(k-1)` carrier hops of the variable-length layout. -/
def varPipelinedRoundPotential {n m : Nat} (ring : DirectedRing m)
    (L : VarGapLayout n m) :
    StopNode (VarPipelinedRoundState ring L) → Nat
  | .active state =>
      n * (choiceRaceReserve state.word + varTotalHops L state.tokens)
  | .success => 0
  | .failure => 0

private theorem varPipelinedRoundPotential_step_le {n m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (L : VarGapLayout n m)
    (state : VarPipelinedRoundState ring L) (edge : Fin n) :
    varPipelinedRoundPotential ring L
        (varPipelinedRoundStep ring P L state edge) ≤
      n * (choiceRaceReserve (varStepWord ring P L state edge) +
        varTotalHops L (varLocalStep L state.tokens edge)) := by
  classical
  simp only [varPipelinedRoundStep]
  split
  · simp [varPipelinedRoundPotential]
  · split
    · simp [varPipelinedRoundPotential]
    · simp [varPipelinedRoundPotential]

/-- **The variable-length pipelined child-sum inequality.**  With a joined
unresolved root, `joinedReserve_childSum` pays the interaction and the
carriers never gain hops; with no joined unresolved root the restricted step
is a literal stutter, but then the state's own Race witness is unjoined, so
`var_exists_hops_pos_of_not_rearmed` produces an in-transit gap and
`varTotalHops_childSum` pays instead. -/
theorem varPipelined_childSum {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (L : VarGapLayout n m)
    (state : VarPipelinedRoundState ring L) :
    1 + (List.ofFn (fun edge : Fin n =>
      choiceRaceReserve (varStepWord ring P L state edge) +
        varTotalHops L (varLocalStep L state.tokens edge))).sum ≤
      n * (choiceRaceReserve state.word + varTotalHops L state.tokens) := by
  classical
  have hsplit :
      (List.ofFn (fun edge : Fin n =>
        choiceRaceReserve (varStepWord ring P L state edge) +
          varTotalHops L (varLocalStep L state.tokens edge))).sum =
        (List.ofFn (fun edge : Fin n =>
          choiceRaceReserve (varStepWord ring P L state edge))).sum +
        (List.ofFn (fun edge : Fin n =>
          varTotalHops L (varLocalStep L state.tokens edge))).sum :=
    ofFn_sum_add _ _
  have hexpand :
      n * (choiceRaceReserve state.word + varTotalHops L state.tokens) =
        n * choiceRaceReserve state.word + n * varTotalHops L state.tokens :=
    Nat.mul_add _ _ _
  by_cases hjoined :
      ∃ i, state.word i = .race ∧ varRearmedOf ring L state.tokens i = true
  · have hword : 1 + (List.ofFn (fun edge : Fin n =>
          choiceRaceReserve (varStepWord ring P L state edge))).sum ≤
            n * choiceRaceReserve state.word :=
      joinedReserve_childSum P (varRearmedOf ring L state.tokens)
        state.word hjoined
    have htokens :
        (List.ofFn (fun edge : Fin n =>
          varTotalHops L (varLocalStep L state.tokens edge))).sum ≤
          n * varTotalHops L state.tokens := by
      calc
        (List.ofFn (fun edge : Fin n =>
            varTotalHops L (varLocalStep L state.tokens edge))).sum ≤
            (List.ofFn (fun _ : Fin n => varTotalHops L state.tokens)).sum :=
          ofFn_sum_le _ _
            (fun edge => varTotalHops_localStep_le L state.tokens edge)
        _ = n * varTotalHops L state.tokens := ofFn_sum_const _ _
    rw [hsplit, hexpand]
    omega
  · have hnone : ∀ i, state.word i = .race →
        varRearmedOf ring L state.tokens i = false := by
      intro i hi
      cases hr : varRearmedOf ring L state.tokens i with
      | false => rfl
      | true => exact absurd ⟨i, hi, hr⟩ hjoined
    have hword : (List.ofFn (fun edge : Fin n =>
          choiceRaceReserve (varStepWord ring P L state edge))).sum =
            n * choiceRaceReserve state.word :=
      joinedReserve_childSum_eq_of_no_joined_race P
        (varRearmedOf ring L state.tokens) state.word hnone
    obtain ⟨witness, hwitness⟩ := state.hasRace
    obtain ⟨g, hg⟩ := var_exists_hops_pos_of_not_rearmed ring L state.tokens
      witness (hnone witness hwitness)
    have htokens : 1 + (List.ofFn (fun edge : Fin n =>
          varTotalHops L (varLocalStep L state.tokens edge))).sum ≤
            n * varTotalHops L state.tokens :=
      varTotalHops_childSum L (⟨state.tokens, ⟨g, hg⟩⟩ : VarMultiGapState L)
    rw [hsplit, hexpand, hword]
    omega

/-- **The variable-length pipelined Bellman certificate.** -/
theorem varPipelined_natBellmanSuperSolution {n m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (L : VarGapLayout n m) :
    NatBellmanSuperSolution (varPipelinedRoundStep ring P L) 1
      (varPipelinedRoundPotential ring L) := by
  refine ⟨rfl, rfl, ?_⟩
  intro state
  have hdebt := varPipelined_childSum ring P L state
  have hscaled := Nat.mul_le_mul_left n hdebt
  have hchildren :
      (List.ofFn (fun edge : Fin n =>
        varPipelinedRoundPotential ring L
          (varPipelinedRoundStep ring P L state edge))).sum ≤
        n * (List.ofFn (fun edge : Fin n =>
          choiceRaceReserve (varStepWord ring P L state edge) +
            varTotalHops L (varLocalStep L state.tokens edge))).sum := by
    calc
      (List.ofFn (fun edge : Fin n =>
          varPipelinedRoundPotential ring L
            (varPipelinedRoundStep ring P L state edge))).sum ≤
          (List.ofFn (fun edge : Fin n =>
            n * (choiceRaceReserve (varStepWord ring P L state edge) +
              varTotalHops L (varLocalStep L state.tokens edge)))).sum := by
            apply ofFn_sum_le
            intro edge
            exact varPipelinedRoundPotential_step_le ring P L state edge
      _ = n * (List.ofFn (fun edge : Fin n =>
          choiceRaceReserve (varStepWord ring P L state edge) +
            varTotalHops L (varLocalStep L state.tokens edge))).sum :=
        ofFn_sum_mul_left n _
  calc
    1 * n + (List.ofFn (fun edge : Fin n =>
        varPipelinedRoundPotential ring L
          (varPipelinedRoundStep ring P L state edge))).sum ≤
        n + n * (List.ofFn (fun edge : Fin n =>
          choiceRaceReserve (varStepWord ring P L state edge) +
            varTotalHops L (varLocalStep L state.tokens edge))).sum := by
          simpa using Nat.add_le_add_left hchildren n
    _ = n * (1 + (List.ofFn (fun edge : Fin n =>
          choiceRaceReserve (varStepWord ring P L state edge) +
            varTotalHops L (varLocalStep L state.tokens edge))).sum) := by
        rw [Nat.mul_add, Nat.mul_one]
    _ ≤ n * (n * (choiceRaceReserve state.word +
          varTotalHops L state.tokens)) := hscaled
    _ = n * varPipelinedRoundPotential ring L (.active state) := rfl

/-! ## Start values -/

/-- Every gap discharged: the terminal carrier family of a completed denial
service. -/
def varAllDischarged {n m : Nat} (L : VarGapLayout n m) :
    (g : Fin m) → GapDenialState (L.len g) :=
  fun g => .denyLeft 0 (Nat.zero_le (L.len g))

@[simp] theorem varTotalHops_allDischarged {n m : Nat}
    (L : VarGapLayout n m) : varTotalHops L (varAllDischarged L) = 0 := by
  have h : varTotalHops L (varAllDischarged L) =
      (List.ofFn (fun _ : Fin m => (0 : Nat))).sum :=
    ofFn_sum_eq _ _ (fun g => rfl)
  rw [h, ofFn_sum_const, Nat.mul_zero]

@[simp] theorem varRearmedOf_allDischarged {n m : Nat}
    (ring : DirectedRing m) (L : VarGapLayout n m) (i : Fin m) :
    varRearmedOf ring L (varAllDischarged L) i = true := rfl

/-- A discharged carrier family is a fixed point of the transport. -/
theorem varLocalStep_allDischarged {n m : Nat} (L : VarGapLayout n m)
    (edge : Fin n) :
    varLocalStep L (varAllDischarged L) edge = varAllDischarged L := by
  funext g
  simp [varLocalStep, varAllDischarged, GapDenialState.localStep,
    GapDenialState.advanceEdge]

/-- With every root joined the pipelined word step is literally the sequential
bare incidence step: the ghost round degenerates to the round of
`ShortGapChoiceStopping`. -/
theorem varStepWord_of_all_joined {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (L : VarGapLayout n m)
    (state : VarPipelinedRoundState ring L)
    (hall : ∀ i, varRearmedOf ring L state.tokens i = true) (edge : Fin n) :
    varStepWord ring P L state edge = incidenceStep P state.word edge :=
  joinedIncidenceStep_eq_of_all_joined P (varRearmedOf ring L state.tokens)
    state.word edge (fun i _ => hall i)

/-- Fresh pipelined entry: every root unresolved in round `k`, every gap of
round `k-1` still at its launched declaration. -/
def varFreshRoundState {n m : Nat} (ring : DirectedRing m)
    (L : VarGapLayout n m) (hm : 0 < m) : VarPipelinedRoundState ring L :=
  ⟨allRaceConfiguration m, fun g => .declareRight 0 (L.len_pos g),
    allRaceConfiguration_hasRace hm, allRaceConfiguration_noCandidate ring⟩

/-- Sequential entry: every root unresolved in round `k`, every round-`(k-1)`
denial already discharged. -/
def varEntryRoundState {n m : Nat} (ring : DirectedRing m)
    (L : VarGapLayout n m) (hm : 0 < m) : VarPipelinedRoundState ring L :=
  ⟨allRaceConfiguration m, varAllDischarged L,
    allRaceConfiguration_hasRace hm, allRaceConfiguration_noCandidate ring⟩

/-- Start bound with a full residual denial service:
`n * (m + 2 * Σ_g len g)`. -/
@[simp] theorem varPipelinedRoundPotential_freshRoundState {n m : Nat}
    (ring : DirectedRing m) (L : VarGapLayout n m) (hm : 0 < m) :
    varPipelinedRoundPotential ring L
        (.active (varFreshRoundState ring L hm)) =
      n * (m + 2 * L.totalLength) := by
  simp [varPipelinedRoundPotential, varFreshRoundState,
    choiceRaceReserve_allRace]

/-- Start bound with no residual denial service: `n * m`, the sequential round
potential of `ShortGapChoiceStopping`. -/
@[simp] theorem varPipelinedRoundPotential_entryRoundState {n m : Nat}
    (ring : DirectedRing m) (L : VarGapLayout n m) (hm : 0 < m) :
    varPipelinedRoundPotential ring L
        (.active (varEntryRoundState ring L hm)) = n * m := by
  simp [varPipelinedRoundPotential, varEntryRoundState,
    choiceRaceReserve_allRace]

/-! ## The round-`k` denial service and its admissible exits -/

/-- An admissible round-`(k+1)` entry read off the completed round-`k`
carriers: an arbitrary partially played word that still has an unresolved root
and no candidate. -/
structure VarRoundEntryMap {n m : Nat} (ring : DirectedRing m)
    (L : VarGapLayout n m) where
  word : ((g : Fin m) → GapDenialState (L.len g)) → Configuration m
  hasRace : ∀ gap, HasRace (word gap)
  noCandidate : ∀ gap i, ¬ Candidate10 ring (word gap) i

/-- The round state an admissible entry produces on the completed carriers. -/
def VarRoundEntryMap.state {n m : Nat} {ring : DirectedRing m}
    {L : VarGapLayout n m} (E : VarRoundEntryMap ring L)
    (gap : (g : Fin m) → GapDenialState (L.len g)) :
    VarPipelinedRoundState ring L :=
  ⟨E.word gap, gap, E.hasRace gap, E.noCandidate gap⟩

/-- The canonical admissible entry: every root rearms to `Race`. -/
def varAllRaceEntryMap {n m : Nat} (ring : DirectedRing m)
    (L : VarGapLayout n m) (hm : 0 < m) : VarRoundEntryMap ring L where
  word := fun _ => allRaceConfiguration m
  hasRace := fun _ => allRaceConfiguration_hasRace hm
  noCandidate := fun _ => allRaceConfiguration_noCandidate ring

/-- One scheduler interaction of the round-`k` denial service: the
variable-length token walk, exiting into an admissible round-`(k+1)` state as
soon as every gap is discharged. -/
noncomputable def varPipelinedServiceStep {n m : Nat}
    {ring : DirectedRing m} (L : VarGapLayout n m)
    (E : VarRoundEntryMap ring L)
    (state : VarMultiGapState L) (edge : Fin n) :
    ServiceOutcome (VarMultiGapState L) (VarPipelinedRoundState ring L) := by
  classical
  exact
    if hnext : ∃ g, 0 < ((varLocalStep L state.gap edge) g).hops then
      .cont ⟨varLocalStep L state.gap edge, hnext⟩
    else .exit (E.state (varLocalStep L state.gap edge))

/-- Residual service potential. -/
def varPipelinedServicePotential {n m : Nat} (L : VarGapLayout n m)
    (state : VarMultiGapState L) : Nat := n * varTotalHops L state.gap

private theorem varPipelinedServiceOutcome_le {n m : Nat}
    {ring : DirectedRing m} (L : VarGapLayout n m)
    (E : VarRoundEntryMap ring L) (state : VarMultiGapState L)
    (edge : Fin n) :
    serviceOutcomePotential (varPipelinedServicePotential L)
        (varPipelinedServiceStep L E state edge) ≤
      n * varTotalHops L (varLocalStep L state.gap edge) := by
  classical
  simp only [varPipelinedServiceStep]
  split
  · simp [serviceOutcomePotential, varPipelinedServicePotential]
  · simp [serviceOutcomePotential]

/-- The round-`k` denial service is a scale-one Bellman supersolution for its
own residual-hop potential. -/
theorem varPipelinedService_bellman {n m : Nat} {ring : DirectedRing m}
    (L : VarGapLayout n m) (E : VarRoundEntryMap ring L) :
    ServiceBellman (varPipelinedServiceStep L E) 1
      (varPipelinedServicePotential L) := by
  intro state
  have hdebt := varTotalHops_childSum L state
  have hscaled := Nat.mul_le_mul_left n hdebt
  have hchildren :
      (List.ofFn (fun edge : Fin n =>
        serviceOutcomePotential (varPipelinedServicePotential L)
          (varPipelinedServiceStep L E state edge))).sum ≤
        n * (List.ofFn (fun edge : Fin n =>
          varTotalHops L (varLocalStep L state.gap edge))).sum := by
    calc
      (List.ofFn (fun edge : Fin n =>
          serviceOutcomePotential (varPipelinedServicePotential L)
            (varPipelinedServiceStep L E state edge))).sum ≤
          (List.ofFn (fun edge : Fin n =>
            n * varTotalHops L (varLocalStep L state.gap edge))).sum :=
        ofFn_sum_le _ _ (fun edge =>
          varPipelinedServiceOutcome_le L E state edge)
      _ = n * (List.ofFn (fun edge : Fin n =>
          varTotalHops L (varLocalStep L state.gap edge))).sum :=
        ofFn_sum_mul_left n _
  calc
    1 * n + (List.ofFn (fun edge : Fin n =>
        serviceOutcomePotential (varPipelinedServicePotential L)
          (varPipelinedServiceStep L E state edge))).sum ≤
        n + n * (List.ofFn (fun edge : Fin n =>
          varTotalHops L (varLocalStep L state.gap edge))).sum := by
          simpa using Nat.add_le_add_left hchildren n
    _ = n * (1 + (List.ofFn (fun edge : Fin n =>
          varTotalHops L (varLocalStep L state.gap edge))).sum) := by
        rw [Nat.mul_add, Nat.mul_one]
    _ ≤ n * (n * varTotalHops L state.gap) := hscaled
    _ = n * varPipelinedServicePotential L state := rfl

private theorem varTotalHops_eq_zero_of_no_active {n m : Nat}
    (L : VarGapLayout n m)
    (gap : (g : Fin m) → GapDenialState (L.len g))
    (hnone : ¬ ∃ g, 0 < (gap g).hops) : varTotalHops L gap = 0 := by
  have h : varTotalHops L gap = (List.ofFn (fun _ : Fin m => (0 : Nat))).sum :=
    ofFn_sum_eq _ _ (fun g => by
      have hg : ¬ 0 < (gap g).hops := fun hpos => hnone ⟨g, hpos⟩
      omega)
  rw [h, ofFn_sum_const, Nat.mul_zero]

/-- **`hexit`.**  Every admissible round the service can exit into has
potential at most `n * m`: its carriers are discharged, so only the `Race`
reserve of the next word contributes, and that is at most `m`. -/
theorem varPipelinedService_exit_le {n m : Nat} {ring : DirectedRing m}
    (L : VarGapLayout n m) (E : VarRoundEntryMap ring L)
    (state : VarMultiGapState L) (edge : Fin n)
    (r : VarPipelinedRoundState ring L)
    (hstep : varPipelinedServiceStep L E state edge = .exit r) :
    varPipelinedRoundPotential ring L (.active r) ≤ n * m := by
  classical
  simp only [varPipelinedServiceStep] at hstep
  split at hstep
  · simp at hstep
  · rename_i hnone
    injection hstep with heq
    have hzero : varTotalHops L (varLocalStep L state.gap edge) = 0 :=
      varTotalHops_eq_zero_of_no_active L _ hnone
    rw [← heq]
    show n * (choiceRaceReserve
        (E.state (varLocalStep L state.gap edge)).word +
      varTotalHops L (E.state (varLocalStep L state.gap edge)).tokens) ≤ n * m
    show n * (choiceRaceReserve (E.word (varLocalStep L state.gap edge)) +
      varTotalHops L (varLocalStep L state.gap edge)) ≤ n * m
    rw [hzero, Nat.add_zero]
    exact Nat.mul_le_mul_left n
      (choiceRaceReserve_le (E.word (varLocalStep L state.gap edge)))

/-- **`hentry`.**  A uniform round failure restarts every gap at its launched
declaration, so the service is entered at potential exactly
`n * (2 * Σ_g len g)`. -/
@[simp] theorem varPipelinedServicePotential_allDeclareStart {n m : Nat}
    (L : VarGapLayout n m) (hm : 0 < m) :
    varPipelinedServicePotential L (varAllDeclareStart L hm) =
      n * (2 * L.totalLength) := by
  simp [varPipelinedServicePotential, varAllDeclareStart]

/-! ## The composed variable-length pipelined process -/

/-- The composed pipelined process on a variable-length layout. -/
noncomputable def varPipelinedComposedStep {n m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (L : VarGapLayout n m)
    (E : VarRoundEntryMap ring L) (hm : 0 < m) :
    RestartState (VarPipelinedRoundState ring L) (VarMultiGapState L) →
      Fin n →
      StopNode (RestartState (VarPipelinedRoundState ring L)
        (VarMultiGapState L)) :=
  partialExitEntryStep (varPipelinedRoundStep ring P L)
    (fun _ _ => varAllDeclareStart L hm) (varPipelinedServiceStep L E)

/-- Composed potential with `A = n * m` and `R = n * (2 * Σ_g len g)`. -/
def varPipelinedComposedPotential {n m : Nat} (ring : DirectedRing m)
    (L : VarGapLayout n m) :
    StopNode (RestartState (VarPipelinedRoundState ring L)
      (VarMultiGapState L)) → Nat :=
  partialExitPotential (varPipelinedRoundPotential ring L)
    (varPipelinedServicePotential L) (n * m) (n * (2 * L.totalLength))

/-- **The composed variable-length pipelined Bellman certificate.** -/
theorem varPipelinedComposed_natBellmanSuperSolution {n m : Nat}
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m) (hn : 1 < n)
    (L : VarGapLayout n m) (E : VarRoundEntryMap ring L) :
    NatBellmanSuperSolution
      (varPipelinedComposedStep ring P L E (by omega)) 1
      (varPipelinedComposedPotential ring L) :=
  partialExitEntry_natBellmanSuperSolution (varPipelinedRoundStep ring P L)
    (fun _ _ => varAllDeclareStart L (by omega))
    (varPipelinedServiceStep L E)
    (varPipelinedRoundPotential ring L) (varPipelinedServicePotential L)
    (varPipelined_natBellmanSuperSolution ring P L)
    (varPipelinedService_bellman L E)
    (fun state => varPipelined_localBalance ring hm P hn L state)
    (fun state edge r hstep =>
      varPipelinedService_exit_le L E state edge r hstep)
    (fun _ _ _ => Nat.le_of_eq
      (varPipelinedServicePotential_allDeclareStart L (by omega)))

/-- The composed process has no bad terminal. -/
theorem varPipelinedComposedStep_ne_failure {n m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (L : VarGapLayout n m)
    (E : VarRoundEntryMap ring L) (hm : 0 < m) :
    ∀ state edge,
      varPipelinedComposedStep ring P L E hm state edge ≠ .failure :=
  partialExitEntryStep_ne_failure (varPipelinedRoundStep ring P L)
    (fun _ _ => varAllDeclareStart L hm) (varPipelinedServiceStep L E)

private theorem budget_eq (n m t : Nat) :
    2 * (n * m) + 2 * n * t = 2 * (n * m) + n * (2 * t) := by
  have hswap : n * (2 * t) = 2 * n * t := by ac_rfl
  rw [hswap]

private theorem ring_budget_eq (n m : Nat) :
    2 * (n * m) + 2 * n * n = 2 * n * (m + n) := by
  rw [Nat.mul_add]
  ac_rfl

/-- **The composed budget.**  From the sequential entry round the composed
potential is exactly `2 * (n * m) + 2 * n * Σ_g len g`. -/
theorem varPipelinedComposedPotential_entryRoundState {n m : Nat}
    (ring : DirectedRing m) (L : VarGapLayout n m) (hm : 0 < m) :
    varPipelinedComposedPotential ring L
        (.active (.round (varEntryRoundState ring L hm))) =
      2 * (n * m) + 2 * n * L.totalLength := by
  rw [budget_eq]
  simp only [varPipelinedComposedPotential, partialExitPotential,
    varPipelinedRoundPotential_entryRoundState ring L hm]
  omega

/-- **The composed complexity bound at variable gap lengths.** -/
theorem varPipelinedComposed_truncatedCost_le {n m : Nat}
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m) (hn : 1 < n)
    (L : VarGapLayout n m) (E : VarRoundEntryMap ring L) (T : Nat) :
    truncatedActiveCostNumerator
        (varPipelinedComposedStep ring P L E (by omega))
        (.active (.round (varEntryRoundState ring L (by omega)))) T ≤
      n ^ T * (2 * (n * m) + 2 * n * L.totalLength) := by
  have hsuper := varPipelinedComposed_natBellmanSuperSolution ring hm P hn L E
  have hcost := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (varPipelinedComposedStep ring P L E (by omega)) 1
    (varPipelinedComposedPotential ring L) hsuper
    (.active (.round (varEntryRoundState ring L (by omega)))) T
  rw [varPipelinedComposedPotential_entryRoundState ring L (by omega)] at hcost
  omega

/-- Reciprocal finite-horizon success tail at variable gap lengths. -/
theorem varPipelinedComposed_success_one_minus_inv_factor
    {n m factor : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (L : VarGapLayout n m)
    (E : VarRoundEntryMap ring L) :
    (factor - 1) *
        n ^ (factor * (2 * (n * m) + 2 * n * L.totalLength)) ≤
      factor * successCount (varPipelinedComposedStep ring P L E (by omega))
        (.active (.round (varEntryRoundState ring L (by omega))))
        (factor * (2 * (n * m) + 2 * n * L.totalLength)) := by
  have hpositive :
      0 < varPipelinedRoundPotential ring L
        (.active (varEntryRoundState ring L (by omega))) +
          (n * m + n * (2 * L.totalLength)) := by
    rw [varPipelinedRoundPotential_entryRoundState ring L (by omega)]
    have : 0 < n * m := Nat.mul_pos (by omega) (by omega)
    omega
  have htail :=
    pred_mul_pow_le_factor_mul_successCount_partialExitEntry_roundBase
      (varPipelinedRoundStep ring P L)
      (fun _ _ => varAllDeclareStart L (by omega : 0 < m))
      (varPipelinedServiceStep L E)
      (varEntryRoundState ring L (by omega))
      (varPipelinedRoundPotential ring L) (varPipelinedServicePotential L)
      (varPipelined_natBellmanSuperSolution ring P L)
      (varPipelinedService_bellman L E)
      (fun state => varPipelined_localBalance ring hm P hn L state)
      (fun state edge r hstep =>
        varPipelinedService_exit_le L E state edge r hstep)
      (fun _ _ _ => Nat.le_of_eq
        (varPipelinedServicePotential_allDeclareStart L (by omega)))
      hpositive (factor := factor)
  rw [varPipelinedRoundPotential_entryRoundState ring L (by omega)] at htail
  rw [budget_eq]
  have hshape : n * m + (n * m + n * (2 * L.totalLength)) =
      2 * (n * m) + n * (2 * L.totalLength) := by omega
  rw [hshape] at htail
  exact htail

/-! ## The placement capstone -/

/-- The pipelined process whose gaps are the placement-derived gaps of an
ordered placement. -/
noncomputable def placementPipelinedComposedStep {n m : Nat}
    (ring : DirectedRing m) (P : Placement n m)
    (hord : RootsOrdered ring P) (hm : 1 < m)
    (E : VarRoundEntryMap ring (placementLayout ring P hord hm)) :=
  varPipelinedComposedStep ring P (placementLayout ring P hord hm) E
    (by omega)

/-- Sequential entry round of the placement-derived pipelined process. -/
def placementEntryRoundState {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (hord : RootsOrdered ring P) (hm : 1 < m) :
    VarPipelinedRoundState ring (placementLayout ring P hord hm) :=
  varEntryRoundState ring (placementLayout ring P hord hm) (by omega)

/-- **Placement capstone.**  For an ordered placement the gaps tile the
physical ring (`ShortGapGapTiling.gapLen_sum_eq`), so the composed pipelined
budget is `2 * n * (m + n)`: two copies of `n * m` for the balanced ghost
round and `2 * n * n` for every carrier hop of the gaps that tile the ring. -/
theorem placementPipelinedComposed_truncatedCost_le {n m : Nat}
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m) (hn : 1 < n)
    (hord : RootsOrdered ring P)
    (E : VarRoundEntryMap ring (placementLayout ring P hord hm)) (T : Nat) :
    truncatedActiveCostNumerator
        (placementPipelinedComposedStep ring P hord hm E)
        (.active (.round (placementEntryRoundState ring P hord hm))) T ≤
      n ^ T * (2 * n * (m + n)) := by
  have hcost := varPipelinedComposed_truncatedCost_le ring hm P hn
    (placementLayout ring P hord hm) E T
  rw [placementLayout_totalLength_eq ring P hord hm, ring_budget_eq] at hcost
  exact hcost

/-- Reciprocal finite-horizon success tail at the placement capstone budget. -/
theorem placementPipelinedComposed_success_one_minus_inv_factor
    {n m factor : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (hord : RootsOrdered ring P)
    (E : VarRoundEntryMap ring (placementLayout ring P hord hm)) :
    (factor - 1) * n ^ (factor * (2 * n * (m + n))) ≤
      factor * successCount (placementPipelinedComposedStep ring P hord hm E)
        (.active (.round (placementEntryRoundState ring P hord hm)))
        (factor * (2 * n * (m + n))) := by
  have htail := varPipelinedComposed_success_one_minus_inv_factor ring hm P hn
    (placementLayout ring P hord hm) E (factor := factor)
  rw [placementLayout_totalLength_eq ring P hord hm, ring_budget_eq] at htail
  exact htail

/-- The capstone at the canonical rearm exit, where service completion rearms
every root to `Race`.  This instantiates every interface of the file at a
concrete admissible entry, so none of the statements above is vacuous. -/
theorem allRaceEntry_placementPipelinedComposed_truncatedCost_le {n m : Nat}
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m) (hn : 1 < n)
    (hord : RootsOrdered ring P) (T : Nat) :
    truncatedActiveCostNumerator
        (placementPipelinedComposedStep ring P hord hm
          (varAllRaceEntryMap ring (placementLayout ring P hord hm)
            (by omega)))
        (.active (.round (placementEntryRoundState ring P hord hm))) T ≤
      n ^ T * (2 * n * (m + n)) :=
  placementPipelinedComposed_truncatedCost_le ring hm P hn hord
    (varAllRaceEntryMap ring (placementLayout ring P hord hm) (by omega)) T

/-- Uniform gap lengths tiling the ring: the capstone budget agrees with the
fixed-length budget `2 * (n * m) * (1 + h)` of
`Leader/Wu/ShortGap/PipelinedRearm.lean`. -/
theorem placement_budget_eq_uniform_budget (n m h : Nat) (hmh : m * h = n) :
    2 * n * (m + n) = 2 * (n * m) * (1 + h) :=
  tiling_budget_eq_uniform_budget n m h hmh

#print axioms varRearmed_monotone_step
#print axioms var_exists_hops_pos_of_not_rearmed
#print axioms varPipelined_localBalance
#print axioms varPipelined_childSum
#print axioms varPipelined_natBellmanSuperSolution
#print axioms varPipelinedService_bellman
#print axioms varPipelinedComposed_natBellmanSuperSolution
#print axioms varPipelinedComposedPotential_entryRoundState
#print axioms varPipelinedComposed_truncatedCost_le
#print axioms varPipelinedComposed_success_one_minus_inv_factor
#print axioms placementPipelinedComposed_truncatedCost_le
#print axioms placementPipelinedComposed_success_one_minus_inv_factor
#print axioms allRaceEntry_placementPipelinedComposed_truncatedCost_le

end ShortGapPipelinedRearmPlacement

import Leader.L3.RequestClock
import Leader.L3.Top.Coefficient

/-!
Conditional request-stage assembly.

H1 below is the *stopped, real/audited form* of the paper's
packet-transport P.1 clock. A bare fixed-data packet clock is
NOT enough to prove this H1: a separate stopped physical
coupling is still needed upstream. H2 is not asserted here.

StageRequestMissingClock has no n >= 5 premise of its own.
Accordingly H1 explicitly includes 5 <= n; no small-n stage
theorem is silently inferred.
-/

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-! ## Exact auxiliary first-hit target for the TOP branch -/

/-- Append each actual IID scheduler edge to its chronological trace.
The physical component is never frozen or rewritten. -/
abbrev RequestStageTraceState (n : Nat) :=
  HeadlineConfiguration n × List (Fin n)

def requestStageTraceNext {n : Nat}
    (ring : DirectedRing n) :
    RequestStageTraceState n → Fin n → RequestStageTraceState n :=
  fun Z e => (headlinePhysicalNext ring Z.1 e, Z.2 ++ [e])

/-- A genuine strict completion is admissible as a *physical*
first-hit witness only with OLD frozen input and an actual
preterminal leaderless, requestless GRANT cut. These properties
are not part of the bare P.1 fixed-data transport estimate. -/
def requestStageQualifiedStrict {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : RequestStageTraceState n) : Prop :=
  ∃ (pfx : List (Fin n)) (e : Fin n),
    Z.2 = pfx ++ [e] ∧
    Z.1 = HeadlineRequest.realRequestRun ring C (pfx ++ [e]) ∧
    HeadlineDigit.StrictCompletesAt ring C s pfx e ∧
    HeadlineDigit.FrozenOnWord ring C pfx ∧
    HeadlineRequest.RequestBeforeStop ring
      (HeadlineRequest.realRequestRun ring C pfx)

/-- The STOPPED transport target is either an earlier real
request-ready/generated hit or a newly completed, causally
authenticated strict comparison on the last actual edge. -/
def requestStageTopStop {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : RequestStageTraceState n) : Prop :=
  HeadlineRequest.requestStoppedTarget ring Z.1 ∨
    requestStageQualifiedStrict ring C s Z

/-- H1, packet-transport Lemma P.1 plus its needed STOPPED
physical realization. The numerical upper bound is n*h(r).
It is deliberately a named hypothesis, NOT a theorem.

This is stronger than the bare fixed-word P.1 bound: the
real/ghost stopped coupling that establishes it must be proved
separately in the TOP-clock implementation. No claim about
dynamic inputs completing a strict comparison is used. -/
def TopStrictClock {n : Nat} (ring : DirectedRing n) : Prop :=
  5 ≤ n ∧
  ∀ (C : HeadlineConfiguration n) (s : Fin n),
    headlineGrantReady ring C →
    (∀ i : Fin n, (C i).l = false) →
    (∀ i : Fin n, (C i).req = false) →
    HeadlineDigit.BadCompletePair C s →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (requestStageTraceNext ring)
      (requestStageTopStop ring C s)
      (C, [])
      ((topCoefficientWidthH
        (compileAdvice (ceilLogTwo n)).t * n : Nat) : Rat)

/-- H2, certificate.tex A.3: the OLD-input real terminal
report bridge. Exactly the existing open proposition, without
a last-service public-freeze assumption. -/
def StrictReportBridgeOldAll {n : Nat}
    (ring : DirectedRing n) : Prop :=
  HeadlineDigit.StrictReportBridgeOld ring

/-! ## Physical end-of-word and TOP report projection -/

/-- The word recorder agrees with the actual physical process
after the final selected edge. -/
private theorem requestStageRunAppend {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (pfx : List (Fin n)) (e : Fin n) :
    HeadlineRequest.realRequestRun ring C (pfx ++ [e]) =
      headlinePhysicalNext ring
        (HeadlineRequest.realRequestRun ring C pfx) e := by
  induction pfx generalizing C with
  | nil =>
      rfl
  | cons x xs ih =>
      exact ih (headlinePhysicalNext ring C x)

/-- Every *qualified* strict terminal is a physical request-ready
cut, using H2, OLD GRANT survival and the purification step. -/
private theorem requestStageQualifiedStrictHits {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hbridge : StrictReportBridgeOldAll ring)
    (Z : RequestStageTraceState n)
    (hstrict : requestStageQualifiedStrict ring C s Z) :
    HeadlineRequest.requestStoppedTarget ring Z.1 := by
  obtain ⟨pfx, e, hword, hreal, hcomplete, hfrozen, hbefore⟩ :=
    hstrict
  have htop : HeadlineDigit.TopRejectAt ring
      (HeadlineRequest.realRequestRun ring C pfx) e :=
    hbridge C s pfx e hbad hfrozen hcomplete
  have hready := HeadlineDigit.topRejectMakesRequestReady
    ring hn (HeadlineRequest.realRequestRun ring C pfx) e
    hbefore.purified hbefore.rootless hbefore.noRequest
    hbefore.grant htop
  have hfinal :
      Z.1 = headlinePhysicalNext ring
        (HeadlineRequest.realRequestRun ring C pfx) e := by
    calc
      Z.1 = HeadlineRequest.realRequestRun ring C (pfx ++ [e]) :=
        hreal
      _ = headlinePhysicalNext ring
            (HeadlineRequest.realRequestRun ring C pfx) e :=
        requestStageRunAppend ring C pfx e
  change headlineRequestReady ring Z.1 ∨
    headlineGeneratedTarget ring Z.1
  rw [hfinal]
  exact Or.inl hready

/-- The stopped TOP auxiliary target is contained in the
REAL simultaneous request/grant-or-generated target. -/
private theorem requestStageTopStopPhysical {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hbridge : StrictReportBridgeOldAll ring) :
    ∀ Z : RequestStageTraceState n,
      requestStageTopStop ring C s Z →
      HeadlineRequest.requestStoppedTarget ring Z.1 := by
  intro Z hz
  rcases hz with htarget | hstrict
  · exact htarget
  · exact requestStageQualifiedStrictHits
      ring hn C s hbad hbridge Z hstrict

/-! ## Exact finite-horizon first-hit composition -/

/-- Finite-horizon physical cost is bounded by the TOP trace
cost, using only a ghost step with the exact real projection. -/
theorem requestStageTopCostOfClock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hbridge : StrictReportBridgeOldAll ring)
    (T : Nat) :
    costNumerator (headlinePhysicalNext ring)
        (HeadlineRequest.requestStoppedTarget ring) C T ≤
      costNumerator (requestStageTraceNext ring)
        (requestStageTopStop ring C s) (C, []) T := by
  exact Prob.costNumerator_ghost_target_le
    (headlinePhysicalNext ring)
    (requestStageTraceNext ring)
    (by intro Z e; rfl)
    (HeadlineRequest.requestStoppedTarget ring)
    (requestStageTopStop ring C s)
    (requestStageTopStopPhysical ring hn C s hbad hbridge)
    (C, []) T

/-- Absorb the paper's optional initial-debt mean n/2 into
one n^2 of checker slack, without rational division. The
inequality is doubled so the full argument stays in Nat. -/
theorem requestStageDebtSlack (n rate : Nat)
    (hn : 5 ≤ n) :
    2 * (rate * n ^ 2) + n ≤
      2 * ((rate + 1) * n ^ 2) := by
  have hnle : n ≤ n ^ 2 := by
    have hm := Nat.mul_le_mul_left n (by omega : 1 ≤ n)
    simpa only [Nat.mul_one, Nat.pow_two] using hm
  have heq :
      2 * ((rate + 1) * n ^ 2) =
        2 * (rate * n ^ 2) + 2 * n ^ 2 := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_add]
  rw [heq]
  omega

/-- TOP cost fits the selected checker ledger. The extra +1 is
retained to match the exact StageRequestMissingClock budget. -/
theorem requestStageTopExpectedOfClock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hg : headlineGrantReady ring C)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hr : ∀ i : Fin n, (C i).req = false)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hclock : TopStrictClock ring)
    (hbridge : StrictReportBridgeOldAll ring) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring)
      (HeadlineRequest.requestStoppedTarget ring) C
      ((((headlineCheckerRate n + 1) * n ^ 2 : Nat)) : Rat) := by
  have hstrict := hclock.2 C s hg hl hr hbad
  have hquota := topCoefficientScaledBound n hn
  have hbudget :
      topCoefficientWidthH
          (compileAdvice (ceilLogTwo n)).t * n ≤
        (headlineCheckerRate n + 1) * n ^ 2 := by
    calc
      topCoefficientWidthH
          (compileAdvice (ceilLogTwo n)).t * n ≤
          headlineCheckerRate n * n ^ 2 := hquota
      _ ≤ (headlineCheckerRate n + 1) * n ^ 2 :=
        Nat.mul_le_mul_right (n ^ 2) (by omega)
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (headlinePhysicalNext ring)
    (HeadlineRequest.requestStoppedTarget ring)
    (by omega : 0 < n) C
    ((headlineCheckerRate n + 1) * n ^ 2)).2
  intro T
  have htopcost := requestStageTopCostOfClock
    ring hn C s hbad hbridge T
  have hclockcost :
      costNumerator (requestStageTraceNext ring)
        (requestStageTopStop ring C s) (C, []) T ≤
      n ^ T *
        (topCoefficientWidthH
          (compileAdvice (ceilLogTwo n)).t * n) :=
    (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (requestStageTraceNext ring)
      (requestStageTopStop ring C s)
      (by omega : 0 < n) (C, [])
      (topCoefficientWidthH
        (compileAdvice (ceilLogTwo n)).t * n)).1 hstrict T
  calc
    costNumerator (headlinePhysicalNext ring)
        (HeadlineRequest.requestStoppedTarget ring) C T ≤
      costNumerator (requestStageTraceNext ring)
        (requestStageTopStop ring C s) (C, []) T := htopcost
    _ ≤ n ^ T *
        (topCoefficientWidthH
          (compileAdvice (ceilLogTwo n)).t * n) := hclockcost
    _ ≤ n ^ T *
        ((headlineCheckerRate n + 1) * n ^ 2) :=
      Nat.mul_le_mul_left (n ^ T) hbudget

/-- Assemble the all-width static failure selector, RAW
clock, stopped strict TOP clock and OLD bridge. The size premise
lives in H1 because StageRequestMissingClock is unguarded. -/
theorem stageRequestMissingClock_of_top_and_bridge {n : Nat}
    (ring : DirectedRing n)
    (hclock : TopStrictClock ring)
    (hbridge : StrictReportBridgeOldAll ring) :
    StageRequestMissingClock ring := by
  intro C hg hl hr
  have hn : 5 ≤ n := hclock.1
  rcases requestRawOrTopFailure C hn hl with
    ⟨s, hraw⟩ | ⟨s, hbad⟩
  · change UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring)
      (HeadlineRequest.requestStoppedTarget ring) C
      ((((headlineCheckerRate n + 1) * n ^ 2 : Nat)) : Rat)
    exact HeadlineRequest.requestRawExpected
      ring hn C s hg hl hr hraw
  · change UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring)
      (HeadlineRequest.requestStoppedTarget ring) C
      ((((headlineCheckerRate n + 1) * n ^ 2 : Nat)) : Rat)
    exact requestStageTopExpectedOfClock
      ring hn C s hg hl hr hbad hclock hbridge

/-! ## Explicit additional P.1-to-H1 obligation (not assumed) -/

/-- H3: the physical frozen-prefix implication needed to turn
the *bare fixed-data* P.1 transport clock into the stopped H1.
This is a separately named future coupling fact, not asserted
from requestQuietPhysicalAll without a word-level induction.

The full H3 packet-to-stopped-cost transfer also needs the
fixed-data shadow process and receipt correspondence; those
are not constructed by these two imported modules. -/
def TopStrictNoHitFrozen {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ (C : HeadlineConfiguration n)
    (hg : headlineGrantReady ring C)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hr : ∀ i : Fin n, (C i).req = false)
    (word : List (Fin n)),
      ¬ HeadlineRequest.realRequestHitBy ring C word →
      HeadlineDigit.FrozenOnWord ring C word

end L3


/-!
Stopped H3 with a proof-only fixed-public TOP shadow.

The quantitative P.1 clock is stated separately, and the
section does not claim that the underlying packet-transport
inequality has already been formalized.
-/

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-! ## The real request-free prefix freezes all checker public data -/

private theorem topRealRunAppend {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (word : List (Fin n)) (e : Fin n) :
    HeadlineRequest.realRequestRun ring C (word ++ [e]) =
      headlinePhysicalNext ring
        (HeadlineRequest.realRequestRun ring C word) e := by
  induction word generalizing C with
  | nil =>
      rfl
  | cons a tail ih =>
      exact ih (headlinePhysicalNext ring C a)

private theorem topNoHitPrefix {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (before after : List (Fin n))
    (h : ¬ HeadlineRequest.realRequestHitBy ring C
      (before ++ after)) :
    ¬ HeadlineRequest.realRequestHitBy ring C before := by
  intro hh
  obtain ⟨a, b, hab, htarget⟩ := hh
  apply h
  refine ⟨a, b ++ after, ?_, htarget⟩
  calc
    before ++ after = (a ++ b) ++ after := by rw [hab]
    _ = a ++ (b ++ after) := List.append_assoc _ _ _

/-- Simultaneous real pre-stop control and public-data induction.
The Q packet/carry scratch remains arbitrary throughout. -/
private theorem topNoHitBeforePublic {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n)
    (hg : headlineGrantReady ring C)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hr : ∀ i : Fin n, (C i).req = false) :
    ∀ word : List (Fin n),
      ¬ HeadlineRequest.realRequestHitBy ring C word →
      HeadlineRequest.RequestBeforeStop ring
        (HeadlineRequest.realRequestRun ring C word) ∧
      HeadlineDigit.SameCheckerPublic C
        (HeadlineRequest.realRequestRun ring C word) := by
  have hstart := HeadlineRequest.grantAtLeaderlessEntrance ring C hg hl
  have hbase : HeadlineRequest.RequestBeforeStop ring C :=
    ⟨hstart.1, hstart.2, hl, hr⟩
  have hkey : ∀ rev : List (Fin n),
      ¬ HeadlineRequest.realRequestHitBy ring C rev.reverse →
      HeadlineRequest.RequestBeforeStop ring
        (HeadlineRequest.realRequestRun ring C rev.reverse) ∧
      HeadlineDigit.SameCheckerPublic C
        (HeadlineRequest.realRequestRun ring C rev.reverse) := by
    intro rev
    induction rev with
    | nil =>
        intro _
        exact ⟨hbase, fun i => ⟨rfl, rfl, rfl, rfl⟩⟩
    | cons e rev ih =>
        rw [List.reverse_cons]
        intro hno
        have hpre : ¬ HeadlineRequest.realRequestHitBy ring C rev.reverse :=
          topNoHitPrefix ring C rev.reverse [e] hno
        obtain ⟨hbefore, hpublic⟩ := ih hpre
        have hnoTarget :
            ¬ HeadlineRequest.requestStoppedTarget ring
              (headlinePhysicalNext ring
                (HeadlineRequest.realRequestRun ring C rev.reverse) e) := by
          intro hh
          have hlast :
              HeadlineRequest.requestStoppedTarget ring
                (HeadlineRequest.realRequestRun ring C
                  (rev.reverse ++ [e])) := by
            rw [topRealRunAppend ring C rev.reverse e]
            exact hh
          exact hno (HeadlineRequest.realRequestHitBy_of_end
            ring C (rev.reverse ++ [e]) hlast)
        have hnext := HeadlineRequest.requestBeforeStopStep
          ring hn (HeadlineRequest.realRequestRun ring C rev.reverse)
          e hbefore hnoTarget
        have hquiet := requestQuietPhysicalAll
          ring (by omega : 2 ≤ n)
          (HeadlineRequest.realRequestRun ring C rev.reverse)
          e hbefore.rootless hbefore.noRequest hnext.noRequest
        have hnewPublic :
            HeadlineDigit.SameCheckerPublic C
              (headlinePhysicalNext ring
                (HeadlineRequest.realRequestRun ring C rev.reverse) e) := by
          intro i
          have hleader :
              ((headlinePhysicalNext ring
                (HeadlineRequest.realRequestRun ring C rev.reverse) e) i).l =
                ((HeadlineRequest.realRequestRun ring C rev.reverse) i).l :=
            (hnext.rootless i).trans (hbefore.rootless i).symm
          have hold := hpublic i
          have hnow := hquiet.1 i
          exact ⟨hleader.trans hold.1,
            hnow.1.trans hold.2.1,
            hnow.2.1.trans hold.2.2.1,
            hnow.2.2.trans hold.2.2.2⟩
        rw [topRealRunAppend ring C rev.reverse e]
        exact ⟨hnext, hnewPublic⟩
  intro word
  have h := hkey word.reverse
  rw [List.reverse_reverse] at h
  exact h

/-- Requested H3(a): all public leader, marker, bit and digit
coordinates agree with the entrance cut at every no-hit prefix. -/
theorem topStrictNoHitFrozen_proved {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) :
    TopStrictNoHitFrozen ring := by
  intro C hg hl hr word hno before after hsplit
  have hfull :
      ¬ HeadlineRequest.realRequestHitBy ring C (before ++ after) := by
    rw [← hsplit]
    exact hno
  have hprefix := topNoHitPrefix ring C before after hfull
  exact (topNoHitBeforePublic ring hn C hg hl hr
    before hprefix).2

/-! ## Fixed-public TOP replay, evolving every OLD packet record -/

/-- A proof-only restoration of exactly four checker public fields,
after performing a genuine full physical step. -/
def topFixedPublicAgent {c : Compiled}
    (fixed evolved : Agent c) : Agent c :=
  { evolved with
      l := fixed.l
      u := fixed.u
      beta := fixed.beta
      d := fixed.d }

def topFixedPublicNext {n : Nat}
    (ring : DirectedRing n) (C D : HeadlineConfiguration n)
    (e : Fin n) : HeadlineConfiguration n :=
  fun i =>
    topFixedPublicAgent (C i) (headlinePhysicalNext ring D e i)

/-- Independent original OLD DigitAudit, synchronized with each
shadow physical edge. The trace is an observed list of Fin n hits. -/
abbrev TopFixedTraceState (n : Nat) :=
  (HeadlineConfiguration n ×
    DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      List (Fin n)

def topFixedTraceNext {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n) :
    TopFixedTraceState n → Fin n → TopFixedTraceState n :=
  fun Z e =>
    ((topFixedPublicNext ring C Z.1.1 e,
      digitAuditStep ring (piD Z.1.1) Z.1.2 e),
     Z.2 ++ [e])

def topFixedTraceRun {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (word : List (Fin n)) : TopFixedTraceState n :=
  word.foldl (topFixedTraceNext ring C)
    ((C, digitAuditInitial (piD C)), [])

/-- A real FIFO sample/export/use strict comparison terminal on
the final shadow edge, rather than an arbitrary old error bit. -/
def topFixedStrictStop {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) : Prop :=
  ∃ (pfx : List (Fin n)) (e : Fin n)
      (terminal : DigitTerminal
        (compileAdvice (ceilLogTwo n)) n),
    Z.2 = pfx ++ [e] ∧
    HeadlineDigit.FirstStrictCyclicTerminal ring C s
      Z.1.2 terminal ∧
    terminal.time = pfx.length + 1 ∧
    terminal.source = e ∧
    terminal.destination = ring.rightNeighbor e

/-- Fixed-data Lemma P.1 in an exact shadow process. This Prop is
the INDEPENDENT missing quantitative theorem; it is NOT H1.
Public l/u/beta/d are frozen, but every comparison packet,
carry, dirty state and audit receipt follows actual OLD rows. -/
def TopFixedClock {n : Nat}
    (ring : DirectedRing n) : Prop :=
  5 ≤ n ∧
  ∀ (C : HeadlineConfiguration n) (s : Fin n),
    headlineGrantReady ring C →
    (∀ i : Fin n, (C i).l = false) →
    (∀ i : Fin n, (C i).req = false) →
    HeadlineDigit.BadCompletePair C s →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (topFixedTraceNext ring C)
      (topFixedStrictStop ring C s)
      ((C, digitAuditInitial (piD C)), [])
      ((topCoefficientWidthH
        (compileAdvice (ceilLogTwo n)).t * n : Nat) : Rat)

end L3


/-!
Prefix-snoc and frozen/actual trace synchronization.
-/

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

private theorem topFixedFoldAppend {α β : Type}
    (step : β → α → β) (start : β) (word : List α)
    (e : α) :
    (word ++ [e]).foldl step start =
      step (word.foldl step start) e := by
  induction word generalizing start with
  | nil =>
      rfl
  | cons x xs ih =>
      exact ih (step start x)

private theorem topFixedTraceRunAppend {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (word : List (Fin n)) (e : Fin n) :
    topFixedTraceRun ring C (word ++ [e]) =
      topFixedTraceNext ring C (topFixedTraceRun ring C word) e := by
  exact topFixedFoldAppend (topFixedTraceNext ring C)
    ((C, digitAuditInitial (piD C)), []) word e

/-- The four restored fields equal the real final fields on a
quiet service, so the entire physical agent is identical. -/
private theorem topFixedPublicNextEq {n : Nat}
    (ring : DirectedRing n) (C D : HeadlineConfiguration n)
    (e : Fin n)
    (hpub : HeadlineDigit.SameCheckerPublic C
      (headlinePhysicalNext ring D e)) :
    topFixedPublicNext ring C D e =
      headlinePhysicalNext ring D e := by
  funext i
  obtain ⟨hl, hu, hb, hd⟩ := hpub i
  change
    ({ (headlinePhysicalNext ring D e i) with
        l := (C i).l
        u := (C i).u
        beta := (C i).beta
        d := (C i).d } :
      Agent (compileAdvice (ceilLogTwo n))) =
        headlinePhysicalNext ring D e i
  rw [← hl, ← hu, ← hb, ← hd]
  rfl

/-! A chronological prefix of an appended word either ends
before its last service or is the entire appended word. -/
private theorem topListSnocPrefix {α : Type} :
    ∀ (word before after : List α) (e : α),
      word ++ [e] = before ++ after →
      (∃ rest : List α, word = before ++ rest) ∨
      (before = word ++ [e] ∧ after = []) := by
  intro word
  induction word with
  | nil =>
      intro before after e heq
      cases before with
      | nil =>
          exact Or.inl ⟨[], rfl⟩
      | cons b bs =>
          have hv := List.cons.inj heq
          have hnil : bs ++ after = ([] : List α) := hv.2.symm
          have hparts := List.append_eq_nil_iff.mp hnil
          rw [hparts.1, hparts.2] at heq
          have he : e = b := (List.cons.inj heq).1
          cases he
          exact Or.inr ⟨by rw [hparts.1]; rfl, hparts.2⟩
  | cons a rest ih =>
      intro before after e heq
      cases before with
      | nil =>
          exact Or.inl ⟨a :: rest, rfl⟩
      | cons b bs =>
          have hv := List.cons.inj heq
          rcases ih bs after e hv.2 with ⟨tail, ht⟩ | ⟨hb, ha⟩
          · refine Or.inl ⟨tail, ?_⟩
            rw [hv.1, ht, List.cons_append]
          · refine Or.inr ⟨?_, ha⟩
            rw [← hv.1, hb, List.cons_append]

private theorem topNoHitSnoc {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (word : List (Fin n)) (e : Fin n)
    (hpre : ¬ HeadlineRequest.realRequestHitBy ring C word)
    (hfinal : ¬ HeadlineRequest.requestStoppedTarget ring
      (HeadlineRequest.realRequestRun ring C (word ++ [e]))) :
    ¬ HeadlineRequest.realRequestHitBy ring C (word ++ [e]) := by
  intro hh
  obtain ⟨before, after, hword, htarget⟩ := hh
  rcases topListSnocPrefix word before after e hword with
    ⟨tail, hprefix⟩ | ⟨hfull, _⟩
  · exact hpre ⟨before, tail, hprefix, htarget⟩
  · apply hfinal
    rw [hfull] at htarget
    exact htarget

private theorem topNoHitEmpty {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (h : ¬ HeadlineRequest.requestStoppedTarget ring C) :
    ¬ HeadlineRequest.realRequestHitBy ring C [] := by
  intro hh
  obtain ⟨before, after, hword, htarget⟩ := hh
  cases before with
  | nil =>
      exact h htarget
  | cons e rest =>
      cases hword

/-- The fixed-public shadow agrees with both the full physical
run and the proof-only real digit audit at every no-hit prefix.
No comparison scratch coordinate is initialized anew. -/
private theorem topFixedTraceSynced {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n)
    (hg : headlineGrantReady ring C)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hr : ∀ i : Fin n, (C i).req = false) :
    ∀ word : List (Fin n),
      ¬ HeadlineRequest.realRequestHitBy ring C word →
      (topFixedTraceRun ring C word).1.1 =
        HeadlineRequest.realRequestRun ring C word ∧
      (topFixedTraceRun ring C word).1.2 =
        (HeadlineDigit.auditedRealRun ring C word).2 ∧
      (topFixedTraceRun ring C word).2 = word := by
  have hkey : ∀ rev : List (Fin n),
      ¬ HeadlineRequest.realRequestHitBy ring C rev.reverse →
      (topFixedTraceRun ring C rev.reverse).1.1 =
        HeadlineRequest.realRequestRun ring C rev.reverse ∧
      (topFixedTraceRun ring C rev.reverse).1.2 =
        (HeadlineDigit.auditedRealRun ring C rev.reverse).2 ∧
      (topFixedTraceRun ring C rev.reverse).2 =
        rev.reverse := by
    intro rev
    induction rev with
    | nil =>
        intro _
        exact ⟨rfl, rfl, rfl⟩
    | cons e rev ih =>
        rw [List.reverse_cons]
        intro hno
        have hpre : ¬ HeadlineRequest.realRequestHitBy ring C rev.reverse :=
          topNoHitPrefix ring C rev.reverse [e] hno
        obtain ⟨hphys, haudit, hword⟩ := ih hpre
        have hnow := (topNoHitBeforePublic ring hn C hg hl hr
          (rev.reverse ++ [e]) hno).2
        have hafter :
            HeadlineDigit.SameCheckerPublic C
              (headlinePhysicalNext ring
                (HeadlineRequest.realRequestRun ring C rev.reverse) e) := by
          rw [← topRealRunAppend ring C rev.reverse e]
          exact hnow
        have hfreeze := topFixedPublicNextEq ring C
          (HeadlineRequest.realRequestRun ring C rev.reverse)
          e hafter
        have hghost :
            digitAuditStep ring
                (piD (HeadlineRequest.realRequestRun ring C rev.reverse))
                (HeadlineDigit.auditedRealRun ring C rev.reverse).2 e =
              (HeadlineDigit.auditedRealRun ring C
                (rev.reverse ++ [e])).2 := by
          rw [HeadlineDigit.checkerAuditedRunAppendOne ring C rev.reverse e,
            HeadlineDigit.checkerAuditedRunPhysical ring C rev.reverse]
        rw [topFixedTraceRunAppend ring C rev.reverse e]
        change
          topFixedPublicNext ring C
              (topFixedTraceRun ring C rev.reverse).1.1 e =
                HeadlineRequest.realRequestRun ring C
                  (rev.reverse ++ [e]) ∧
          digitAuditStep ring
              (piD (topFixedTraceRun ring C rev.reverse).1.1)
              (topFixedTraceRun ring C rev.reverse).1.2 e =
                (HeadlineDigit.auditedRealRun ring C
                  (rev.reverse ++ [e])).2 ∧
          (topFixedTraceRun ring C rev.reverse).2 ++ [e] =
            rev.reverse ++ [e]
        refine ⟨?_, ?_, ?_⟩
        · rw [hphys, hfreeze, topRealRunAppend]
        · rw [hphys, haudit]
          exact hghost
        · rw [hword]
  intro word
  have h := hkey word.reverse
  rw [List.reverse_reverse] at h
  exact h

end L3


/-!
H3 cost transfer. StrictReportBridgeOldAll
remains the independent downstream H2 obligation.
-/

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- A relation between two concrete paths on one SAME IID edge
word, stopped before the first physical real request hit.
Neither side has an independently conditioned edge tape. -/
def TopFixedRelated {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : RequestStageTraceState n)
    (F : TopFixedTraceState n) : Prop :=
  ∃ word : List (Fin n),
    Z = (HeadlineRequest.realRequestRun ring C word, word) ∧
    F = topFixedTraceRun ring C word ∧
    ¬ HeadlineRequest.realRequestHitBy ring C word

private theorem topFixedRelatedStep {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : RequestStageTraceState n)
    (F : TopFixedTraceState n)
    (hrel : TopFixedRelated ring C Z F)
    (e : Fin n)
    (hnot :
      ¬ requestStageTopStop ring C s
        (requestStageTraceNext ring Z e)) :
    TopFixedRelated ring C
      (requestStageTraceNext ring Z e)
      (topFixedTraceNext ring C F e) := by
  obtain ⟨word, hZ, hF, hno⟩ := hrel
  subst Z
  subst F
  have hlast :
      ¬ HeadlineRequest.requestStoppedTarget ring
        (HeadlineRequest.realRequestRun ring C (word ++ [e])) := by
    intro hh
    apply hnot
    apply Or.inl
    change HeadlineRequest.requestStoppedTarget ring
      (headlinePhysicalNext ring
        (HeadlineRequest.realRequestRun ring C word) e)
    rw [← topRealRunAppend ring C word e]
    exact hh
  have hnoNew := topNoHitSnoc ring C word e hno hlast
  refine ⟨word ++ [e], ?_, ?_, hnoNew⟩
  · change
      (headlinePhysicalNext ring
        (HeadlineRequest.realRequestRun ring C word) e,
        word ++ [e]) =
      (HeadlineRequest.realRequestRun ring C (word ++ [e]),
        word ++ [e])
    rw [topRealRunAppend]
  · exact (topFixedTraceRunAppend ring C word e).symm

/-- On a good coupled cut, a fixed-data strict terminal on the
last edge is the actual qualified strict completion in H1.
The preterminal cut is still RequestBeforeStop, and ONLY the
strict preceding word, not the final TOP service, is frozen. -/
private theorem topFixedRelatedStrict {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hg : headlineGrantReady ring C)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hr : ∀ i : Fin n, (C i).req = false)
    (Z : RequestStageTraceState n)
    (F : TopFixedTraceState n)
    (hrel : TopFixedRelated ring C Z F)
    (hstrict : topFixedStrictStop ring C s F) :
    requestStageTopStop ring C s Z := by
  obtain ⟨word, hZ, hF, hno⟩ := hrel
  obtain ⟨pfx, e, terminal, hwordF, hfirst, htime,
    hsource, hdest⟩ := hstrict
  have hsync := topFixedTraceSynced ring hn C hg hl hr word hno
  have hword : word = pfx ++ [e] := by
    rw [hF] at hwordF
    exact (hsync.2.2).symm.trans hwordF
  have hnoFull :
      ¬ HeadlineRequest.realRequestHitBy ring C (pfx ++ [e]) := by
    rw [← hword]
    exact hno
  have hnoBefore := topNoHitPrefix ring C pfx [e] hnoFull
  have hbefore := (topNoHitBeforePublic ring hn C hg hl hr
    pfx hnoBefore).1
  have hfrozen := topStrictNoHitFrozen_proved ring hn
    C hg hl hr pfx hnoBefore
  have haudit :
      F.1.2 =
        (HeadlineDigit.auditedRealRun ring C (pfx ++ [e])).2 := by
    rw [hF, hword]
    exact (topFixedTraceSynced ring hn C hg hl hr
      (pfx ++ [e]) hnoFull).2.1
  have hrealStrict :
      HeadlineDigit.StrictCompletesAt ring C s pfx e := by
    refine ⟨terminal, ?_, htime, hsource, hdest⟩
    rw [← haudit]
    exact hfirst
  have htrace : Z.2 = pfx ++ [e] := by
    rw [hZ, hword]
  have hphysical :
      Z.1 = HeadlineRequest.realRequestRun ring C (pfx ++ [e]) := by
    rw [hZ, hword]
  exact Or.inr
    ⟨pfx, e, htrace, hphysical, hrealStrict, hfrozen, hbefore⟩

/-- Finite-horizon Bellman comparison, stopped at whichever
real target occurs first. Before then the coupled shadow is
exactly related on the next actual selected physical edge.
No independence or conditioning on a future event is used. -/
private theorem topStoppedCostSimulation
    {S U : Type} {n : Nat}
    (realNext : S → Fin n → S)
    (fixedNext : U → Fin n → U)
    (P : S → Prop) (Q : U → Prop)
    (Related : S → U → Prop)
    (hterminal : ∀ x y, Related x y → Q y → P x)
    (hstep : ∀ x y, Related x y → ¬ P x →
      ∀ e : Fin n, ¬ P (realNext x e) →
        Related (realNext x e) (fixedNext y e)) :
    ∀ (x : S) (y : U), Related x y →
      ∀ T : Nat,
      costNumerator realNext P x T ≤
        costNumerator fixedNext Q y T := by
  classical
  have hkey : ∀ T : Nat, ∀ (x : S) (y : U),
      Related x y →
      costNumerator realNext P x T ≤
        costNumerator fixedNext Q y T := by
    intro T
    induction T with
    | zero =>
        intro x y _
        simp only [costNumerator_zero, Nat.le_refl]
    | succ T ih =>
        intro x y hrel
        by_cases hp : P x
        · rw [costNumerator_terminal realNext P x hp (T + 1)]
          exact Nat.zero_le _
        · have hq : ¬ Q y := by
            intro h
            exact hp (hterminal x y hrel h)
          rw [costNumerator_succ realNext P x hp T,
            costNumerator_succ fixedNext Q y hq T]
          have hs := ofFn_sum_le
            (fun e : Fin n =>
              costNumerator realNext P (realNext x e) T)
            (fun e : Fin n =>
              costNumerator fixedNext Q (fixedNext y e) T)
            (fun e => by
              by_cases hnext : P (realNext x e)
              · rw [costNumerator_terminal realNext P
                  (realNext x e) hnext T]
                exact Nat.zero_le _
              · exact ih (realNext x e) (fixedNext y e)
                  (hstep x y hrel hp e hnext))
          exact Nat.add_le_add_left hs (n ^ (T + 1))
  intro x y hrel T
  exact hkey T x y hrel

/-- H3: the fixed-data P.1 clock gives the genuinely stopped
request-stage H1 with the same n*h(r) budget, via word-level
prefix freezing and the exact OLD digit-audit receipts.
No H2 false-report bridge is imported at this stage. -/
theorem topStrictClock_of_fixed {n : Nat}
    (ring : DirectedRing n)
    (hfixed : TopFixedClock ring) :
    TopStrictClock ring := by
  refine ⟨hfixed.1, ?_⟩
  intro C s hg hl hr hbad
  have hn : 5 ≤ n := hfixed.1
  have hpositive : 0 < n := by omega
  classical
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (requestStageTraceNext ring)
    (requestStageTopStop ring C s)
    hpositive (C, [])
    (topCoefficientWidthH
      (compileAdvice (ceilLogTwo n)).t * n)).2
  intro T
  by_cases hstart : requestStageTopStop ring C s (C, [])
  · rw [costNumerator_terminal
      (requestStageTraceNext ring)
      (requestStageTopStop ring C s)
      (C, []) hstart T]
    exact Nat.zero_le _
  · have hphysical :
        ¬ HeadlineRequest.requestStoppedTarget ring C := by
      intro hh
      exact hstart (Or.inl hh)
    have hrelated :
        TopFixedRelated ring C (C, [])
          ((C, digitAuditInitial (piD C)), []) := by
      exact ⟨[], rfl, rfl, topNoHitEmpty ring C hphysical⟩
    have hdom := topStoppedCostSimulation
      (requestStageTraceNext ring)
      (topFixedTraceNext ring C)
      (requestStageTopStop ring C s)
      (topFixedStrictStop ring C s)
      (TopFixedRelated ring C)
      (topFixedRelatedStrict ring hn C s hg hl hr)
      (fun Z F hrel _ e hnot =>
        topFixedRelatedStep ring C s Z F hrel e hnot)
      (C, []) ((C, digitAuditInitial (piD C)), [])
      hrelated T
    have hclock := hfixed.2 C s hg hl hr hbad
    have hcost :=
      (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
        (topFixedTraceNext ring C)
        (topFixedStrictStop ring C s)
        hpositive
        ((C, digitAuditInitial (piD C)), [])
        (topCoefficientWidthH
          (compileAdvice (ceilLogTwo n)).t * n)).1 hclock T
    exact Nat.le_trans hdom hcost

end L3

namespace L3

/-- The checker stage now waits only on the fixed-data TOP clock
(packet-transport Lemma P.1): the OLD-input report bridge H2 is
`HeadlineDigit.strictReportBridgeOld_proved`, and H3 turns the
fixed-data clock into the stopped one. -/
theorem stageRequestMissingClock_of_fixedTop {n : Nat}
    (ring : DirectedRing n)
    (hfixed : TopFixedClock ring) :
    StageRequestMissingClock ring :=
  stageRequestMissingClock_of_top_and_bridge ring
    (topStrictClock_of_fixed ring hfixed)
    (HeadlineDigit.strictReportBridgeOld_proved ring)

end L3

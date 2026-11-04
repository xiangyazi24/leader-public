import Leader.L3.Protocol
import Leader.L3.Certificate
import Leader.L3.ProbStages
import Leader.L3.ProbRenewal

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
# Fresh-scan substrate

No replacement physical transition is introduced.

The full paper bound is NOT asserted here: the uniform clearing
and stopped-retry cost theorem still requires a separate proof.
-/

/-! ## Literal R1/R0 rows on actual Agent pairs -/

/-- Every outgoing raw service clears its source token and kick. -/
theorem raw_source_retires (c : Compiled)
    (x y : Agent c) (post : PostE) :
    (rawD1Step c x y post).tokX = none ∧
    (rawD1Step c x y post).kickX = false := by
  cases hx : x.rawTok with
  | none =>
      cases hy : y.rawTok with
      | none =>
          cases hk : y.rawKick <;>
            simp [rawD1Step, hx, hy, hk]
      | some r =>
          simp [rawD1Step, hx, hy]
  | some r =>
      cases hy : y.rawTok with
      | none =>
          by_cases hj : r.j < c.t <;>
            simp [rawD1Step, hx, hy, hj]
      | some v =>
          simp [rawD1Step, hx, hy]

/-- R0a: an occupied target wins a collision. -/
theorem raw_collision_keeps_resident (c : Compiled)
    (x y : Agent c) (post : PostE)
    (incoming resident : RawTok c.t) :
    (rawD1Step c
      {x with rawTok := some incoming}
      {y with rawTok := some resident} post).tokY =
        some resident ∧
    (rawD1Step c
      {x with rawTok := some incoming}
      {y with rawTok := some resident} post).row = "R0a" :=
  ⟨rfl, rfl⟩

/-- R1b: the first empty/empty edge hit sets the kick. -/
theorem raw_arm_row (c : Compiled)
    (x y : Agent c) (post : PostE) :
    (rawD1Step c
      {x with rawTok := none}
      {y with rawTok := none, rawKick := false} post).row =
        "R1b" := by
  rfl

/-- R1c: the next edge hit launches a new scanner. -/
theorem raw_launch_row (c : Compiled)
    (x y : Agent c) (post : PostE) :
    (rawD1Step c
      {x with rawTok := none}
      {y with rawTok := none, rawKick := true} post).row =
        "R1c" := by
  rfl

/-- The literal launch token is computed from OLD responder data. -/
theorem raw_launch_token (c : Compiled)
    (x y : Agent c) (post : PostE) (ht : 0 < c.t) :
    (rawD1Step c
      {x with rawTok := none}
      {y with rawTok := none, rawKick := true} post).tokY =
      some { jm1 := ⟨0, ht⟩
             z := y.u
             p := c.taps 0 && y.u
             a := y.u
             h := post.eY.l
             m := false } := by
  simp [rawD1Step, ht]

/-- Intermediate R0b does not yet produce a rejection. -/
theorem raw_advance_row (c : Compiled)
    (x y : Agent c) (post : PostE)
    (r : RawTok c.t) (hj : r.j < c.t) :
    (rawD1Step c
      {x with rawTok := some r}
      {y with rawTok := none} post).row = "R0b" ∧
    (rawD1Step c
      {x with rawTok := some r}
      {y with rawTok := none} post).reject = false := by
  simp [rawD1Step, hj]

/-- R0b samples the next bit and (at index t) the MARK relation. -/
theorem raw_advance_token (c : Compiled)
    (x y : Agent c) (post : PostE)
    (r : RawTok c.t) (hj : r.j < c.t) :
    (rawD1Step c
      {x with rawTok := some r}
      {y with rawTok := none} post).tokY =
      some { jm1 := ⟨r.j, hj⟩
             z := r.z || y.u
             p := Bool.xor r.p (c.taps r.j && y.u)
             a := r.a && y.u
             h := r.h || post.eY.l
             m := if r.j + 1 == c.t then
               (!(r.h || post.eY.l) && (y.beta != (r.a && y.u)))
               else false } := by
  simp [rawD1Step, hj]

/-- Exact R0c terminal rejection: the latched MARK failure survives
a terminal leader; ZERO and REC do not. -/
theorem raw_terminal_formula (c : Compiled)
    (x y : Agent c) (post : PostE)
    (r : RawTok c.t) (hj : r.j = c.t) :
    (rawD1Step c
      {x with rawTok := some r}
      {y with rawTok := none} post).reject =
      (r.m || (!(r.h || post.eY.l) && (!r.z || (y.u != r.p)))) := by
  have hnot : ¬ r.j < c.t := by omega
  simp [rawD1Step, hnot]

/-- Link to the event field returned by the installed certificate owner. -/
theorem certificate_raw_event (c : Compiled)
    (x y : Agent c) :
    (certificateStepFull c x y).event.d1Reject =
      (rawD1Step c x y (postEInfo x y)).reject := by
  rfl

/-! ## Static window and genuinely sampled terminal accumulators -/

def rawWindowAny {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n) : Bool :=
  Fin.foldl c.t
    (fun acc j => acc || certWindow W s j) false

def rawWindowAll {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n) : Bool :=
  Fin.foldl c.t
    (fun acc j => acc && certWindow W s j) true

def rawWindowParity {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n) : Bool :=
  Fin.foldl c.t
    (fun acc j => Bool.xor acc (c.taps j.val && certWindow W s j)) false

/-- Source-supported widths have t >= 2. The marker check is first
latched in R0b at the completion of those t samples. -/
def rawSampledTerminal {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n)
    (ht : 2 ≤ c.t) : RawTok c.t :=
  { jm1 := ⟨c.t - 1, by omega⟩
    z := rawWindowAny W s
    p := rawWindowParity W s
    a := rawWindowAll W s
    h := false
    m := certMarker W (certSite s (c.t - 1)) != rawWindowAll W s }

theorem raw_sampled_terminal_index {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n)
    (ht : 2 ≤ c.t) :
    (rawSampledTerminal W s ht).j = c.t := by
  change c.t - 1 + 1 = c.t
  omega

/-- Terminal R0c is exactly MARK OR (unexempt ZERO OR REC). -/
theorem raw_sampled_terminal_formula {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n)
    (ht : 2 ≤ c.t) (x y : Agent c) (post : PostE) :
    (rawD1Step c
      {x with rawTok := some (rawSampledTerminal W s ht)}
      {y with rawTok := none} post).reject =
      ((certMarker W (certSite s (c.t - 1)) != rawWindowAll W s) ||
       (!post.eY.l &&
         (!rawWindowAny W s || (y.u != rawWindowParity W s)))) := by
  have h := raw_terminal_formula c x y post
    (rawSampledTerminal W s ht) (raw_sampled_terminal_index W s ht)
  simpa [rawSampledTerminal, rawWindowAny, rawWindowAll,
    rawWindowParity] using h

/-- Exact bridge for the paper's MarkerRelation on a rootless window. -/
theorem raw_marker_failure_iff {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n)
    (hroot : RootlessCertificate W) :
    ¬ MarkerRelation W s ↔
      certMarker W (certSite s (c.t - 1)) ≠ rawWindowAll W s := by
  constructor
  · intro hbad heq
    apply hbad
    intro _
    exact heq
  · intro hbad hrelation
    apply hbad
    exact hrelation (by intro j; exact hroot _)

/-- A full post-cut sampled token rejects a false MarkerRelation. -/
theorem raw_sampled_terminal_rejects_marker {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n)
    (ht : 2 ≤ c.t) (hroot : RootlessCertificate W)
    (hbad : ¬ MarkerRelation W s)
    (x y : Agent c) (post : PostE) :
    (rawD1Step c
      {x with rawTok := some (rawSampledTerminal W s ht)}
      {y with rawTok := none} post).reject = true := by
  have hne := (raw_marker_failure_iff W s hroot).mp hbad
  have hm :
      (certMarker W (certSite s (c.t - 1)) != rawWindowAll W s) = true := by
    cases hb : certMarker W (certSite s (c.t - 1)) <;>
      cases ha : rawWindowAll W s <;>
      simp [hb, ha] at hne ⊢
  rw [raw_sampled_terminal_formula]
  simp [hm]

/-- If the sampled OR is zero, or the following bit disagrees with
the tap parity, R0c rejects unless the terminal is a leader. -/
theorem raw_sampled_terminal_rejects_lower {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n)
    (ht : 2 ≤ c.t) (x y : Agent c) (post : PostE)
    (hfollow : post.eY.l = false)
    (hbad : rawWindowAny W s = false ∨
      y.u ≠ rawWindowParity W s) :
    (rawD1Step c
      {x with rawTok := some (rawSampledTerminal W s ht)}
      {y with rawTok := none} post).reject = true := by
  rw [raw_sampled_terminal_formula]
  rw [hfollow]
  rcases hbad with hz | hp
  · simp [hz]
  · cases hb : y.u <;>
      cases ha : rawWindowParity W s <;>
      simp [hb, ha] at hp ⊢

/-! ## Causal report predicate on real protocol configurations -/

/-- A real full L3 trajectory, not a surrogate raw-only protocol. -/
structure RealRawTrace (n q : Nat) (ring : DirectedRing n) where
  states : Nat → (protocol q).Configuration n
  edges : Nat → Fin n
  evolves : ∀ k, states (k + 1) =
    (protocol q).step ring (states k) (edges k)

/-- Installed raw result on the OLD selected pair at time k. -/
def traceRawResult {n q : Nat} {ring : DirectedRing n}
    (T : RealRawTrace n q ring) (k : Nat) :
    RawResult (compileAdvice q).t :=
  let c := compileAdvice q
  let x := T.edges k
  let y := ring.rightNeighbor x
  rawD1Step c (T.states k x) (T.states k y)
    (postEInfo (T.states k x) (T.states k y))

def TraceRawReject {n q : Nat} {ring : DirectedRing n}
    (T : RealRawTrace n q ring) (k : Nat) : Prop :=
  (traceRawResult T k).reject = true

/-- The true sampled prefix at stage j+1 (j counts from zero). -/
def rawPrefixSample {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n)
    (j : Fin c.t) : RawTok c.t :=
  let k := j.val + 1
  let all := Fin.foldl k
    (fun acc i => acc && certBit W (certSite s i.val)) true
  { jm1 := j
    z := Fin.foldl k
      (fun acc i => acc || certBit W (certSite s i.val)) false
    p := Fin.foldl k
      (fun acc i => Bool.xor acc
        (c.taps i.val && certBit W (certSite s i.val))) false
    a := all
    h := false
    m := if k == c.t then
      certMarker W (certSite s (c.t - 1)) != all
      else false }

/-- A sufficient full-window, post-cut provenance witness.

Each inspected record belongs to the actual chronological trace;
a fresh R1c launch precedes each recorded stage, and the selected
forward edges are in order, with other global edges allowed between
them. This does NOT encode the more tolerant paper coupon-clear event. -/
def FreshCoverWitness {n q : Nat} {ring : DirectedRing n}
    (T : RealRawTrace n q ring)
    (W : CertificateWord n (compileAdvice q))
    (s : Fin n) (cut terminal : Nat) : Prop :=
  ∃ launch : Nat,
    cut ≤ launch ∧
    launch + (compileAdvice q).t = terminal ∧
    T.edges launch = certSite s (n - 1) ∧
    (traceRawResult T launch).row = "R1c" ∧
    (∀ j : Fin (compileAdvice q).t,
      T.edges (launch + 1 + j.val) = certSite s j.val ∧
      (T.states (launch + 1 + j.val) (certSite s j.val)).rawTok =
        some (rawPrefixSample W s j))

/-- Full event: causal window-cover witness and an actual raw rejection.
A bare static false relation does not provide this history. -/
def FreshScanReject {n q : Nat} {ring : DirectedRing n}
    (T : RealRawTrace n q ring)
    (W : CertificateWord n (compileAdvice q))
    (s : Fin n) (cut terminal : Nat) : Prop :=
  FreshCoverWitness T W s cut terminal ∧ TraceRawReject T terminal

/-! ## Exact rational F and an integer bound for the cost API -/

/-- The factorial (core Lean has no `Nat.factorial`). -/
def freshFact : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * freshFact k

/-- F(t) = numerator / denominator, with 20/19 retained exactly. -/
def freshFactorNumerator (t : Nat) : Nat :=
  t ^ t *
    (3 * (t + 2) ^ 2 * freshFact (t + 3) * 20 ^ (t + 3) +
     (2 * t + 5) * 19 ^ (t + 3))

def freshFactorDenominator (t : Nat) : Nat :=
  19 ^ (t + 3)

def freshFactor (t : Nat) : Rat :=
  (freshFactorNumerator t : Rat) / (freshFactorDenominator t : Rat)

/-- Slightly conservative integer bound, F(t) <= upper(t). -/
def freshFactorUpper (t : Nat) : Nat :=
  freshFactorNumerator t / freshFactorDenominator t + 1

theorem freshFactorDenominator_pos (t : Nat) :
    0 < freshFactorDenominator t := by
  unfold freshFactorDenominator
  exact Nat.pow_pos (by omega : 0 < 19)

theorem freshFactorNumerator_le_upper (t : Nat) :
    freshFactorNumerator t ≤
      freshFactorDenominator t * freshFactorUpper t := by
  have hmod :
      freshFactorNumerator t % freshFactorDenominator t <
      freshFactorDenominator t :=
    Nat.mod_lt _ (freshFactorDenominator_pos t)
  have hdiv := Nat.mod_add_div
    (freshFactorNumerator t) (freshFactorDenominator t)
  unfold freshFactorUpper
  calc
    freshFactorNumerator t =
        freshFactorNumerator t % freshFactorDenominator t +
          freshFactorDenominator t *
            (freshFactorNumerator t / freshFactorDenominator t) :=
      hdiv.symm
    _ ≤ freshFactorDenominator t +
          freshFactorDenominator t *
            (freshFactorNumerator t / freshFactorDenominator t) :=
      Nat.add_le_add_right (Nat.le_of_lt hmod) _
    _ = freshFactorDenominator t *
          (freshFactorNumerator t / freshFactorDenominator t + 1) := by
      simp [Nat.mul_add, Nat.add_comm]

/-- Conversion into the exact first-hit cost API. This is an equivalence,
NOT the unproved bound on its right-hand side. -/
theorem fresh_cost_iff_expected {S : Type} {n : Nat}
    (hn : 0 < n) (next : S → Fin n → S)
    (target : S → Prop) (x : S) (t : Nat) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      next target x ((n * freshFactorUpper t : Nat) : Rat) ↔
    ∀ T : Nat,
      K2ArbitraryElimination.FiniteAccounting.costNumerator
        next target x T ≤ n ^ T * (n * freshFactorUpper t) := by
  exact UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    next target hn x (n * freshFactorUpper t)


/-! ## Real transition projection and strict-target obstruction

The frozen-word paper lemma permits unrelated services between scan edges.
The older FreshCoverWitness does not. Its event imposes consecutive global
scheduler services; this is too rare for the claimed n * F(t) cost bound.
-/

/-- The real pair's raw fields are those of the literal raw owner.
There is no replacement raw-only transition. -/
theorem fresh_raw_pair_projection (c : Compiled) (x y : Agent c) :
    (transition c x y).1.rawTok =
        (rawD1Step c x y (postEInfo x y)).tokX ∧
    (transition c x y).2.rawTok =
        (rawD1Step c x y (postEInfo x y)).tokY ∧
    (transition c x y).1.rawKick =
        (rawD1Step c x y (postEInfo x y)).kickX ∧
    (transition c x y).2.rawKick =
        (rawD1Step c x y (postEInfo x y)).kickY := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The exact consecutive pattern forced by the existing witness. -/
def StrictFreshEdgeBlock {n q : Nat} {ring : DirectedRing n}
    (T : RealRawTrace n q ring) (s : Fin n) (launch : Nat) : Prop :=
  T.edges launch = certSite s (n - 1) ∧
  ∀ j : Fin (compileAdvice q).t,
    T.edges (launch + 1 + j.val) = certSite s j.val

theorem fresh_cover_requires_strict_block
    {n q : Nat} {ring : DirectedRing n}
    (T : RealRawTrace n q ring)
    (W : CertificateWord n (compileAdvice q))
    (s : Fin n) (cut terminal : Nat)
    (h : FreshCoverWitness T W s cut terminal) :
    ∃ launch : Nat,
      cut ≤ launch ∧
      launch + (compileAdvice q).t = terminal ∧
      StrictFreshEdgeBlock T s launch := by
  rcases h with ⟨launch, hcut, hterminal, hedge, _hrow, hstages⟩
  refine ⟨launch, hcut, hterminal, ?_⟩
  exact ⟨hedge, fun j => (hstages j).1⟩

theorem fresh_reject_requires_strict_block
    {n q : Nat} {ring : DirectedRing n}
    (T : RealRawTrace n q ring)
    (W : CertificateWord n (compileAdvice q))
    (s : Fin n) (cut terminal : Nat)
    (h : FreshScanReject T W s cut terminal) :
    ∃ launch : Nat,
      cut ≤ launch ∧
      launch + (compileAdvice q).t = terminal ∧
      StrictFreshEdgeBlock T s launch := by
  exact fresh_cover_requires_strict_block T W s cut terminal h.1

/-- Observation-only chronology permitting arbitrary interleaved
global services. All inspected raw records are real trace fields.
The last stage is required to be the terminal selected service. -/
def InterleavedFreshCover {n q : Nat} {ring : DirectedRing n}
    (T : RealRawTrace n q ring)
    (W : CertificateWord n (compileAdvice q))
    (s : Fin n) (cut terminal : Nat) : Prop :=
  ∃ launch : Nat,
  ∃ stages : Fin (compileAdvice q).t → Nat,
    cut ≤ launch ∧
    T.edges launch = certSite s (n - 1) ∧
    (traceRawResult T launch).row = "R1c" ∧
    (∀ j : Fin (compileAdvice q).t,
      launch < stages j ∧
      stages j ≤ terminal ∧
      T.edges (stages j) = certSite s j.val ∧
      (T.states (stages j) (certSite s j.val)).rawTok =
        some (rawPrefixSample W s j)) ∧
    (∀ i j : Fin (compileAdvice q).t,
      i.val < j.val → stages i < stages j) ∧
    (∃ j : Fin (compileAdvice q).t,
      j.val + 1 = (compileAdvice q).t ∧
      stages j = terminal)

theorem fresh_cover_implies_interleaved
    {n q : Nat} {ring : DirectedRing n}
    (T : RealRawTrace n q ring)
    (W : CertificateWord n (compileAdvice q))
    (s : Fin n) (cut terminal : Nat)
    (ht : 0 < (compileAdvice q).t)
    (h : FreshCoverWitness T W s cut terminal) :
    InterleavedFreshCover T W s cut terminal := by
  rcases h with ⟨launch, hcut, hlast, hedge, hrow, hstages⟩
  refine ⟨launch, (fun j => launch + 1 + j.val),
    hcut, hedge, hrow, ?_, ?_, ?_⟩
  · intro j
    dsimp only
    have hj := j.isLt
    exact ⟨by omega, by omega, (hstages j).1, (hstages j).2⟩
  · intro i j hij
    dsimp only
    omega
  · refine ⟨⟨(compileAdvice q).t - 1, by omega⟩, by dsimp only; omega, ?_⟩
    dsimp only
    omega

def InterleavedFreshReject {n q : Nat} {ring : DirectedRing n}
    (T : RealRawTrace n q ring)
    (W : CertificateWord n (compileAdvice q))
    (s : Fin n) (cut terminal : Nat) : Prop :=
  InterleavedFreshCover T W s cut terminal ∧
  TraceRawReject T terminal

theorem strict_reject_implies_interleaved
    {n q : Nat} {ring : DirectedRing n}
    (T : RealRawTrace n q ring)
    (W : CertificateWord n (compileAdvice q))
    (s : Fin n) (cut terminal : Nat)
    (ht : 0 < (compileAdvice q).t)
    (h : FreshScanReject T W s cut terminal) :
    InterleavedFreshReject T W s cut terminal := by
  exact ⟨fresh_cover_implies_interleaved T W s cut terminal ht h.1, h.2⟩

/-! ## A legal rootless start with a failing nonzero test -/

def freshBlankConfiguration (n q : Nat) :
    (protocol q).Configuration n :=
  fun _ => Agent.blank (compileAdvice q)

theorem fresh_blank_is_rootless (n q : Nat) :
    RootlessCertificate
      (certificateWordOfAgents (compileAdvice q)
        (freshBlankConfiguration n q)) := by
  intro i
  rfl

theorem fresh_blank_fails_nonzero {n q : Nat}
    (s : Fin n) :
    ¬ NonzeroRelation
      (certificateWordOfAgents (compileAdvice q)
        (freshBlankConfiguration n q)) s := by
  intro hrelation
  have hArc :
      certFollowerArc
        (certificateWordOfAgents (compileAdvice q)
          (freshBlankConfiguration n q))
        s ((compileAdvice q).t + 1) := by
    intro j
    rfl
  obtain ⟨j, htrue⟩ := hrelation hArc
  have hfalse :
      certWindow
        (certificateWordOfAgents (compileAdvice q)
          (freshBlankConfiguration n q)) s j = false := by
    rfl
  have hcontradiction : (false : Bool) = true :=
    hfalse.symm.trans htrue
  cases hcontradiction

/-! ## A numerical certificate for the strict pattern lower bound

At q=8,n=256, width t=3. The original strict event requires
(e_255,e_0,e_1,e_2) in four consecutive global scheduler services.
For B=n*freshFactorUpper 3 the strict inequality 4 B < n^4 holds.
The elementary union-bound/cost contradiction is given below in prose.
-/

theorem fresh_factor_upper_at_three :
    freshFactorUpper 3 = 1983723 := by
  decide

theorem fresh_strict_block_numeric_gap :
    4 * (256 * freshFactorUpper 3) < 256 ^ 4 := by
  simpa only [fresh_factor_upper_at_three] using
    (show 4 * (256 * 1983723) < 256 ^ 4 by decide)


/-! ## Causal raw-scanner provenance ghost

Proof-only tags track actual tokens; no physical row changes. The
timestamp map has at most t indices; its Nat values are ghost data,
not additional protocol states. A future soundness induction must
connect those timestamps to sampled data on the real frozen trace.
-/

inductive GhostRawTag (n t : Nat) where
  | vacant
  | inherited
  | fresh (origin : Fin n) (launchAt : Nat)
      (moves : Fin t → Option Nat)

/-- Do not promote an inconsistently untagged resident to fresh. -/
def ghostKeepTag {n t : Nat} :
    GhostRawTag n t → GhostRawTag n t
  | .vacant => .inherited
  | .inherited => .inherited
  | .fresh s launch times => .fresh s launch times

/-- OLD-pair tag arbiter in the exact rawD1Step priority order.
R0a/R1a keep the resident tag. R0b transfers the source, stamping
its outgoing service index. R1c creates fresh provenance. R0c
leaves no successor scanner. -/
def ghostResponderTag {n : Nat} (c : Compiled)
    (oldX oldY : Agent c) (post : PostE)
    (markX markY : GhostRawTag n c.t)
    (y : Fin n) (clock : Nat) : GhostRawTag n c.t :=
  let raw := rawD1Step c oldX oldY post
  match raw.tokY with
  | none => .vacant
  | some _ =>
    match oldY.rawTok with
    | some _ => ghostKeepTag markY
    | none =>
      match oldX.rawTok with
      | some r =>
        if r.j < c.t then
          match markX with
          | .fresh s launch times =>
            .fresh s launch
              (fun j => if j = r.jm1 then some clock else times j)
          | _ => .inherited
        else .inherited
      | none =>
        if oldY.rawKick then
          .fresh y clock (fun _ => none)
        else .inherited

structure GhostRaw (n q : Nat) where
  physical : (protocol q).Configuration n
  marks : Fin n → GhostRawTag n (compileAdvice q).t
  cut : Nat
  clock : Nat

/-- At an adapted cut all existing tokens are untrusted predecessors. -/
def ghostRawInit {n q : Nat}
    (C : (protocol q).Configuration n) (cut : Nat) : GhostRaw n q :=
  { physical := C
    marks := fun i =>
      if (C i).rawTok.isSome then .inherited else .vacant
    cut := cut
    clock := cut }

/-- The REAL protocol performs the physical successor; the ghost
updates only the two corresponding tag sites. -/
def ghostRawStep {n q : Nat}
    (ring : DirectedRing n) (G : GhostRaw n q)
    (e : Fin n) : GhostRaw n q :=
  let c := compileAdvice q
  let y := ring.rightNeighbor e
  let oldX := G.physical e
  let oldY := G.physical y
  let nextY := ghostResponderTag c oldX oldY
    (postEInfo oldX oldY) (G.marks e) (G.marks y)
    y G.clock
  { physical := (protocol q).step ring G.physical e
    marks := fun i =>
      if i = y then nextY
      else if i = e then .vacant
      else G.marks i
    cut := G.cut
    clock := G.clock + 1 }

/-- Projection identity, for every configuration and selected edge. -/
theorem ghostRawStep_projection {n q : Nat}
    (ring : DirectedRing n) (G : GhostRaw n q)
    (e : Fin n) :
    (ghostRawStep ring G e).physical =
      (protocol q).step ring G.physical e := by
  rfl

theorem ghostRawInit_projection {n q : Nat}
    (C : (protocol q).Configuration n) (cut : Nat) :
    (ghostRawInit C cut).physical = C := by
  rfl

theorem ghostRawStep_clock {n q : Nat}
    (ring : DirectedRing n) (G : GhostRaw n q)
    (e : Fin n) :
    (ghostRawStep ring G e).clock = G.clock + 1 := by
  rfl

theorem ghostRawStep_cut {n q : Nat}
    (ring : DirectedRing n) (G : GhostRaw n q)
    (e : Fin n) :
    (ghostRawStep ring G e).cut = G.cut := by
  rfl

/-- Inherited-token initialization never forges a fresh lineage. -/
theorem ghostRawInit_no_fresh {n q : Nat}
    (C : (protocol q).Configuration n) (cut : Nat)
    (i s : Fin n) (launch : Nat)
    (times : Fin (compileAdvice q).t → Option Nat) :
    (ghostRawInit C cut).marks i ≠
      .fresh s launch times := by
  cases h : (C i).rawTok <;>
    simp [ghostRawInit, h]

/-- R0a collision retains the RESIDENT mark. -/
theorem ghostResponder_collision {n : Nat} (c : Compiled)
    (x y : Agent c) (post : PostE)
    (left right : RawTok c.t)
    (markX markY : GhostRawTag n c.t)
    (site : Fin n) (clock : Nat) :
    ghostResponderTag c
      {x with rawTok := some left}
      {y with rawTok := some right} post
      markX markY site clock = ghostKeepTag markY := by
  rfl

/-- R1a, source empty and destination occupied, retains its resident. -/
theorem ghostResponder_resident {n : Nat} (c : Compiled)
    (x y : Agent c) (post : PostE)
    (right : RawTok c.t)
    (markX markY : GhostRawTag n c.t)
    (site : Fin n) (clock : Nat) :
    ghostResponderTag c
      {x with rawTok := none}
      {y with rawTok := some right} post
      markX markY site clock = ghostKeepTag markY := by
  rfl

/-- R1b arms the kick but has no scanner to tag. -/
theorem ghostResponder_arming {n : Nat} (c : Compiled)
    (x y : Agent c) (post : PostE)
    (markX markY : GhostRawTag n c.t)
    (site : Fin n) (clock : Nat) :
    ghostResponderTag c
      {x with rawTok := none}
      {y with rawTok := none, rawKick := false} post
      markX markY site clock = .vacant := by
  rfl

/-- R1c genuine launch; the tag records its first service time. -/
theorem ghostResponder_launch {n : Nat} (c : Compiled)
    (x y : Agent c) (post : PostE)
    (markX markY : GhostRawTag n c.t)
    (site : Fin n) (clock : Nat)
    (ht : 0 < c.t) :
    ghostResponderTag c
      {x with rawTok := none}
      {y with rawTok := none, rawKick := true} post
      markX markY site clock =
        .fresh site clock (fun _ => none) := by
  simp [ghostResponderTag, rawD1Step, ht]

/-- R0b forwards the source provenance, appending this service time. -/
theorem ghostResponder_forward {n : Nat} (c : Compiled)
    (x y : Agent c) (post : PostE)
    (r : RawTok c.t) (hj : r.j < c.t)
    (s : Fin n) (launch : Nat)
    (times : Fin c.t → Option Nat)
    (markY : GhostRawTag n c.t)
    (site : Fin n) (clock : Nat) :
    ghostResponderTag c
      {x with rawTok := some r}
      {y with rawTok := none} post
      (.fresh s launch times) markY site clock =
        .fresh s launch
          (fun k => if k = r.jm1 then some clock else times k) := by
  simp [ghostResponderTag, rawD1Step, hj]

/-- R0c consumes the source token: no responder mark survives. -/
theorem ghostResponder_terminal {n : Nat} (c : Compiled)
    (x y : Agent c) (post : PostE)
    (r : RawTok c.t) (hj : r.j = c.t)
    (markX markY : GhostRawTag n c.t)
    (site : Fin n) (clock : Nat) :
    ghostResponderTag c
      {x with rawTok := some r}
      {y with rawTok := none} post
      markX markY site clock = .vacant := by
  have hnot : ¬ r.j < c.t := by omega
  simp [ghostResponderTag, rawD1Step, hnot]

theorem ghostRawStep_source_vacant {n q : Nat}
    (ring : DirectedRing n) (G : GhostRaw n q)
    (e : Fin n) (hxy : e ≠ ring.rightNeighbor e) :
    (ghostRawStep ring G e).marks e = .vacant := by
  simp [ghostRawStep, hxy]

theorem ghostRawStep_other_mark {n q : Nat}
    (ring : DirectedRing n) (G : GhostRaw n q)
    (e i : Fin n)
    (hiX : i ≠ e) (hiY : i ≠ ring.rightNeighbor e) :
    (ghostRawStep ring G e).marks i = G.marks i := by
  simp [ghostRawStep, hiX, hiY]

/-! ## Projected real trace and explicit frozen data requirement -/

structure GhostRawTrace (n q : Nat) (ring : DirectedRing n) where
  states : Nat → GhostRaw n q
  edges : Nat → Fin n
  evolves : ∀ k, states (k + 1) =
    ghostRawStep ring (states k) (edges k)

def ghostTraceReal {n q : Nat} {ring : DirectedRing n}
    (T : GhostRawTrace n q ring) : RealRawTrace n q ring :=
  { states := fun k => (T.states k).physical
    edges := T.edges
    evolves := by
      intro k
      have h := congrArg
        (fun G : GhostRaw n q => G.physical) (T.evolves k)
      simpa only [ghostRawStep_projection] using h }

/-- Frozen OLD u/beta and rootlessness throughout the causal segment.
Only assuming W was rootless at the entrance is insufficient because
the actual birth owner can change native l without changing u/beta. -/
def GhostRawFrozen {n q : Nat} {ring : DirectedRing n}
    (T : GhostRawTrace n q ring)
    (W : CertificateWord n (compileAdvice q))
    (start stop : Nat) : Prop :=
  ∀ k : Nat, start ≤ k → k ≤ stop →
    ∀ i : Fin n,
      ((T.states k).physical i).u = certBit W i ∧
      ((T.states k).physical i).beta = certMarker W i ∧
      ((T.states k).physical i).l = false

/-- The intended source-payload invariant, separated from chronology. -/
def GhostTagPayloadSoundAt {n q : Nat}
    (G : GhostRaw n q)
    (W : CertificateWord n (compileAdvice q)) : Prop :=
  ∀ (site s : Fin n) (launch : Nat)
    (times : Fin (compileAdvice q).t → Option Nat),
    G.marks site = .fresh s launch times →
    ∃ j : Fin (compileAdvice q).t,
      (G.physical site).rawTok = some (rawPrefixSample W s j)

/-- At an initialization cut, soundness holds without assuming any
inherited token is valid: no fresh tag yet exists. -/
theorem ghostRawInit_payload_sound {n q : Nat}
    (C : (protocol q).Configuration n) (cut : Nat)
    (W : CertificateWord n (compileAdvice q)) :
    GhostTagPayloadSoundAt (ghostRawInit C cut) W := by
  intro site s launch times h
  exact False.elim
    ((ghostRawInit_no_fresh C cut site s launch times) h)

/-- A tagged R0c event, with payload equality made explicit instead
of assuming the currently unfinished global payload induction. -/
def GhostTaggedTerminal {n q : Nat} {ring : DirectedRing n}
    (T : GhostRawTrace n q ring)
    (W : CertificateWord n (compileAdvice q))
    (s : Fin n) (k : Nat) : Prop :=
  ∃ launch : Nat,
  ∃ times : Fin (compileAdvice q).t → Option Nat,
  ∃ j : Fin (compileAdvice q).t,
    (T.states k).marks (T.edges k) = .fresh s launch times ∧
    ((T.states k).physical (T.edges k)).rawTok =
      some (rawPrefixSample W s j) ∧
    j.val + 1 = (compileAdvice q).t ∧
    (traceRawResult (ghostTraceReal T) k).row = "R0c" ∧
    TraceRawReject (ghostTraceReal T) k

/-! ## Historical receipts needed for the terminal-to-trace bridge

This is the missing global induction invariant, stated precisely.
It is not imposed as an implicit condition on GhostRaw.
-/

def GhostTagHistorySoundAt {n q : Nat} {ring : DirectedRing n}
    (T : GhostRawTrace n q ring)
    (W : CertificateWord n (compileAdvice q))
    (cut k : Nat) : Prop :=
  ∀ (site s : Fin n) (launch : Nat)
    (times : Fin (compileAdvice q).t → Option Nat)
    (j : Fin (compileAdvice q).t),
    (T.states k).marks site = .fresh s launch times →
    ((T.states k).physical site).rawTok =
      some (rawPrefixSample W s j) →
    site = certSite s j.val ∧
    cut ≤ launch ∧
    launch < k ∧
    T.edges launch = certSite s (n - 1) ∧
    (traceRawResult (ghostTraceReal T) launch).row = "R1c" ∧
    (∀ i : Fin (compileAdvice q).t, i.val < j.val →
      ∃ service : Nat,
        times i = some service ∧
        launch < service ∧ service < k ∧
        T.edges service = certSite s i.val ∧
        ((T.states service).physical (certSite s i.val)).rawTok =
          some (rawPrefixSample W s i)) ∧
    (∀ i h : Fin (compileAdvice q).t,
      i.val < h.val → h.val < j.val →
      ∃ a b : Nat,
        times i = some a ∧ times h = some b ∧ a < b)

/-- The terminal-to-InterleavedFreshReject implication is proved
from the explicitly named causal receipt invariant. The missing
obligation is to prove that initialized ghost traces preserve it
under GhostRawFrozen; it is not silently assumed by the ghost type. -/
theorem ghost_tagged_terminal_to_interleaved
    {n q : Nat} {ring : DirectedRing n}
    (T : GhostRawTrace n q ring)
    (W : CertificateWord n (compileAdvice q))
    (s : Fin n) (cut k : Nat)
    (hHistory : GhostTagHistorySoundAt T W cut k)
    (h : GhostTaggedTerminal T W s k) :
    InterleavedFreshReject (ghostTraceReal T) W s cut k := by
  rcases h with
    ⟨launch, times, j, htag, htok, hj, _hrow, hreject⟩
  obtain ⟨hsite, hcut, hlaunch, hedge, hlaunchrow,
      hprev, horder⟩ :=
    hHistory (T.edges k) s launch times j htag htok
  let stages : Fin (compileAdvice q).t → Nat :=
    fun i =>
      if i.val + 1 = (compileAdvice q).t then k
      else (times i).getD 0
  have hstage (i : Fin (compileAdvice q).t) :
      launch < stages i ∧ stages i ≤ k ∧
      T.edges (stages i) = certSite s i.val ∧
      ((T.states (stages i)).physical (certSite s i.val)).rawTok =
        some (rawPrefixSample W s i) := by
    by_cases hl : i.val + 1 = (compileAdvice q).t
    · have heq : i = j := by
        apply Fin.ext
        omega
      subst i
      have htime : stages j = k := by
        simp [stages, hj]
      rw [htime]
      exact ⟨hlaunch, Nat.le_refl _, hsite, hsite ▸ htok⟩
    · have hiless : i.val < j.val := by omega
      obtain ⟨service, htime, hafter, hbefore, he, ht⟩ :=
        hprev i hiless
      have hs : stages i = service := by
        simp [stages, hl, htime]
      rw [hs]
      exact ⟨hafter, by omega, he, ht⟩
  have hstages_order (i h : Fin (compileAdvice q).t)
      (hih : i.val < h.val) : stages i < stages h := by
    by_cases hlast : h.val + 1 = (compileAdvice q).t
    · have hiless : i.val < j.val := by omega
      obtain ⟨a, ha, _, hb, _, _⟩ := hprev i hiless
      have hiNot : ¬ i.val + 1 = (compileAdvice q).t := by omega
      have hia : stages i = a := by simp [stages, hiNot, ha]
      have hhk : stages h = k := by simp [stages, hlast]
      rw [hia, hhk]
      exact hb
    · have hiNot : ¬ i.val + 1 = (compileAdvice q).t := by omega
      have hsmall : h.val < j.val := by omega
      obtain ⟨a, b, ha, hb, hab⟩ :=
        horder i h hih hsmall
      have hia : stages i = a := by simp [stages, hiNot, ha]
      have hhb : stages h = b := by simp [stages, hlast, hb]
      rw [hia, hhb]
      exact hab
  refine ⟨?_, hreject⟩
  refine ⟨launch, stages, hcut, hedge, hlaunchrow,
    hstage, hstages_order, ?_⟩
  refine ⟨j, hj, ?_⟩
  simp [stages, hj]


/-! ## Static prefix folds and literal ring geometry

These lemmas are deliberately about
the installed rawD1Step and physical rightNeighbor, not an auxiliary
scanner transition.
-/

private theorem fresh_fold_last {α : Type}
    (f : α → Nat → α) (a : α) (k : Nat) :
    Fin.foldl (k + 1) (fun z i => f z i.val) a =
      f (Fin.foldl k (fun z i => f z i.val) a) k := by
  simpa only [Fin.foldl_succ_last, Fin.val_castSucc, Fin.val_last]

theorem raw_prefix_first {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n)
    (ht : 2 ≤ c.t) :
    rawPrefixSample W s ⟨0, by omega⟩ =
      { jm1 := ⟨0, by omega⟩
        z := certBit W s
        p := c.taps 0 && certBit W s
        a := certBit W s
        h := false
        m := false } := by
  have hneq : (1 : Nat) ≠ c.t := by omega
  simp [rawPrefixSample, Fin.foldl_succ, certSite_zero, hneq]

theorem raw_prefix_or_succ {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n)
    (j : Fin c.t) (hj : j.val + 1 < c.t) :
    (rawPrefixSample W s ⟨j.val + 1, hj⟩).z =
      ((rawPrefixSample W s j).z ||
        certBit W (certSite s (j.val + 1))) := by
  change
    Fin.foldl (j.val + 1 + 1)
      (fun z i => z || certBit W (certSite s i.val)) false =
    ((Fin.foldl (j.val + 1)
      (fun z i => z || certBit W (certSite s i.val)) false) ||
      certBit W (certSite s (j.val + 1)))
  exact fresh_fold_last (fun z i => z || certBit W (certSite s i))
    false (j.val + 1)

theorem raw_prefix_xor_succ {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n)
    (j : Fin c.t) (hj : j.val + 1 < c.t) :
    (rawPrefixSample W s ⟨j.val + 1, hj⟩).p =
      Bool.xor (rawPrefixSample W s j).p
        (c.taps (j.val + 1) &&
          certBit W (certSite s (j.val + 1))) := by
  change
    Fin.foldl (j.val + 1 + 1)
      (fun z i => Bool.xor z
        (c.taps i.val && certBit W (certSite s i.val))) false =
    Bool.xor
      (Fin.foldl (j.val + 1)
        (fun z i => Bool.xor z
          (c.taps i.val && certBit W (certSite s i.val))) false)
      (c.taps (j.val + 1) &&
        certBit W (certSite s (j.val + 1)))
  exact fresh_fold_last
    (fun z i => Bool.xor z (c.taps i &&
      certBit W (certSite s i))) false (j.val + 1)

theorem raw_prefix_and_succ {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n)
    (j : Fin c.t) (hj : j.val + 1 < c.t) :
    (rawPrefixSample W s ⟨j.val + 1, hj⟩).a =
      ((rawPrefixSample W s j).a &&
        certBit W (certSite s (j.val + 1))) := by
  change
    Fin.foldl (j.val + 1 + 1)
      (fun z i => z && certBit W (certSite s i.val)) true =
    ((Fin.foldl (j.val + 1)
      (fun z i => z && certBit W (certSite s i.val)) true) &&
      certBit W (certSite s (j.val + 1)))
  exact fresh_fold_last (fun z i => z && certBit W (certSite s i))
    true (j.val + 1)

theorem raw_prefix_marker_succ {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n)
    (j : Fin c.t) (hj : j.val + 1 < c.t) :
    (rawPrefixSample W s ⟨j.val + 1, hj⟩).m =
      (if j.val + 1 + 1 == c.t then
        certMarker W (certSite s (j.val + 1)) !=
          ((rawPrefixSample W s j).a &&
            certBit W (certSite s (j.val + 1)))
       else false) := by
  have ha := raw_prefix_and_succ W s j hj
  change
    (if j.val + 1 + 1 == c.t then
      certMarker W (certSite s (c.t - 1)) !=
        (rawPrefixSample W s ⟨j.val + 1, hj⟩).a
     else false) = _
  by_cases hlast : j.val + 1 + 1 = c.t
  · have heq : c.t - 1 = j.val + 1 := by omega
    simp [hlast, heq, ha]
  · simp [hlast]

/-- Structural extensionality for raw tokens. Core Lean 4.33 does
not generate RawTok.ext from DecidableEq/Repr derivations. -/
private theorem raw_tok_fields_ext {t : Nat} (x y : RawTok t)
    (hj : x.jm1 = y.jm1)
    (hz : x.z = y.z)
    (hp : x.p = y.p)
    (ha : x.a = y.a)
    (hh : x.h = y.h)
    (hm : x.m = y.m) : x = y := by
  cases x with
  | mk jx zx px ax hx mx =>
      cases y with
      | mk jy zy py ay hy my =>
          cases hj
          cases hz
          cases hp
          cases ha
          cases hh
          cases hm
          rfl

theorem raw_prefix_next {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n)
    (j : Fin c.t) (hj : j.val + 1 < c.t) :
    rawPrefixSample W s ⟨j.val + 1, hj⟩ =
      { jm1 := ⟨j.val + 1, hj⟩
        z := (rawPrefixSample W s j).z ||
          certBit W (certSite s (j.val + 1))
        p := Bool.xor (rawPrefixSample W s j).p
          (c.taps (j.val + 1) &&
            certBit W (certSite s (j.val + 1)))
        a := (rawPrefixSample W s j).a &&
          certBit W (certSite s (j.val + 1))
        h := false
        m := if j.val + 1 + 1 == c.t then
          certMarker W (certSite s (j.val + 1)) !=
            ((rawPrefixSample W s j).a &&
              certBit W (certSite s (j.val + 1)))
          else false } := by
  apply raw_tok_fields_ext
  · rfl
  · exact raw_prefix_or_succ W s j hj
  · exact raw_prefix_xor_succ W s j hj
  · exact raw_prefix_and_succ W s j hj
  · rfl
  · exact raw_prefix_marker_succ W s j hj

theorem raw_postY_rootless {c : Compiled}
    (x y : Agent c) (hx : x.l = false) (hy : y.l = false) :
    (postEInfo x y).eY.l = false := by
  simp [postEInfo, certLiteralEPair, Agent.certNative, hx, hy]

theorem raw_prefix_launch {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n)
    (ht : 2 ≤ c.t)
    (x y : Agent c) (post : PostE)
    (hx : x.rawTok = none) (hy : y.rawTok = none)
    (hk : y.rawKick = true)
    (hbit : y.u = certBit W s) (hpost : post.eY.l = false) :
    (rawD1Step c x y post).tokY =
      some (rawPrefixSample W s ⟨0, by omega⟩) := by
  rw [raw_prefix_first W s ht]
  simp [rawD1Step, hx, hy, hk, hbit, hpost, show 0 < c.t by omega]

theorem raw_prefix_forward {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n)
    (j : Fin c.t) (hj : j.val + 1 < c.t)
    (x y : Agent c) (post : PostE)
    (hx : x.rawTok = some (rawPrefixSample W s j))
    (hy : y.rawTok = none)
    (hbit : y.u = certBit W (certSite s (j.val + 1)))
    (hbeta : y.beta = certMarker W (certSite s (j.val + 1)))
    (hpost : post.eY.l = false) :
    (rawD1Step c x y post).tokY =
      some (rawPrefixSample W s ⟨j.val + 1, hj⟩) := by
  have hindex : (rawPrefixSample W s j).j < c.t := by
    change j.val + 1 < c.t
    exact hj
  rw [raw_prefix_next W s j hj]
  simp [rawD1Step, hx, hy, hj, hbit, hbeta, hpost,
    rawPrefixSample, RawTok.j]

theorem ring_neighbor_certSite {n : Nat}
    (ring : DirectedRing n) (s : Fin n) (j : Nat) :
    ring.rightNeighbor (certSite s j) = certSite s (j + 1) := by
  calc
    ring.rightNeighbor (certSite s j) =
        certSite (certSite s j) 1 := by
          apply Fin.ext
          rfl
    _ = certSite s (j + 1) := by rw [certSite_add]

theorem ring_predecessor_certSite {n : Nat}
    (ring : DirectedRing n) (e : Fin n) :
    e = certSite (ring.rightNeighbor e) (n - 1) := by
  have hn : 0 < n := ring.hn
  calc
    e = certSite e n := (certSite_n e).symm
    _ = certSite e (1 + (n - 1)) := by
          congr 1
          omega
    _ = certSite (certSite e 1) (n - 1) :=
          (certSite_add e 1 (n - 1)).symm
    _ = certSite (ring.rightNeighbor e) (n - 1) := by
          congr 1

theorem ring_neighbor_distinct {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n) (e : Fin n) :
    e ≠ ring.rightNeighbor e := by
  intro heq
  have hv := congrArg Fin.val heq
  change e.val = (e.val + 1) % n at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have htop : e.val + 1 = n := by
      have hbound := e.isLt
      omega
    rw [htop, Nat.mod_self] at hv
    omega

theorem ghost_step_target_tok {n q : Nat}
    (ring : DirectedRing n) (G : GhostRaw n q)
    (e : Fin n) (hne : e ≠ ring.rightNeighbor e) :
    ((ghostRawStep ring G e).physical (ring.rightNeighbor e)).rawTok =
      (rawD1Step (compileAdvice q)
        (G.physical e) (G.physical (ring.rightNeighbor e))
        (postEInfo (G.physical e)
          (G.physical (ring.rightNeighbor e)))).tokY := by
  let y := ring.rightNeighbor e
  let c := compileAdvice q
  have hproj := (fresh_raw_pair_projection c
    (G.physical e) (G.physical y)).2.1
  have hne' : ring.rightNeighbor e ≠ e := Ne.symm hne
  have hstep : (protocol q).step ring G.physical e (ring.rightNeighbor e) =
      ((protocol q).transition (G.physical e)
        (G.physical (ring.rightNeighbor e))).2 := by
    simp [PopulationProtocol.step, hne']
  rw [ghostRawStep_projection, hstep]
  exact hproj

theorem ghost_step_other_tok {n q : Nat}
    (ring : DirectedRing n) (G : GhostRaw n q)
    (e site : Fin n)
    (hxe : site ≠ e) (hye : site ≠ ring.rightNeighbor e) :
    ((ghostRawStep ring G e).physical site).rawTok =
      (G.physical site).rawTok := by
  change (if site = e then
      (transition (compileAdvice q) (G.physical e)
        (G.physical (ring.rightNeighbor e))).1
    else if site = ring.rightNeighbor e then
      (transition (compileAdvice q) (G.physical e)
        (G.physical (ring.rightNeighbor e))).2
    else G.physical site).rawTok = _
  simp [hxe, hye]

private theorem ghost_keep_fresh {n t : Nat}
    (mark : GhostRawTag n t) (s : Fin n) (launch : Nat)
    (times : Fin t → Option Nat)
    (h : ghostKeepTag mark = .fresh s launch times) :
    mark = .fresh s launch times := by
  cases mark with
  | vacant => cases h
  | inherited => cases h
  | fresh s' l' ts' => exact h


/-! ## One joint invariant (payload plus ordered receipts)

An arbitrary cut is indexed by global time: the initialization equation
is T.states cut = ghostRawInit C cut. Initializing at T.states 0
with a nonzero clock instead would not synchronize launchAt with
T.edges launchAt, and would make the requested history assertion false.
-/

private def GhostTagJointSoundAt {n q : Nat}
    {ring : DirectedRing n}
    (T : GhostRawTrace n q ring)
    (W : CertificateWord n (compileAdvice q))
    (cut k : Nat) : Prop :=
  ∀ (site s : Fin n) (launch : Nat)
    (times : Fin (compileAdvice q).t → Option Nat),
    (T.states k).marks site = .fresh s launch times →
    ∃ j : Fin (compileAdvice q).t,
      ((T.states k).physical site).rawTok =
        some (rawPrefixSample W s j) ∧
      site = certSite s j.val ∧
      cut ≤ launch ∧
      launch < k ∧
      T.edges launch = certSite s (n - 1) ∧
      (traceRawResult (ghostTraceReal T) launch).row = "R1c" ∧
      (∀ i : Fin (compileAdvice q).t, i.val < j.val →
        ∃ service : Nat,
          times i = some service ∧
          launch < service ∧ service < k ∧
          T.edges service = certSite s i.val ∧
          ((T.states service).physical
            (certSite s i.val)).rawTok =
              some (rawPrefixSample W s i)) ∧
      (∀ i h : Fin (compileAdvice q).t,
        i.val < h.val → h.val < j.val →
        ∃ a b : Nat,
          times i = some a ∧ times h = some b ∧ a < b)

private theorem ghost_joint_init {n q : Nat}
    {ring : DirectedRing n}
    (T : GhostRawTrace n q ring)
    (W : CertificateWord n (compileAdvice q))
    (C : (protocol q).Configuration n) (cut : Nat)
    (hinit : T.states cut = ghostRawInit C cut) :
    GhostTagJointSoundAt T W cut cut := by
  intro site s launch times htag
  rw [hinit] at htag
  exact False.elim
    ((ghostRawInit_no_fresh C cut site s launch times) htag)

private theorem ghost_joint_frame {n q : Nat}
    {ring : DirectedRing n}
    (T : GhostRawTrace n q ring)
    (W : CertificateWord n (compileAdvice q))
    (cut k : Nat)
    (hprev : GhostTagJointSoundAt T W cut k)
    (site s : Fin n) (launch : Nat)
    (times : Fin (compileAdvice q).t → Option Nat)
    (htag : (T.states k).marks site = .fresh s launch times)
    (htok :
      ((T.states (k + 1)).physical site).rawTok =
      ((T.states k).physical site).rawTok) :
    ∃ j : Fin (compileAdvice q).t,
      ((T.states (k + 1)).physical site).rawTok =
        some (rawPrefixSample W s j) ∧
      site = certSite s j.val ∧
      cut ≤ launch ∧
      launch < k + 1 ∧
      T.edges launch = certSite s (n - 1) ∧
      (traceRawResult (ghostTraceReal T) launch).row = "R1c" ∧
      (∀ i : Fin (compileAdvice q).t, i.val < j.val →
        ∃ service : Nat,
          times i = some service ∧
          launch < service ∧ service < k + 1 ∧
          T.edges service = certSite s i.val ∧
          ((T.states service).physical
            (certSite s i.val)).rawTok =
              some (rawPrefixSample W s i)) ∧
      (∀ i h : Fin (compileAdvice q).t,
        i.val < h.val → h.val < j.val →
        ∃ a b : Nat,
          times i = some a ∧ times h = some b ∧ a < b) := by
  obtain ⟨j, hraw, hsite, hcut, hlaunch, hedge, hrow,
    hreceipts, horder⟩ := hprev site s launch times htag
  refine ⟨j, htok.trans hraw, hsite, hcut, by omega,
    hedge, hrow, ?_, horder⟩
  intro i hi
  obtain ⟨service, hs, ha, hb, he, hp⟩ := hreceipts i hi
  exact ⟨service, hs, ha, by omega, he, hp⟩

theorem ghost_trace_clock_at {n q : Nat}
    {ring : DirectedRing n}
    (T : GhostRawTrace n q ring)
    (C : (protocol q).Configuration n) (cut : Nat)
    (hinit : T.states cut = ghostRawInit C cut)
    (k : Nat) (hk : cut ≤ k) :
    (T.states k).clock = k := by
  have hrun : ∀ d : Nat,
      (T.states (cut + d)).clock = cut + d := by
    intro d
    induction d with
    | zero =>
        simp only [Nat.add_zero, hinit, ghostRawInit]
    | succ d ih =>
        have hs := congrArg
          (fun G : GhostRaw n q => G.clock)
          (T.evolves (cut + d))
        simpa only [Nat.add_succ, ghostRawStep_clock, ih] using hs
  have hre : k = cut + (k - cut) := by omega
  rw [hre]
  exact hrun (k - cut)

/-- Recover both the existing public predicates from the stronger
lineage invariant, without postulating either of them. -/
private theorem ghost_joint_payload {n q : Nat}
    {ring : DirectedRing n}
    (T : GhostRawTrace n q ring)
    (W : CertificateWord n (compileAdvice q))
    (cut k : Nat)
    (hjoint : GhostTagJointSoundAt T W cut k) :
    GhostTagPayloadSoundAt (T.states k) W := by
  intro site s launch times htag
  obtain ⟨j, ht, _, _, _, _, _, _, _⟩ :=
    hjoint site s launch times htag
  exact ⟨j, ht⟩

private theorem ghost_joint_history {n q : Nat}
    {ring : DirectedRing n}
    (T : GhostRawTrace n q ring)
    (W : CertificateWord n (compileAdvice q))
    (cut k : Nat)
    (hjoint : GhostTagJointSoundAt T W cut k) :
    GhostTagHistorySoundAt T W cut k := by
  intro site s launch times j htag htok
  obtain ⟨j', ht, hsite, hcut, hlaunch, hedge, hrow,
    hreceipts, horder⟩ :=
    hjoint site s launch times htag
  have heq : rawPrefixSample W s j' = rawPrefixSample W s j :=
    Option.some.inj (ht.symm.trans htok)
  have hj : j' = j := by
    have hidx := congrArg
      (fun r : RawTok (compileAdvice q).t => r.jm1) heq
    simpa only [rawPrefixSample] using hidx
  subst j'
  exact ⟨hsite, hcut, hlaunch, hedge, hrow, hreceipts, horder⟩


/-- Preservation across one *real* selected edge. The frozen hypothesis
is on every OLD state through k+1. It supplies both u/beta samples
and native rootlessness; hence postE.eY.l is false. -/
private theorem ghost_joint_step {n q : Nat}
    {ring : DirectedRing n}
    (T : GhostRawTrace n q ring)
    (W : CertificateWord n (compileAdvice q))
    (cut k : Nat)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hcut : cut ≤ k)
    (hfreeze : GhostRawFrozen T W cut (k + 1))
    (hclock : (T.states k).clock = k)
    (hold : GhostTagJointSoundAt T W cut k) :
    GhostTagJointSoundAt T W cut (k + 1) := by
  let c := compileAdvice q
  let G := T.states k
  let e := T.edges k
  let y := ring.rightNeighbor e
  let xOld := G.physical e
  let yOld := G.physical y
  let post := postEInfo xOld yOld
  have hne : e ≠ y :=
    ring_neighbor_distinct ring (by omega : 2 ≤ n) e
  have hOldX := hfreeze k hcut (by omega) e
  have hOldY := hfreeze k hcut (by omega) y
  have hpost : post.eY.l = false :=
    raw_postY_rootless xOld yOld hOldX.2.2 hOldY.2.2
  intro site s launch times hnew
  have hnewStep :
      (ghostRawStep ring G e).marks site =
        .fresh s launch times := by
    simpa only [T.evolves k] using hnew
  by_cases hySite : site = y
  · subst site
    have htarget :
        (ghostRawStep ring G e).marks y =
          ghostResponderTag c xOld yOld post
            (G.marks e) (G.marks y) y G.clock := by
      simp [ghostRawStep, c, y, xOld, yOld, post]
    rw [htarget] at hnewStep
    rw [hclock] at hnewStep
    cases hyTok : yOld.rawTok with
    | some resident =>
        have hkeep : ghostKeepTag (G.marks y) =
            .fresh s launch times := by
          cases hxTok : xOld.rawTok with
          | none =>
              simpa [ghostResponderTag, rawD1Step,
                hxTok, hyTok] using hnewStep
          | some r =>
              simpa [ghostResponderTag, rawD1Step,
                hxTok, hyTok] using hnewStep
        have hmark : G.marks y = .fresh s launch times :=
          ghost_keep_fresh (G.marks y) s launch times hkeep
        have htok :
            ((T.states (k + 1)).physical y).rawTok =
              (G.physical y).rawTok := by
          rw [T.evolves k, ghost_step_target_tok ring G e hne]
          have hy' : (G.physical (ring.rightNeighbor e)).rawTok =
              some resident := hyTok
          cases hxTok : xOld.rawTok with
          | none =>
              have hx' : (G.physical e).rawTok = none := hxTok
              simp [rawD1Step, hx', hy', y]
          | some r =>
              have hx' : (G.physical e).rawTok = some r := hxTok
              simp [rawD1Step, hx', hy', y]
        exact ghost_joint_frame T W cut k hold
          y s launch times hmark htok
    | none =>
        cases hxTok : xOld.rawTok with
        | none =>
            by_cases hkick : yOld.rawKick = true
            · have htagEq :
                  (GhostRawTag.fresh y k (fun _ => none)) =
                    .fresh s launch times := by
                simpa [ghostResponderTag, rawD1Step,
                  hxTok, hyTok, hkick,
                  show 0 < c.t from (by show 0 < (compileAdvice q).t; omega)] using hnewStep
              injection htagEq with hs hl hts
              subst s
              subst launch
              subst times
              have htoken :
                  ((T.states (k + 1)).physical y).rawTok =
                    some (rawPrefixSample W y
                      ⟨0, by omega⟩) := by
                rw [T.evolves k, ghost_step_target_tok ring G e hne]
                exact raw_prefix_launch W y ht xOld yOld post
                  hxTok hyTok hkick hOldY.1 hpost
              have hedge : T.edges k =
                  certSite y (n - 1) :=
                ring_predecessor_certSite ring e
              have hrow :
                  (traceRawResult (ghostTraceReal T) k).row =
                    "R1c" := by
                change (rawD1Step c xOld yOld post).row = "R1c"
                simp [rawD1Step, hxTok, hyTok, hkick]
              refine ⟨⟨0, by omega⟩, htoken,
                (certSite_zero y).symm,
                hcut, by omega, hedge, hrow, ?_, ?_⟩
              · intro i hi
                have hbad : i.val < 0 := hi
                omega
              · intro i h _ hh
                have hbad : h.val < 0 := hh
                omega
            · have hkickFalse : yOld.rawKick = false := by
                cases hb : yOld.rawKick with
                | false => rfl
                | true => exact False.elim (hkick hb)
              have hbad :
                  (GhostRawTag.vacant : GhostRawTag n c.t) =
                    .fresh s launch times := by
                simpa [ghostResponderTag, rawD1Step,
                  hxTok, hyTok, hkickFalse]
                  using hnewStep
              cases hbad
        | some r =>
            by_cases hj : r.j < c.t
            · cases hxMark : G.marks e with
              | vacant =>
                  have hbad :
                      (GhostRawTag.inherited : GhostRawTag n c.t) =
                        .fresh s launch times := by
                    simpa [ghostResponderTag, rawD1Step,
                      hxTok, hyTok, hj, hxMark]
                      using hnewStep
                  cases hbad
              | inherited =>
                  have hbad :
                      (GhostRawTag.inherited : GhostRawTag n c.t) =
                        .fresh s launch times := by
                    simpa [ghostResponderTag, rawD1Step,
                      hxTok, hyTok, hj, hxMark]
                      using hnewStep
                  cases hbad
              | fresh sOld launchOld timesOld =>
                  have htagEq :
                      (GhostRawTag.fresh sOld launchOld
                        (fun i => if i = r.jm1 then
                          some k else timesOld i)) =
                      .fresh s launch times := by
                    simpa [ghostResponderTag, rawD1Step,
                      hxTok, hyTok, hj, hxMark]
                      using hnewStep
                  injection htagEq with hs hl hts
                  subst s
                  subst launch
                  subst times
                  obtain ⟨j, htokOld, hsiteOld, hcutOld,
                    hlaunchOld, hedgeOld, hrowOld,
                    hreceipts, horder⟩ :=
                      hold e sOld launchOld timesOld hxMark
                  have hr : r = rawPrefixSample W sOld j := by
                    apply Option.some.inj
                    exact hxTok.symm.trans htokOld
                  have hindex : r.j = j.val + 1 := by
                    rw [hr]
                    rfl
                  have hjNext : j.val + 1 < c.t := by omega
                  let jNext : Fin c.t := ⟨j.val + 1, hjNext⟩
                  have hsiteY :
                      y = certSite sOld (j.val + 1) := by
                    calc
                      y = ring.rightNeighbor e := rfl
                      _ = ring.rightNeighbor
                            (certSite sOld j.val) := by rw [hsiteOld]
                      _ = certSite sOld (j.val + 1) :=
                            ring_neighbor_certSite ring sOld j.val
                  have hbit :
                      yOld.u =
                        certBit W (certSite sOld (j.val + 1)) := by
                    exact hOldY.1.trans (congrArg (certBit W) hsiteY)
                  have hbeta :
                      yOld.beta =
                        certMarker W (certSite sOld (j.val + 1)) := by
                    exact hOldY.2.1.trans (congrArg (certMarker W) hsiteY)
                  have hxPrefix :
                      xOld.rawTok =
                        some (rawPrefixSample W sOld j) :=
                    hxTok.trans (congrArg some hr)
                  have htokNew :
                      ((T.states (k + 1)).physical y).rawTok =
                        some (rawPrefixSample W sOld jNext) := by
                    rw [T.evolves k, ghost_step_target_tok ring G e hne]
                    exact raw_prefix_forward W sOld j hjNext
                      xOld yOld post hxPrefix hyTok
                      hbit hbeta hpost
                  have htokAtE :
                      ((T.states k).physical
                        (certSite sOld j.val)).rawTok =
                        some (rawPrefixSample W sOld j) := by
                    rw [← hsiteOld]
                    exact htokOld
                  refine ⟨jNext, htokNew, hsiteY, hcutOld,
                    by omega, hedgeOld, hrowOld, ?_, ?_⟩
                  · intro i hi
                    by_cases hiEq : i = j
                    · subst i
                      refine ⟨k, ?_, hlaunchOld, by omega,
                        hsiteOld, htokAtE⟩
                      rw [hr]
                      simp [rawPrefixSample]
                    · have hneqVal : i.val ≠ j.val := by
                        intro heq
                        exact hiEq (Fin.ext heq)
                      have hiOld : i.val < j.val := by
                        change i.val < j.val + 1 at hi
                        omega
                      obtain ⟨service, hstamp, ha, hb, he,
                        hp⟩ := hreceipts i hiOld
                      refine ⟨service, ?_, ha, by omega, he, hp⟩
                      simpa [hr, hiEq, rawPrefixSample] using hstamp
                  · intro i h hih hh
                    by_cases hEq : h = j
                    · subst h
                      obtain ⟨a, ha, _, hbefore, _, _⟩ :=
                        hreceipts i hih
                      have hiNe : i ≠ j := by
                        intro heq
                        subst i
                        omega
                      refine ⟨a, k, ?_, ?_, hbefore⟩
                      · simpa [hr, hiNe, rawPrefixSample] using ha
                      · rw [hr]
                        simp [rawPrefixSample]
                    · have hneqVal : h.val ≠ j.val := by
                        intro heq
                        exact hEq (Fin.ext heq)
                      have hhOld : h.val < j.val := by
                        change h.val < j.val + 1 at hh
                        omega
                      obtain ⟨a, b, ha, hb, hab⟩ :=
                        horder i h hih hhOld
                      have hiNe : i ≠ j := by
                        intro heq
                        subst i
                        omega
                      refine ⟨a, b, ?_, ?_, hab⟩
                      · simpa [hr, hiNe, rawPrefixSample] using ha
                      · simpa [hr, hEq, rawPrefixSample] using hb
            · have hbad :
                  (GhostRawTag.vacant : GhostRawTag n c.t) =
                    .fresh s launch times := by
                simpa [ghostResponderTag, rawD1Step,
                  hxTok, hyTok, hj] using hnewStep
              cases hbad
  · by_cases hxSite : site = e
    · subst site
      have hVacant :
          (ghostRawStep ring G e).marks e = .vacant :=
        ghostRawStep_source_vacant ring G e hne
      rw [hVacant] at hnewStep
      cases hnewStep
    · have hmark :
          G.marks site = .fresh s launch times := by
        have hother := ghostRawStep_other_mark
          ring G e site hxSite hySite
        rw [hother] at hnewStep
        exact hnewStep
      have htok :
          ((T.states (k + 1)).physical site).rawTok =
            ((T.states k).physical site).rawTok := by
        rw [T.evolves k]
        exact ghost_step_other_tok ring G e site hxSite hySite
      exact ghost_joint_frame T W cut k hold site s launch
        times hmark htok

/-- Induct from the actual initialization cut, with frozen old
public data and leaderlessness through the terminal cut. -/
theorem ghost_joint_reached {n q : Nat}
    {ring : DirectedRing n}
    (T : GhostRawTrace n q ring)
    (W : CertificateWord n (compileAdvice q))
    (C : (protocol q).Configuration n)
    (cut stop : Nat)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hinit : T.states cut = ghostRawInit C cut)
    (hfreeze : GhostRawFrozen T W cut stop)
    (k : Nat) (hk : cut ≤ k) (hstop : k ≤ stop) :
    GhostTagJointSoundAt T W cut k := by
  have hind : ∀ d : Nat, cut + d ≤ stop →
      GhostTagJointSoundAt T W cut (cut + d) := by
    intro d
    induction d with
    | zero =>
        intro _
        simpa only [Nat.add_zero] using
          (ghost_joint_init T W C cut hinit)
    | succ d ih =>
        intro hbound
        have hcm : cut ≤ cut + d := by omega
        have hds : cut + d ≤ stop := by omega
        have hfr : GhostRawFrozen T W cut (cut + d + 1) := by
          intro v hcv hvm i
          exact hfreeze v hcv (by omega) i
        have hs := ghost_joint_step T W cut (cut + d)
          ht hn hcm hfr
          (ghost_trace_clock_at T C cut hinit (cut + d) hcm)
          (ih hds)
        simpa only [Nat.add_succ] using hs
  have hre : k = cut + (k - cut) := by omega
  rw [hre]
  exact hind (k - cut) (by omega)

theorem ghost_tag_payload_reached {n q : Nat}
    {ring : DirectedRing n}
    (T : GhostRawTrace n q ring)
    (W : CertificateWord n (compileAdvice q))
    (C : (protocol q).Configuration n)
    (cut stop : Nat)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hinit : T.states cut = ghostRawInit C cut)
    (hfreeze : GhostRawFrozen T W cut stop)
    (k : Nat) (hk : cut ≤ k) (hstop : k ≤ stop) :
    GhostTagPayloadSoundAt (T.states k) W :=
  ghost_joint_payload T W cut k
    (ghost_joint_reached T W C cut stop ht hn
      hinit hfreeze k hk hstop)

theorem ghost_tag_history_reached {n q : Nat}
    {ring : DirectedRing n}
    (T : GhostRawTrace n q ring)
    (W : CertificateWord n (compileAdvice q))
    (C : (protocol q).Configuration n)
    (cut stop : Nat)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hinit : T.states cut = ghostRawInit C cut)
    (hfreeze : GhostRawFrozen T W cut stop)
    (k : Nat) (hk : cut ≤ k) (hstop : k ≤ stop) :
    GhostTagHistorySoundAt T W cut k :=
  ghost_joint_history T W cut k
    (ghost_joint_reached T W C cut stop ht hn
      hinit hfreeze k hk hstop)


/-! ## Request-free entrance and joint-invariant interfaces

The full joint successor proof is still a required separate lemma.
The following basic statements do not assume an unproved closure.
-/

/-- Physical no-request interval used in the frozen first-request
comparison of certificate.tex. An initially rootless native mask
is separately necessary; this predicate alone permits old roots. -/
def GhostRawNoRequests {n q : Nat} {ring : DirectedRing n}
    (T : GhostRawTrace n q ring)
    (start stop : Nat) : Prop :=
  ∀ k, start ≤ k → k ≤ stop →
    ∀ i : Fin n, ((T.states k).physical i).req = false

/-- Without an OLD request at either selected endpoint, even an
arbitrary OLD grant cannot trigger the legacy FIRE birth row. -/
theorem ghost_no_old_request_no_fire {c : Compiled}
    (x y : Agent c) (hx : x.req = false) (hy : y.req = false)
    (ex ey : CertNative) :
    fireSelect x y ex ey = none := by
  simp [fireSelect, hx, hy]

/-- The stronger joint invariant implies both previously exposed
payload and receipt predicates. This does not assert joint closure. -/
theorem ghost_joint_gives_public_soundness {n q : Nat}
    {ring : DirectedRing n}
    (T : GhostRawTrace n q ring)
    (W : CertificateWord n (compileAdvice q))
    (cut k : Nat)
    (hjoint : GhostTagJointSoundAt T W cut k) :
    GhostTagPayloadSoundAt (T.states k) W ∧
      GhostTagHistorySoundAt T W cut k := by
  exact ⟨ghost_joint_payload T W cut k hjoint,
    ghost_joint_history T W cut k hjoint⟩

/-- If the *joint* provenance invariant has actually been proved at
the selected cut, a fresh tagged R0c rejection has an interleaved
real-protocol full-window history, by the prior conditional theorem.
A separate induction is still needed to obtain hjoint from init. -/
theorem ghost_joint_terminal_to_interleaved
    {n q : Nat} {ring : DirectedRing n}
    (T : GhostRawTrace n q ring)
    (W : CertificateWord n (compileAdvice q))
    (s : Fin n) (cut k : Nat)
    (hjoint : GhostTagJointSoundAt T W cut k)
    (h : GhostTaggedTerminal T W s k) :
    InterleavedFreshReject (ghostTraceReal T) W s cut k := by
  exact ghost_tagged_terminal_to_interleaved
    T W s cut k (ghost_joint_history T W cut k hjoint) h


/-! ## Literal single-slot rank and bounded-stage interface

The new results below do not assert an unproved all-scratch
protected-interval rank. A free site can be re-armed by R1b and
refilled by an incoming R0b. The one-site nominated-edge cost is
unconditional; the polynomial complete-window theorem explicitly
exposes the missing whole-window certificate.
-/

/-- One physical raw slot has neither a token nor a launch kick. -/
def GhostSlotClear {n q : Nat}
    (G : GhostRaw n q) (site : Fin n) : Prop :=
  (G.physical site).rawTok = none ∧
    (G.physical site).rawKick = false

/-- This follows from the *actual* L3 protocol's source projection,
not a replacement raw-only transition. Includes n=1, where the
initiator-first branch still gives the source update. -/
theorem ghost_source_slot_clears {n q : Nat}
    (ring : DirectedRing n) (G : GhostRaw n q)
    (e : Fin n) :
    GhostSlotClear (ghostRawStep ring G e) e := by
  let c := compileAdvice q
  let y := ring.rightNeighbor e
  let xOld := G.physical e
  let yOld := G.physical y
  have hp := fresh_raw_pair_projection c xOld yOld
  have hr := raw_source_retires c xOld yOld
    (postEInfo xOld yOld)
  have hstep :
      (protocol q).step ring G.physical e e =
        ((protocol q).transition
          (G.physical e)
          (G.physical (ring.rightNeighbor e))).1 := by
    simp [PopulationProtocol.step]
  have htok :
      ((protocol q).transition
        (G.physical e)
        (G.physical (ring.rightNeighbor e))).1.rawTok = none :=
    hp.1.trans hr.1
  have hkick :
      ((protocol q).transition
        (G.physical e)
        (G.physical (ring.rightNeighbor e))).1.rawKick = false :=
    hp.2.2.1.trans hr.2
  unfold GhostSlotClear
  rw [ghostRawStep_projection, hstep]
  exact ⟨htok, hkick⟩

/-- Rank zero after the nominated outgoing edge clears this site.
Every other successor has rank zero or one. -/
noncomputable def GhostSlotRank {n q : Nat}
    (G : GhostRaw n q) (site : Fin n) : Nat := by
  classical
  exact if GhostSlotClear G site then 0 else 1

theorem ghost_slot_rank_le_one {n q : Nat}
    (G : GhostRaw n q) (site : Fin n) :
    GhostSlotRank G site ≤ 1 := by
  classical
  by_cases h : GhostSlotClear G site
  · simp [GhostSlotRank, h]
  · simp [GhostSlotRank, h]

/-- The first-hit cost for clearing ONE arbitrary physical slot
is ≤ n from every Cartesian ghost state, for every finite horizon.
The nominated edge is the site's own outgoing edge. -/
theorem ghost_slot_clear_cost {n q : Nat}
    (ring : DirectedRing n) (site : Fin n)
    (G : GhostRaw n q) (T : Nat) :
    K2ArbitraryElimination.FiniteAccounting.costNumerator
      (ghostRawStep ring)
      (fun z => GhostSlotClear z site) G T ≤
        n ^ T * n := by
  classical
  let rank : GhostRaw n q → Nat :=
    fun z => GhostSlotRank z site
  let chosen : GhostRaw n q → Fin n := fun _ => site
  have hdrop : ∀ z, ¬ GhostSlotClear z site →
      rank (ghostRawStep ring z (chosen z)) + 1 ≤ rank z := by
    intro z hz
    have hc : GhostSlotClear (ghostRawStep ring z site) site :=
      ghost_source_slot_clears ring z site
    dsimp [rank, chosen]
    simp [GhostSlotRank, hc, hz]
  have hnoninc : ∀ z, ¬ GhostSlotClear z site →
      ∀ e, rank (ghostRawStep ring z e) ≤ rank z := by
    intro z hz e
    dsimp [rank]
    by_cases hc : GhostSlotClear (ghostRawStep ring z e) site
    · simp [GhostSlotRank, hc, hz]
    · simp [GhostSlotRank, hc, hz]
  have hcost := Prob.costNumerator_le_of_nominated_edge
    (ghostRawStep ring)
    (fun z => GhostSlotClear z site)
    rank chosen hdrop hnoninc G T
  calc
    K2ArbitraryElimination.FiniteAccounting.costNumerator
        (ghostRawStep ring) (fun z => GhostSlotClear z site)
        G T ≤ n ^ T * (n * rank G) := hcost
    _ ≤ n ^ T * (n * 1) :=
      Nat.mul_le_mul_left (n ^ T)
        (Nat.mul_le_mul_left n
          (ghost_slot_rank_le_one G site))
    _ = n ^ T * n := by
      rw [Nat.mul_one]

/-- Local obstruction to using the sum of unarmed empty sites as an
all-edges-nonincreasing rank: R1b creates a kick on an empty pair. -/
theorem raw_empty_pair_arms (c : Compiled)
    (x y : Agent c) (post : PostE) :
    (rawD1Step c
      { x with rawTok := none }
      { y with rawTok := none, rawKick := false }
      post).kickY = true := by
  rfl

/-- A future terminal for a false MARKER window: a tagged
genuine post-cut token is at the last sampled source and the
terminal site's physical raw slot is empty. This is a
pre-service state predicate, not an assertion that R0c has
already occurred. -/
def GhostReadyMarker {n q : Nat}
    (G : GhostRaw n q)
    (W : CertificateWord n (compileAdvice q))
    (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t) : Prop :=
  ∃ launch : Nat,
  ∃ times : Fin (compileAdvice q).t → Option Nat,
    G.marks (certSite s ((compileAdvice q).t - 1)) =
      .fresh s launch times ∧
    (G.physical (certSite s ((compileAdvice q).t - 1))).rawTok =
      some (rawPrefixSample W s
        ⟨(compileAdvice q).t - 1, by omega⟩) ∧
    (G.physical (certSite s (compileAdvice q).t)).rawTok =
      none

/-- An absolute segment end, or a physical OLD request.
A clock threshold is a genuine state predicate on GhostRaw;
a request is also physical rather than a post-event ghost tag. -/
def GhostMarkerSegmentStop {n q : Nat}
    (G : GhostRaw n q) (stop : Nat) : Prop :=
  stop ≤ G.clock ∨
    ∃ i : Fin n, (G.physical i).req = true

theorem ghost_no_request_before_segment_stop {n q : Nat}
    {ring : DirectedRing n}
    (Tr : GhostRawTrace n q ring)
    (C : (protocol q).Configuration n)
    (cut stop k : Nat)
    (hinit : Tr.states cut = ghostRawInit C cut)
    (hno : GhostRawNoRequests Tr cut stop)
    (hcut : cut ≤ k) (hk : k < stop) :
    ¬ GhostMarkerSegmentStop (Tr.states k) stop := by
  intro h
  have hclock : (Tr.states k).clock = k :=
    ghost_trace_clock_at Tr C cut hinit k hcut
  rcases h with htime | ⟨i, hreq⟩
  · rw [hclock] at htime
    omega
  · have hf := hno k hcut (by omega) i
    rw [hf] at hreq
    cases hreq

/-! The actual multi-edge progress gap is expressed as a *certificate*
rather than a false claim that a static empty-slot count is monotone.
The fields are precisely those accepted by the compiled nominated-edge
Bellman theorem, and the rank is bounded by a polynomial in t whenever
the launch/forward stage begins with the nominated predecessor clear.
A certificate must be constructed from the literal R0a/R0b/R1b/R1c
rows and any retry observer, not inferred merely from the shape of
this record. -/

/-- Missing physical launch/forward machine certificate.
The rank measures remaining work until ready-or-stop; aborts
or collisions must be accounted for without violating the
all-edge-nonincreasing field. No existence proof is claimed. -/
structure GhostMarkerProgressCert {n q : Nat}
    (ring : DirectedRing n)
    (W : CertificateWord n (compileAdvice q))
    (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (stop : Nat) where
  rank : GhostRaw n q → Nat
  chosen : GhostRaw n q → Fin n
  bound : ∀ G, GhostSlotClear G (certSite s (n - 1)) →
    rank G ≤ ((compileAdvice q).t + 3) ^ 2
  decrease : ∀ G,
    ¬ (GhostReadyMarker G W s ht ∨
      GhostMarkerSegmentStop G stop) →
    rank (ghostRawStep ring G (chosen G)) + 1 ≤ rank G
  nonincrease : ∀ G,
    ¬ (GhostReadyMarker G W s ht ∨
      GhostMarkerSegmentStop G stop) →
    ∀ e, rank (ghostRawStep ring G e) ≤ rank G

/-- Complete, *conditional* two-stage cost calculation.
The first stage is genuinely proved above; the second stage
is precisely the as-yet-unconstructed rank certificate.
The explicit bound B(t)=1+(t+3)^2 is polynomial and n-free,
but is NOT established unconditionally for ghostRawStep. -/
theorem ghost_marker_cost_if_progress_cert {n q : Nat}
    (ring : DirectedRing n)
    (W : CertificateWord n (compileAdvice q))
    (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (stop : Nat)
    (cert : GhostMarkerProgressCert ring W s ht stop)
    (G : GhostRaw n q) (T : Nat) :
    K2ArbitraryElimination.FiniteAccounting.costNumerator
      (ghostRawStep ring)
      (fun z => GhostReadyMarker z W s ht ∨
        GhostMarkerSegmentStop z stop) G T ≤
      n ^ T * (n * (1 + ((compileAdvice q).t + 3) ^ 2)) := by
  let A : GhostRaw n q → Prop :=
    fun z => GhostSlotClear z (certSite s (n - 1))
  let P : GhostRaw n q → Prop :=
    fun z => GhostReadyMarker z W s ht ∨
      GhostMarkerSegmentStop z stop
  let R : Nat := ((compileAdvice q).t + 3) ^ 2
  have hfirst : ∀ k,
      K2ArbitraryElimination.FiniteAccounting.costNumerator
        (ghostRawStep ring) (fun z => A z ∨ P z)
        G k ≤ n ^ k * n := by
    intro k
    calc
      K2ArbitraryElimination.FiniteAccounting.costNumerator
        (ghostRawStep ring) (fun z => A z ∨ P z)
        G k ≤
        K2ArbitraryElimination.FiniteAccounting.costNumerator
          (ghostRawStep ring) A G k :=
          Prob.costNumerator_target_mono
            (ghostRawStep ring) A
            (fun z => A z ∨ P z)
            (fun _ ha => Or.inl ha) G k
      _ ≤ n ^ k * n :=
          ghost_slot_clear_cost ring (certSite s (n - 1)) G k
  have hsecond : ∀ z, A z → ∀ k,
      K2ArbitraryElimination.FiniteAccounting.costNumerator
        (ghostRawStep ring) P z k ≤ n ^ k * (n * R) := by
    intro z hz k
    have hb := Prob.costNumerator_le_of_nominated_edge
      (ghostRawStep ring) P cert.rank cert.chosen
      cert.decrease cert.nonincrease z k
    calc
      K2ArbitraryElimination.FiniteAccounting.costNumerator
        (ghostRawStep ring) P z k ≤
          n ^ k * (n * cert.rank z) := hb
      _ ≤ n ^ k * (n * R) :=
          Nat.mul_le_mul_left (n ^ k)
            (Nat.mul_le_mul_left n (cert.bound z hz))
  have hs := Prob.costNumerator_stage_le
    (ghostRawStep ring) G A P n (n * R)
    hfirst hsecond T
  calc
    K2ArbitraryElimination.FiniteAccounting.costNumerator
        (ghostRawStep ring) P G T ≤
      n ^ T * (n + n * R) := hs
    _ = n ^ T * (n * (1 + R)) := by
      simp only [Nat.mul_add, Nat.mul_one]
    _ = n ^ T * (n * (1 + ((compileAdvice q).t + 3) ^ 2)) := rfl



/-! ## Real tagged forward hit and collision abort

These are *one-service* facts. A nominated outgoing service moves
the fresh token to the next prefix stage if the responder is empty;
otherwise R0a discards the incoming token. The next proof must turn
the possible aborts into a valid renewal-failure count.
-/

/-- One successful R0b service updates both the physical sampled
payload and the ghost provenance on the ACTUAL step. -/
theorem ghost_tagged_forward_when_empty {n q : Nat}
    (ring : DirectedRing n)
    (G : GhostRaw n q)
    (W : CertificateWord n (compileAdvice q))
    (s : Fin n)
    (j : Fin (compileAdvice q).t)
    (hj : j.val + 1 < (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (launch : Nat)
    (times : Fin (compileAdvice q).t → Option Nat)
    (htag : G.marks (certSite s j.val) = .fresh s launch times)
    (htok : (G.physical (certSite s j.val)).rawTok =
      some (rawPrefixSample W s j))
    (hempty : (G.physical (certSite s (j.val + 1))).rawTok =
      none)
    (hbit : (G.physical (certSite s (j.val + 1))).u =
      certBit W (certSite s (j.val + 1)))
    (hbeta : (G.physical (certSite s (j.val + 1))).beta =
      certMarker W (certSite s (j.val + 1)))
    (hrootX : (G.physical (certSite s j.val)).l = false)
    (hrootY : (G.physical (certSite s (j.val + 1))).l = false) :
    let source := certSite s j.val
    let target := certSite s (j.val + 1)
    ((ghostRawStep ring G source).physical target).rawTok =
        some (rawPrefixSample W s ⟨j.val + 1, hj⟩) ∧
    (ghostRawStep ring G source).marks target =
        .fresh s launch
          (fun i => if i = j then some G.clock else times i) := by
  let c := compileAdvice q
  let source := certSite s j.val
  let target := certSite s (j.val + 1)
  have hneighbor : ring.rightNeighbor source = target :=
    ring_neighbor_certSite ring s j.val
  have hdistinct : source ≠ ring.rightNeighbor source :=
    ring_neighbor_distinct ring (by omega : 2 ≤ n) source
  have hemptyY :
      (G.physical (ring.rightNeighbor source)).rawTok = none := by
    rw [hneighbor]
    exact hempty
  have hbitY :
      (G.physical (ring.rightNeighbor source)).u =
        certBit W target := by
    rw [hneighbor]
    exact hbit
  have hbetaY :
      (G.physical (ring.rightNeighbor source)).beta =
        certMarker W target := by
    rw [hneighbor]
    exact hbeta
  have hrootY' :
      (G.physical (ring.rightNeighbor source)).l = false := by
    rw [hneighbor]
    exact hrootY
  have hpost :
      (postEInfo (G.physical source)
        (G.physical (ring.rightNeighbor source))).eY.l =
        false :=
    raw_postY_rootless (G.physical source)
      (G.physical (ring.rightNeighbor source))
      hrootX hrootY'
  have hjraw : (rawPrefixSample W s j).j < c.t := by
    change j.val + 1 < c.t
    exact hj
  have hxTok :
      (G.physical source).rawTok =
        some (rawPrefixSample W s j) := htok
  have hxMark :
      G.marks source = .fresh s launch times := htag
  constructor
  · have hreal :
        ((ghostRawStep ring G source).physical
          (ring.rightNeighbor source)).rawTok =
          some (rawPrefixSample W s ⟨j.val + 1, hj⟩) := by
      rw [ghost_step_target_tok ring G source hdistinct]
      exact raw_prefix_forward W s j hj
        (G.physical source)
        (G.physical (ring.rightNeighbor source))
        (postEInfo (G.physical source)
          (G.physical (ring.rightNeighbor source)))
        hxTok hemptyY hbitY hbetaY hpost
    change ((ghostRawStep ring G source).physical target).rawTok =
      some (rawPrefixSample W s ⟨j.val + 1, hj⟩)
    simpa only [hneighbor] using hreal
  · have htagNext :
        (ghostRawStep ring G source).marks
          (ring.rightNeighbor source) =
          .fresh s launch
            (fun i => if i = j then some G.clock else times i) := by
      have htarget :
          (ghostRawStep ring G source).marks
            (ring.rightNeighbor source) =
          ghostResponderTag c
            (G.physical source)
            (G.physical (ring.rightNeighbor source))
            (postEInfo (G.physical source)
              (G.physical (ring.rightNeighbor source)))
            (G.marks source)
            (G.marks (ring.rightNeighbor source))
            (ring.rightNeighbor source) G.clock := by
        simp [ghostRawStep, c, source]
      rw [htarget]
      simp [ghostResponderTag, rawD1Step,
        hxTok, hemptyY, hjraw, hxMark,
        show (rawPrefixSample W s j).jm1 = j from rfl]
      rfl
    change (ghostRawStep ring G source).marks target =
      .fresh s launch
        (fun i => if i = j then some G.clock else times i)
    simpa only [hneighbor] using htagNext

/-- R0a is a genuine abort of the incoming source. Its source tag
becomes vacant and the occupied responder keeps the resident tag.
Nothing here claims that this abort has a bounded retry count. -/
theorem ghost_collision_retires_source {n q : Nat}
    (ring : DirectedRing n) (G : GhostRaw n q)
    (e : Fin n) (hn : 2 ≤ n)
    (r resident : RawTok (compileAdvice q).t)
    (hx : (G.physical e).rawTok = some r)
    (hy : (G.physical (ring.rightNeighbor e)).rawTok =
      some resident) :
    (ghostRawStep ring G e).marks e = .vacant ∧
    (ghostRawStep ring G e).marks
       (ring.rightNeighbor e) =
      ghostKeepTag (G.marks (ring.rightNeighbor e)) := by
  have hd : e ≠ ring.rightNeighbor e :=
    ring_neighbor_distinct ring hn e
  constructor
  · exact ghostRawStep_source_vacant ring G e hd
  · simp [ghostRawStep, ghostResponderTag,
      rawD1Step, hx, hy]

/-- On a successful R0b transfer the remaining number of forward
services decreases exactly by one. This is the rank arithmetic used
by a labelled attempt; collision must terminate that attempt
rather than recharge this rank. -/
theorem ghost_forward_remaining_decrements (t j : Nat)
    (hj : j + 1 < t) :
    (t - (j + 2)) + 1 = t - (j + 1) := by
  omega



/-! ## Deterministic protected clearing from last services

This is the exact implication needed for the protected t+3 edge
window: outgoing retirement wins over the LAST incoming service.
It remains a *schedule predicate*, not a nonincreasing rank
on current scanner fields. A probability/cost estimate for entering
this schedule predicate is not smuggled into the cost proof.
-/

/-- A nonincident global interaction frames both raw fields at site. -/
theorem ghost_slot_nonincident_preserves {n q : Nat}
    (ring : DirectedRing n) (G : GhostRaw n q)
    (e site : Fin n)
    (hx : site ≠ e)
    (hy : site ≠ ring.rightNeighbor e)
    (hclear : GhostSlotClear G site) :
    GhostSlotClear (ghostRawStep ring G e) site := by
  have hframe :
      (ghostRawStep ring G e).physical site =
        G.physical site := by
    rw [ghostRawStep_projection]
    simp [PopulationProtocol.step, hx, hy]
  unfold GhostSlotClear at hclear ⊢
  rw [hframe]
  exact hclear

/-- After one outgoing service, any later schedule that omits
both incident edges keeps the physical token and kick empty. -/
theorem ghost_slot_clear_without_incidence {n q : Nat}
    {ring : DirectedRing n}
    (Tr : GhostRawTrace n q ring)
    (site : Fin n) (start stop : Nat)
    (hstart : start ≤ stop)
    (hclear : GhostSlotClear (Tr.states start) site)
    (hquiet : ∀ k, start ≤ k → k < stop →
      site ≠ Tr.edges k ∧
      site ≠ ring.rightNeighbor (Tr.edges k)) :
    GhostSlotClear (Tr.states stop) site := by
  have hind : ∀ d, start + d ≤ stop →
      GhostSlotClear (Tr.states (start + d)) site := by
    intro d
    induction d with
    | zero =>
        intro _
        simpa only [Nat.add_zero] using hclear
    | succ d ih =>
        intro hbound
        obtain ⟨hx, hy⟩ :=
          hquiet (start + d) (by omega) (by omega)
        have hp :=
          ghost_slot_nonincident_preserves ring
            (Tr.states (start + d))
            (Tr.edges (start + d)) site hx hy
            (ih (by omega))
        have hs := Tr.evolves (start + d)
        simpa only [Nat.add_succ, hs] using hp
  have htime : stop = start + (stop - start) := by omega
  rw [htime]
  exact hind (stop - start) (by omega)

/-- The final outgoing service clears its site. No later incoming
or outgoing selection occurs through stop. -/
theorem ghost_slot_clear_after_last_outgoing {n q : Nat}
    {ring : DirectedRing n}
    (Tr : GhostRawTrace n q ring)
    (site : Fin n) (last stop : Nat)
    (hlt : last < stop)
    (hout : Tr.edges last = site)
    (hquiet : ∀ k, last < k → k < stop →
      Tr.edges k ≠ site ∧
      ring.rightNeighbor (Tr.edges k) ≠ site) :
    GhostSlotClear (Tr.states stop) site := by
  have hfirst :
      GhostSlotClear (Tr.states (last + 1)) site := by
    rw [Tr.evolves last, hout]
    exact ghost_source_slot_clears ring (Tr.states last) site
  apply ghost_slot_clear_without_incidence
    Tr site (last + 1) stop (by omega) hfirst
  intro k hk hs
  obtain ⟨hx, hy⟩ := hquiet k (by omega) hs
  exact ⟨Ne.symm hx, Ne.symm hy⟩

/-- A later last outgoing service than last incoming service makes
the site empty at the endpoint of the schedule. -/
theorem ghost_slot_clear_after_ordered_last {n q : Nat}
    {ring : DirectedRing n}
    (Tr : GhostRawTrace n q ring)
    (site : Fin n)
    (incoming outgoing stop : Nat)
    (horder : incoming < outgoing)
    (hout : outgoing < stop)
    (he : Tr.edges outgoing = site)
    (houtlast : ∀ k, outgoing < k → k < stop →
      Tr.edges k ≠ site)
    (hinlast : ∀ k, incoming < k → k < stop →
      Tr.edges k ≠ certSite site (n - 1)) :
    GhostSlotClear (Tr.states stop) site := by
  apply ghost_slot_clear_after_last_outgoing
    Tr site outgoing stop hout he
  intro k hk hs
  constructor
  · exact houtlast k hk hs
  · intro hneighbor
    have hpred := ring_predecessor_certSite ring (Tr.edges k)
    have heq : Tr.edges k = certSite site (n - 1) := by
      simpa only [hneighbor] using hpred
    exact hinlast k (by omega) hs heq

/-- Proof-side finite history of the protected physical edge set.
It records the LAST occurrence of each protected edge before stop,
in strictly increasing clockwise order. -/
def GhostProtectedLastOrder {n q : Nat}
    {ring : DirectedRing n}
    (Tr : GhostRawTrace n q ring)
    (s : Fin n) (start stop : Nat) : Prop :=
  ∃ last : Fin ((compileAdvice q).t + 3) → Nat,
    (∀ j : Fin ((compileAdvice q).t + 3),
      start ≤ last j ∧ last j < stop ∧
      Tr.edges (last j) = certSite s (n - 2 + j.val) ∧
      ∀ k, last j < k → k < stop →
        Tr.edges k ≠ certSite s (n - 2 + j.val)) ∧
    (∀ j : Fin ((compileAdvice q).t + 2),
      last ⟨j.val, by omega⟩ <
        last ⟨j.val + 1, by omega⟩)

/-- Every site in the protected t+2 interval is actually empty
at the last-occurrence cut, no matter what inherited token/kick
records the trace had before the schedule. -/
theorem ghost_protected_last_order_clears {n q : Nat}
    {ring : DirectedRing n}
    (Tr : GhostRawTrace n q ring) (s : Fin n)
    (start stop : Nat)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (horder : GhostProtectedLastOrder Tr s start stop) :
    ∀ j : Fin ((compileAdvice q).t + 2),
      GhostSlotClear (Tr.states stop)
        (certSite s (n - 1 + j.val)) := by
  obtain ⟨last, hlast, hsorted⟩ := horder
  intro j
  let prev : Fin ((compileAdvice q).t + 3) :=
    ⟨j.val, by omega⟩
  let curr : Fin ((compileAdvice q).t + 3) :=
    ⟨j.val + 1, by omega⟩
  let site := certSite s (n - 1 + j.val)
  have hmath : n - 2 + (j.val + 1) = n - 1 + j.val := by
    omega
  have houtEq : Tr.edges (last curr) = site := by
    have h := (hlast curr).2.2.1
    change Tr.edges (last curr) =
      certSite s (n - 2 + (j.val + 1)) at h
    simpa only [hmath] using h
  have hneighbor :
      ring.rightNeighbor (certSite s (n - 2 + j.val)) =
        site := by
    have he : n - 2 + j.val + 1 = n - 1 + j.val := by
      omega
    simpa only [he] using
      ring_neighbor_certSite ring s (n - 2 + j.val)
  have hpred :
      certSite s (n - 2 + j.val) =
        certSite site (n - 1) := by
    have h := ring_predecessor_certSite ring
      (certSite s (n - 2 + j.val))
    rw [hneighbor] at h
    exact h
  have hinLast : ∀ k, last prev < k → k < stop →
      Tr.edges k ≠ certSite site (n - 1) := by
    intro k hstart hk heq
    have hprevNo := (hlast prev).2.2.2 k hstart hk
    apply hprevNo
    change Tr.edges k = certSite s (n - 2 + j.val)
    exact heq.trans hpred.symm
  have houtLast : ∀ k, last curr < k → k < stop →
      Tr.edges k ≠ site := by
    intro k hstart hk heq
    have hcurrNo := (hlast curr).2.2.2 k hstart hk
    apply hcurrNo
    change Tr.edges k = certSite s (n - 2 + (j.val + 1))
    rw [hmath]
    exact heq
  exact ghost_slot_clear_after_ordered_last
    Tr site (last prev) (last curr) stop
    (hsorted j) (hlast curr).2.1
    houtEq houtLast hinLast



/-! ## MARKER ready state has an actual terminal R0c report

The sampled prefix is exact by the fold induction.
The following lemma only identifies the OLD-pair report if the
terminal edge is selected. It is not a state-level "already
rejected" target and does not assert a bound on that edge's wait.
-/

theorem ghost_prefix_last_eq_sampled {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n)
    (ht : 2 ≤ c.t) :
    rawPrefixSample W s ⟨c.t - 1, by omega⟩ =
      rawSampledTerminal W s ht := by
  have hindex : c.t - 1 + 1 = c.t := by omega
  simp [rawPrefixSample, rawSampledTerminal,
    rawWindowAny, rawWindowAll, rawWindowParity,
    certWindow, hindex]

/-- The true physical terminal token is the same full sampled
static record as the one in the marker-failure lemma. -/
theorem ghost_ready_marker_sampled {n q : Nat}
    (G : GhostRaw n q)
    (W : CertificateWord n (compileAdvice q))
    (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hready : GhostReadyMarker G W s ht) :
    ∃ launch : Nat,
    ∃ times : Fin (compileAdvice q).t → Option Nat,
      G.marks (certSite s ((compileAdvice q).t - 1)) =
        .fresh s launch times ∧
      (G.physical
        (certSite s ((compileAdvice q).t - 1))).rawTok =
          some (rawSampledTerminal W s ht) ∧
      (G.physical (certSite s (compileAdvice q).t)).rawTok =
        none := by
  obtain ⟨launch, times, hmark, htok, hterm⟩ := hready
  refine ⟨launch, times, hmark, ?_, hterm⟩
  rw [← ghost_prefix_last_eq_sampled W s ht]
  exact htok

/-- A false MARKER relation makes the literal R0c reject
if the selected source and responder have the ready fields.
No rootless post-E guard is needed for a latched marker failure. -/
theorem ghost_ready_marker_report {n q : Nat}
    (G : GhostRaw n q)
    (W : CertificateWord n (compileAdvice q))
    (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hroot : RootlessCertificate W)
    (hbad : ¬ MarkerRelation W s)
    (hready : GhostReadyMarker G W s ht) :
    let c := compileAdvice q
    let x := G.physical (certSite s (c.t - 1))
    let y := G.physical (certSite s c.t)
    (rawD1Step c x y (postEInfo x y)).reject = true := by
  obtain ⟨launch, times, hmark, htok, hempty⟩ :=
    ghost_ready_marker_sampled G W s ht hready
  let c := compileAdvice q
  let x := G.physical (certSite s (c.t - 1))
  let y := G.physical (certSite s c.t)
  let post := postEInfo x y
  let r := rawSampledTerminal W s ht
  have hindex : r.j = c.t :=
    raw_sampled_terminal_index W s ht
  have hnot : ¬ r.j < c.t := by omega
  have hreport :
      (rawD1Step c
        {x with rawTok := some r}
        {y with rawTok := none}
        post).reject = true :=
    raw_sampled_terminal_rejects_marker W s
      ht hroot hbad x y post
  have hxTok : x.rawTok = some r := htok
  have hyTok : y.rawTok = none := hempty
  have hsame :
      (rawD1Step c x y post).reject =
      (rawD1Step c
        {x with rawTok := some r}
        {y with rawTok := none}
        post).reject := by
    simp [rawD1Step, hxTok, hyTok, hnot]
  exact hsame.trans hreport



/-! ## Genuine retry-kernel interface on the real ghost step

This theorem only uses the existing compiled finite-word renewal
calculus. It makes explicit what a collision-tolerant completion
would have to supply: a same-edge RetrySimulation with valid reached
restarts, attempt cost O(n t^2), and retry mass at most one half.
There is no constructed machine-specific kernel or claimed numerical
hazard here.
-/

/-- If a machine-specific attempt kernel and same-scheduler relation
have the stated quantitative receipts, the MARKER ready-or-stop
first-hit cost is bounded by n * 2(t+3)^2. All retries carry
their ACTUAL reached ghost state. -/
theorem ghost_marker_half_retry_if_kernel
    {n q : Nat} {A : Type}
    (ring : DirectedRing n)
    (W : CertificateWord n (compileAdvice q))
    (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (stop : Nat)
    (K : PPL.Convergence.LDLocal.RetryKernel
      A (GhostRaw n q) n)
    (Rel : GhostRaw n q → A → Prop)
    (hsim : Prob.RetrySimulation K (ghostRawStep ring)
      (fun z => GhostReadyMarker z W s ht ∨
        GhostMarkerSegmentStop z stop) Rel)
    (hcost : ∀ seed, K.valid seed → ∀ T,
      K2ArbitraryElimination.FiniteAccounting.costNumerator
        (Prob.attemptStepper K)
        (fun z => Prob.attemptGood z ∨ Prob.attemptFail z)
        (.active (K.start seed)) T ≤
        n ^ T * (n * ((compileAdvice q).t + 3) ^ 2))
    (hfail : ∀ seed, K.valid seed → ∀ T,
      2 * PPL.Convergence.LDLocal.retryCount K
        (.active (K.start seed)) T ≤ n ^ T)
    (G : GhostRaw n q) (seed : GhostRaw n q)
    (hvalid : K.valid seed)
    (hrel : Rel G (K.start seed))
    (T : Nat) :
    K2ArbitraryElimination.FiniteAccounting.costNumerator
      (ghostRawStep ring)
      (fun z => GhostReadyMarker z W s ht ∨
        GhostMarkerSegmentStop z stop) G T ≤
      n ^ T * (n * (2 * ((compileAdvice q).t + 3) ^ 2)) := by
  let B : Nat := n * ((compileAdvice q).t + 3) ^ 2
  have hfail' : ∀ z, K.valid z → ∀ k,
      2 * PPL.Convergence.LDLocal.retryCount K
        (.active (K.start z)) k ≤ 1 * n ^ k := by
    intro z hz k
    simpa only [Nat.one_mul] using hfail z hz k
  have hc := Prob.costNumerator_renewal_le
    (ghostRawStep ring)
    (fun z => GhostReadyMarker z W s ht ∨
      GhostMarkerSegmentStop z stop)
    K Rel hsim B 1 2 (by decide)
    hcost hfail' G seed hvalid hrel T
  have hceil : Prob.renewalCeiling B 1 2 =
      n * (2 * ((compileAdvice q).t + 3) ^ 2) := by
    change (B * 2 / 1 +
      (if B * 2 % 1 = 0 then 0 else 1)) =
        n * (2 * ((compileAdvice q).t + 3) ^ 2)
    rw [Nat.div_one, Nat.mod_one]
    simp only [if_pos rfl, Nat.add_zero]
    dsimp [B]
    ac_rfl
  simpa only [hceil] using hc



/-! ## Legal nonempty MARKER-failure controls

These states inhabit the complete Agent alphabet, not a surrogate
raw-only machine. The single beta mismatch is intentionally public.
The finite checks are at the two requested production widths.
-/

/-- All-zero public u with one deliberately wrong last-sample
marker. Every native and non-public component comes from a
legal blank agent. -/
def ghostMarkerBadInit (n q : Nat) (s : Fin n) :
    (protocol q).Configuration n :=
  fun i =>
    { Agent.blank (compileAdvice q) with
      beta := decide
        (i = certSite s ((compileAdvice q).t - 1)) }

/-- Exact static projection of that legal Cartesian state. -/
def ghostMarkerBadWord (n q : Nat) (s : Fin n) :
    CertificateWord n (compileAdvice q) :=
  certificateWordOfAgents (compileAdvice q)
    (ghostMarkerBadInit n q s)

theorem ghost_marker_bad_init_rootless (n q : Nat)
    (s : Fin n) :
    RootlessCertificate (ghostMarkerBadWord n q s) := by
  intro i
  rfl

theorem ghost_marker_bad_init_no_request (n q : Nat)
    (s : Fin n) :
    ∀ i : Fin n, (ghostMarkerBadInit n q s i).req = false := by
  intro i
  rfl

/-- Nonempty t=2, n=16 production control. -/
theorem ghost_marker_bad_control_sixteen :
    (compileAdvice 4).t = 2 ∧
      ¬ MarkerRelation
        (ghostMarkerBadWord 16 4 (0 : Fin 16))
        (0 : Fin 16) := by
  constructor
  · decide +kernel
  · intro h
    have harc : certFollowerArc
        (ghostMarkerBadWord 16 4 (0 : Fin 16))
        (0 : Fin 16) (compileAdvice 4).t := by
      intro i
      exact ghost_marker_bad_init_rootless 16 4
        (0 : Fin 16) (certSite (0 : Fin 16) i.val)
    have hneq :
        certMarker
          (ghostMarkerBadWord 16 4 (0 : Fin 16))
          (certSite (0 : Fin 16) ((compileAdvice 4).t - 1)) ≠
        Fin.foldl (compileAdvice 4).t
          (fun acc j => acc &&
            certWindow (ghostMarkerBadWord 16 4 (0 : Fin 16))
              (0 : Fin 16) j) true := by
      decide +kernel
    exact hneq (h harc)

/-- Nonempty t=3, n=17 production control. -/
theorem ghost_marker_bad_control_seventeen :
    (compileAdvice 5).t = 3 ∧
      ¬ MarkerRelation
        (ghostMarkerBadWord 17 5 (0 : Fin 17))
        (0 : Fin 17) := by
  constructor
  · decide +kernel
  · intro h
    have harc : certFollowerArc
        (ghostMarkerBadWord 17 5 (0 : Fin 17))
        (0 : Fin 17) (compileAdvice 5).t := by
      intro i
      exact ghost_marker_bad_init_rootless 17 5
        (0 : Fin 17) (certSite (0 : Fin 17) i.val)
    have hneq :
        certMarker
          (ghostMarkerBadWord 17 5 (0 : Fin 17))
          (certSite (0 : Fin 17) ((compileAdvice 5).t - 1)) ≠
        Fin.foldl (compileAdvice 5).t
          (fun acc j => acc &&
            certWindow (ghostMarkerBadWord 17 5 (0 : Fin 17))
              (0 : Fin 17) j) true := by
      decide +kernel
    exact hneq (h harc)


end L3

set_option autoImplicit false
set_option Elab.async false

namespace L3
namespace FreshReference

/-!
## The frozen reference process

The physical transition is the literal protocol transition followed
by restoration of the frozen public and native fields at the selected
endpoints. Scanner slots and kick bits are not restored. Frozen is
closed under every edge; there is no trajectory conditioning.
-/

/-- Restore precisely the fixed public bits and native record. -/
def restore {c : Compiled}
    (fixed current : Agent c) : Agent c :=
  { current with
    u := fixed.u
    beta := fixed.beta
    l := fixed.l
    b := fixed.b
    sh := fixed.sh
    sg := fixed.sg }

/-- The fields frozen in the reference experiment. -/
def data {c : Compiled} (a : Agent c) :
    Bool × Bool × CertNative :=
  (a.u, a.beta, a.certNative)

theorem restore_data {c : Compiled}
    (fixed current : Agent c) :
    data (restore fixed current) = data fixed := by
  rfl

theorem restore_raw {c : Compiled}
    (fixed current : Agent c) :
    (restore fixed current).rawTok = current.rawTok ∧
      (restore fixed current).rawKick = current.rawKick := by
  exact ⟨rfl, rfl⟩

/-- Other fields, including scanner scratch, remain unrestricted. -/
def Frozen {n q : Nat}
    (fixed C : (protocol q).Configuration n) : Prop :=
  ∀ i : Fin n, data (C i) = data (fixed i)

/-- Literal protocol interaction, then endpoint restoration. -/
def step {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (e : Fin n) : (protocol q).Configuration n :=
  let next := (protocol q).step ring C e
  fun i =>
    if i = e then restore (fixed i) (next i)
    else if i = ring.rightNeighbor e then
      restore (fixed i) (next i)
    else next i

theorem step_source {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (e : Fin n) :
    step ring fixed C e e =
      restore (fixed e)
        (transition (compileAdvice q)
          (C e) (C (ring.rightNeighbor e))).1 := by
  simp [step, PopulationProtocol.step, protocol]

theorem step_target {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    step ring fixed C e (ring.rightNeighbor e) =
      restore (fixed (ring.rightNeighbor e))
        (transition (compileAdvice q)
          (C e) (C (ring.rightNeighbor e))).2 := by
  simp [step, PopulationProtocol.step, protocol, hne]

theorem other {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (e i : Fin n)
    (hi : i ≠ e)
    (hj : i ≠ ring.rightNeighbor e) :
    step ring fixed C e i = C i := by
  simp [step, PopulationProtocol.step, hi, hj]

theorem step_endpoint_eq {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (e i : Fin n)
    (hij : i = e ∨ i = ring.rightNeighbor e) :
    step ring fixed C e i =
      restore (fixed i) ((protocol q).step ring C e i) := by
  show (if i = e then restore (fixed i) ((protocol q).step ring C e i)
      else if i = ring.rightNeighbor e then
        restore (fixed i) ((protocol q).step ring C e i)
      else (protocol q).step ring C e i) = _
  by_cases h : i = e
  · exact if_pos h
  · rcases hij with h' | h'
    · exact absurd h' h
    · exact (if_neg h).trans (if_pos h')

/-- One-step projection from the same OLD configuration; not a
claim that real and reference multi-step trajectories coincide. -/
theorem step_raw_projection {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (e i : Fin n) :
    (step ring fixed C e i).rawTok =
        ((protocol q).step ring C e i).rawTok ∧
      (step ring fixed C e i).rawKick =
        ((protocol q).step ring C e i).rawKick := by
  by_cases hi : i = e
  · rw [step_endpoint_eq ring fixed C e i (Or.inl hi)]
    exact restore_raw (fixed i) ((protocol q).step ring C e i)
  · by_cases hj : i = ring.rightNeighbor e
    · rw [step_endpoint_eq ring fixed C e i (Or.inr hj)]
      exact restore_raw (fixed i) ((protocol q).step ring C e i)
    · simp [step, hi, hj]

theorem source_clears {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (e : Fin n) :
    (step ring fixed C e e).rawTok = none ∧
      (step ring fixed C e e).rawKick = false := by
  have hp := fresh_raw_pair_projection (compileAdvice q)
    (C e) (C (ring.rightNeighbor e))
  have hr := raw_source_retires (compileAdvice q)
    (C e) (C (ring.rightNeighbor e))
    (postEInfo (C e) (C (ring.rightNeighbor e)))
  rw [step_source]
  exact ⟨hp.1.trans hr.1, hp.2.2.1.trans hr.2⟩

theorem target_raw {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    (step ring fixed C e (ring.rightNeighbor e)).rawTok =
        (rawD1Step (compileAdvice q)
          (C e) (C (ring.rightNeighbor e))
          (postEInfo (C e) (C (ring.rightNeighbor e)))).tokY ∧
      (step ring fixed C e (ring.rightNeighbor e)).rawKick =
        (rawD1Step (compileAdvice q)
          (C e) (C (ring.rightNeighbor e))
          (postEInfo (C e) (C (ring.rightNeighbor e)))).kickY := by
  have hp := fresh_raw_pair_projection (compileAdvice q)
    (C e) (C (ring.rightNeighbor e))
  rw [step_target ring fixed C e hne]
  exact ⟨hp.2.1, hp.2.2.2⟩

theorem step_frozen {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (hC : Frozen fixed C)
    (e : Fin n) :
    Frozen fixed (step ring fixed C e) := by
  intro i
  by_cases hi : i = e
  · rw [step_endpoint_eq ring fixed C e i (Or.inl hi)]
    try exact restore_data (fixed i) ((protocol q).step ring C e i)
  · by_cases hj : i = ring.rightNeighbor e
    · rw [step_endpoint_eq ring fixed C e i (Or.inr hj)]
      try exact restore_data (fixed i) ((protocol q).step ring C e i)
    · rw [other ring fixed C e i hi hj]
      exact hC i

theorem frozen_fields {n q : Nat}
    (fixed C : (protocol q).Configuration n)
    (hC : Frozen fixed C)
    (i : Fin n) :
    (C i).u = (fixed i).u ∧
      (C i).beta = (fixed i).beta ∧
      (C i).certNative = (fixed i).certNative := by
  have hu := congrArg
    (fun z : Bool × Bool × CertNative => z.1) (hC i)
  have hb := congrArg
    (fun z : Bool × Bool × CertNative => z.2.1) (hC i)
  have hn := congrArg
    (fun z : Bool × Bool × CertNative => z.2.2) (hC i)
  exact ⟨hu, hb, hn⟩

theorem frozen_rootless {n q : Nat}
    (fixed C : (protocol q).Configuration n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hC : Frozen fixed C)
    (i : Fin n) :
    (C i).l = false := by
  have hn := (frozen_fields fixed C hC i).2.2
  have hl := congrArg CertNative.l hn
  exact hl.trans (hroot i)

theorem postY_rootless {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hC : Frozen fixed C)
    (e : Fin n) :
    (postEInfo (C e) (C (ring.rightNeighbor e))).eY.l =
      false := by
  exact raw_postY_rootless
    (C e) (C (ring.rightNeighbor e))
    (frozen_rootless fixed C hroot hC e)
    (frozen_rootless fixed C hroot hC (ring.rightNeighbor e))

def init {n q : Nat}
    (fixed : (protocol q).Configuration n)
    (tokens : Fin n → Option (RawTok (compileAdvice q).t))
    (kicks : Fin n → Bool) : (protocol q).Configuration n :=
  fun i =>
    { fixed i with rawTok := tokens i, rawKick := kicks i }

theorem init_frozen {n q : Nat}
    (fixed : (protocol q).Configuration n)
    (tokens : Fin n → Option (RawTok (compileAdvice q).t))
    (kicks : Fin n → Bool) :
    Frozen fixed (init fixed tokens kicks) := by
  intro i
  rfl

theorem init_raw {n q : Nat}
    (fixed : (protocol q).Configuration n)
    (tokens : Fin n → Option (RawTok (compileAdvice q).t))
    (kicks : Fin n → Bool)
    (i : Fin n) :
    (init fixed tokens kicks i).rawTok = tokens i ∧
      (init fixed tokens kicks i).rawKick = kicks i := by
  exact ⟨rfl, rfl⟩

abbrev State {n q : Nat}
    (fixed : (protocol q).Configuration n) :=
  { C : (protocol q).Configuration n // Frozen fixed C }

def closedStep {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (C : State fixed)
    (e : Fin n) : State fixed :=
  ⟨step ring fixed C.val e,
    step_frozen ring fixed C.val C.property e⟩

theorem closedStep_projection {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (C : State fixed)
    (e : Fin n) :
    (closedStep ring fixed C e).val =
      step ring fixed C.val e := by
  rfl

end FreshReference
end L3


namespace L3
namespace FreshReference

/-! ## Deterministic clearing for every finite edge word -/

def finitePrefix {n len : Nat}
    (word : Fin (len + 1) → Fin n) : Fin len → Fin n :=
  fun i => word ⟨i.val, by omega⟩

def finiteLast {n len : Nat}
    (word : Fin (len + 1) → Fin n) : Fin n :=
  word ⟨len, by omega⟩

/-- Chronological execution of a finite word. -/
def finiteRun {S : Type} {n : Nat}
    (next : S → Fin n → S) (initial : S) :
    (len : Nat) → (Fin len → Fin n) → S
  | 0, _ => initial
  | len + 1, word =>
      next
        (finiteRun next initial len (finitePrefix word))
        (finiteLast word)

/-- Induction over the entire finite word, removing its last letter. -/
theorem finiteRun_last_service_clears
    {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (clear : S → Fin n → Prop)
    (neighbor : Fin n → Fin n)
    (hsource : ∀ C e, clear (next C e) e)
    (hframe : ∀ C e site,
      site ≠ e →
      site ≠ neighbor e →
      clear C site →
      clear (next C e) site)
    (initial : S) :
    ∀ (len : Nat) (word : Fin len → Fin n)
      (site : Fin n) (outgoing : Fin len),
      word outgoing = site →
      (∀ k : Fin len, outgoing.val < k.val →
        word k ≠ site ∧ neighbor (word k) ≠ site) →
      clear (finiteRun next initial len word) site := by
  intro len
  induction len with
  | zero =>
      intro word site outgoing
      exact Fin.elim0 outgoing
  | succ len ih =>
      intro word site outgoing hselected hquiet
      let last : Fin (len + 1) := ⟨len, by omega⟩
      by_cases hend : outgoing.val = len
      · have heq : outgoing = last := by
          apply Fin.ext
          exact hend
        have hlastSelected : finiteLast word = site := by
          change word last = site
          rw [← heq]
          exact hselected
        change clear
          (next
            (finiteRun next initial len (finitePrefix word))
            (finiteLast word)) site
        rw [hlastSelected]
        exact hsource
          (finiteRun next initial len (finitePrefix word)) site
      · have hout : outgoing.val < len := by
          have hbound := outgoing.isLt
          omega
        let prior : Fin len := ⟨outgoing.val, hout⟩
        have hpriorSelected :
            finitePrefix word prior = site := by
          exact hselected
        have hpriorQuiet :
            ∀ k : Fin len, prior.val < k.val →
              finitePrefix word k ≠ site ∧
                neighbor (finitePrefix word k) ≠ site := by
          intro k hk
          exact hquiet ⟨k.val, by omega⟩ hk
        have hclear :
            clear
              (finiteRun next initial len (finitePrefix word))
              site :=
          ih (finitePrefix word) site prior
            hpriorSelected hpriorQuiet
        have hlastAfter : outgoing.val < last.val := by
          change outgoing.val < len
          exact hout
        obtain ⟨hx, hy⟩ := hquiet last hlastAfter
        change clear
          (next
            (finiteRun next initial len (finitePrefix word))
            (finiteLast word)) site
        exact hframe
          (finiteRun next initial len (finitePrefix word))
          (finiteLast word) site
          (Ne.symm hx) (Ne.symm hy) hclear

def SlotClear {n q : Nat}
    (C : (protocol q).Configuration n) (site : Fin n) : Prop :=
  (C site).rawTok = none ∧ (C site).rawKick = false

/-- Presence and actual last positions of all protected edges.
This predicate depends only on the scheduler word. -/
def ProtectedLastOrder {n q len : Nat}
    (s : Fin n) (word : Fin len → Fin n) : Prop :=
  ∃ last : Fin ((compileAdvice q).t + 3) → Fin len,
    (∀ j : Fin ((compileAdvice q).t + 3),
      word (last j) = certSite s (n - 2 + j.val) ∧
      ∀ k : Fin len, (last j).val < k.val →
        word k ≠ certSite s (n - 2 + j.val)) ∧
    (∀ j : Fin ((compileAdvice q).t + 2),
      (last ⟨j.val, by omega⟩).val <
        (last ⟨j.val + 1, by omega⟩).val)

/-- Exact paper clearing implication, uniform over initial scratch.
The t+2 cleared sites are s-1,...,s+t; s-2 is the boundary site. -/
theorem protected_last_order_clears
    {n q len : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (s : Fin n) (word : Fin len → Fin n)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (horder : ProtectedLastOrder (q := q) s word) :
    ∀ j : Fin ((compileAdvice q).t + 2),
      SlotClear
        (finiteRun (step ring fixed) C len word)
        (certSite s (n - 1 + j.val)) := by
  obtain ⟨last, hlast, hsorted⟩ := horder
  intro j
  let prev : Fin ((compileAdvice q).t + 3) :=
    ⟨j.val, by omega⟩
  let curr : Fin ((compileAdvice q).t + 3) :=
    ⟨j.val + 1, by omega⟩
  let site := certSite s (n - 1 + j.val)
  have hmath :
      n - 2 + (j.val + 1) = n - 1 + j.val := by
    omega
  have houtEq : word (last curr) = site := by
    have h := (hlast curr).1
    change word (last curr) =
      certSite s (n - 2 + (j.val + 1)) at h
    simpa only [hmath] using h
  have hneighbor :
      ring.rightNeighbor
          (certSite s (n - 2 + j.val)) = site := by
    have he :
        n - 2 + j.val + 1 = n - 1 + j.val := by
      omega
    simpa only [he] using
      ring_neighbor_certSite ring s (n - 2 + j.val)
  have hpred :
      certSite s (n - 2 + j.val) =
        certSite site (n - 1) := by
    have h := ring_predecessor_certSite ring
      (certSite s (n - 2 + j.val))
    rw [hneighbor] at h
    exact h
  have hquiet :
      ∀ k : Fin len, (last curr).val < k.val →
        word k ≠ site ∧
          ring.rightNeighbor (word k) ≠ site := by
    intro k hk
    constructor
    · intro heq
      have hno := (hlast curr).2 k hk
      apply hno
      change word k =
        certSite s (n - 2 + (j.val + 1))
      rw [hmath]
      exact heq
    · intro heq
      have hbefore :
          (last prev).val < (last curr).val :=
        hsorted j
      have hno := (hlast prev).2 k (by omega)
      have hback := ring_predecessor_certSite ring (word k)
      rw [heq] at hback
      apply hno
      change word k = certSite s (n - 2 + j.val)
      exact hback.trans hpred.symm
  apply finiteRun_last_service_clears
    (step ring fixed) SlotClear ring.rightNeighbor
    (fun D e => source_clears ring fixed D e)
    (fun D e i hi hj hc => ?_)
    C len word site (last curr) houtEq hquiet
  unfold SlotClear at hc ⊢
  rw [other ring fixed D e i hi hj]
  exact hc

end FreshReference
end L3


namespace L3
namespace FreshReference

/-! ## All three static failures imply the literal report -/

private theorem fold_or_false (k : Nat) :
    ∀ (f : Fin k → Bool),
      (∀ i : Fin k, f i = false) →
        Fin.foldl k (fun a i => a || f i) false = false := by
  induction k with
  | zero =>
      intro f hf
      rfl
  | succ k ih =>
      intro f hf
      rw [Fin.foldl_succ, hf 0]
      exact ih (fun i => f i.succ) (fun i => hf i.succ)

theorem nonzero_bad_any_false {n : Nat} {c : Compiled}
    (W : CertificateWord n c)
    (s : Fin n)
    (hbad : ¬ NonzeroRelation W s) :
    rawWindowAny W s = false := by
  have hall : ∀ j : Fin c.t, certWindow W s j = false := by
    intro j
    cases hj : certWindow W s j with
    | false =>
        rfl
    | true =>
        exact False.elim
          (hbad (by
            intro _
            exact ⟨j, hj⟩))
  exact fold_or_false c.t (certWindow W s) hall

theorem recurrence_of_terminal_eq {n : Nat} {c : Compiled}
    (W : CertificateWord n c)
    (s : Fin n)
    (hterminal :
      certBit W (certSite s c.t) = rawWindowParity W s) :
    RecurrenceRelation W s := by
  intro _
  funext j
  change certBit W (certSite (certSite s 1) j.val) =
    (if h : j.val + 1 < c.t then
       certWindow W s ⟨j.val + 1, h⟩
     else rawWindowParity W s)
  rw [certSite_add]
  by_cases hj : j.val + 1 < c.t
  · rw [dif_pos hj]
    change certBit W (certSite s (1 + j.val)) =
      certBit W (certSite s (j.val + 1))
    rw [Nat.add_comm 1 j.val]
  · have hlast : 1 + j.val = c.t := by
      have hbound := j.isLt
      omega
    simpa only [dif_neg hj, hlast] using hterminal

theorem recurrence_bad_terminal_ne {n : Nat} {c : Compiled}
    (W : CertificateWord n c)
    (s : Fin n)
    (hbad : ¬ RecurrenceRelation W s) :
    certBit W (certSite s c.t) ≠ rawWindowParity W s := by
  intro heq
  exact hbad (recurrence_of_terminal_eq W s heq)

/-- Exact actual-pair R0c rejection once the genuine sampled token
is at its final source and the terminal target is empty. -/
theorem sampled_bad_pair_rejects {n : Nat} {c : Compiled}
    (W : CertificateWord n c)
    (s : Fin n)
    (ht : 2 ≤ c.t)
    (hroot : RootlessCertificate W)
    (hbad :
      ¬ NonzeroRelation W s ∨
        ¬ RecurrenceRelation W s ∨
        ¬ MarkerRelation W s)
    (x y : Agent c)
    (hxTok : x.rawTok = some (rawSampledTerminal W s ht))
    (hyTok : y.rawTok = none)
    (hyBit : y.u = certBit W (certSite s c.t))
    (hxRoot : x.l = false)
    (hyRoot : y.l = false) :
    (rawD1Step c x y (postEInfo x y)).reject = true := by
  let post := postEInfo x y
  let r := rawSampledTerminal W s ht
  have hpost : post.eY.l = false :=
    raw_postY_rootless x y hxRoot hyRoot
  have hindex : r.j = c.t :=
    raw_sampled_terminal_index W s ht
  have hnot : ¬ r.j < c.t := by
    omega
  have hreport :
      (rawD1Step c
        {x with rawTok := some r}
        {y with rawTok := none} post).reject = true := by
    rcases hbad with hzero | hrec | hmarker
    · exact raw_sampled_terminal_rejects_lower W s ht x y
        post hpost
        (Or.inl (nonzero_bad_any_false W s hzero))
    · have hne :
          y.u ≠ rawWindowParity W s := by
        intro heq
        exact recurrence_bad_terminal_ne W s hrec
          (hyBit.symm.trans heq)
      exact raw_sampled_terminal_rejects_lower W s ht x y
        post hpost (Or.inr hne)
    · exact raw_sampled_terminal_rejects_marker W s ht
        hroot hmarker x y post
  have hx : x.rawTok = some r := hxTok
  have hsame :
      (rawD1Step c x y post).reject =
        (rawD1Step c
          {x with rawTok := some r}
          {y with rawTok := none} post).reject := by
    simp [rawD1Step, hx, hyTok, hnot]
  exact hsame.trans hreport

end FreshReference
end L3


namespace L3
namespace FreshReference

/-! ## The two monitored launch marks -/

def runList {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (word : List (Fin n)) : (protocol q).Configuration n :=
  word.foldl (step ring fixed) C

theorem runList_nil {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n) :
    runList ring fixed C [] = C := rfl

theorem runList_cons {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (e : Fin n) (word : List (Fin n)) :
    runList ring fixed C (e :: word) =
      runList ring fixed (step ring fixed C e) word := rfl

theorem runList_append {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (left right : List (Fin n)) :
    runList ring fixed C (left ++ right) =
      runList ring fixed
        (runList ring fixed C left) right := by
  simp only [runList, List.foldl_append]

theorem runList_preserves {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (P : (protocol q).Configuration n → Prop)
    (allowed : Fin n → Prop)
    (hstep : ∀ D, P D → ∀ e, allowed e →
      P (step ring fixed D e))
    (word : List (Fin n))
    (C : (protocol q).Configuration n)
    (hC : P C)
    (hword : ∀ e, e ∈ word → allowed e) :
    P (runList ring fixed C word) := by
  induction word generalizing C with
  | nil =>
      exact hC
  | cons e tail ih =>
      exact ih (step ring fixed C e)
        (hstep C hC e (hword e (by simp)))
        (by
          intro f hf
          exact hword f (by simp [hf]))

theorem runList_frozen {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (word : List (Fin n))
    (hC : Frozen fixed C) :
    Frozen fixed (runList ring fixed C word) := by
  apply runList_preserves ring fixed
    (Frozen fixed) (fun _ => True)
    (fun D hD e _ => step_frozen ring fixed D hD e)
    word C hC
  intro e he
  trivial

theorem site_offset_injective {n : Nat}
    (s : Fin n) (a b : Nat)
    (ha : a < n) (hb : b < n)
    (heq : certSite s a = certSite s b) :
    a = b := by
  have hv := congrArg Fin.val heq
  change (s.val + a) % n = (s.val + b) % n at hv
  have hs := s.isLt
  by_cases hsmallA : s.val + a < n
  · rw [Nat.mod_eq_of_lt hsmallA] at hv
    by_cases hsmallB : s.val + b < n
    · rw [Nat.mod_eq_of_lt hsmallB] at hv
      omega
    · have hge : n ≤ s.val + b := by omega
      have hlt : s.val + b - n < n := by omega
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt] at hv
      omega
  · have hge : n ≤ s.val + a := by omega
    have hlt : s.val + a - n < n := by omega
    have hred : (s.val + a) % n = s.val + a - n := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
    rw [hred] at hv
    by_cases hsmallB : s.val + b < n
    · rw [Nat.mod_eq_of_lt hsmallB] at hv
      omega
    · have hgeB : n ≤ s.val + b := by omega
      have hltB : s.val + b - n < n := by omega
      rw [Nat.mod_eq_sub_mod hgeB, Nat.mod_eq_of_lt hltB] at hv
      omega

theorem site_add_cycle {n : Nat}
    (s : Fin n) (k : Nat) :
    certSite s (n + k) = certSite s k := by
  rw [← certSite_add, certSite_n]

theorem clear_of_no_incoming {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (e site : Fin n)
    (hc : SlotClear C site)
    (hy : site ≠ ring.rightNeighbor e) :
    SlotClear (step ring fixed C e) site := by
  by_cases hx : site = e
  · subst site
    exact source_clears ring fixed C e
  · unfold SlotClear at hc ⊢
    rw [other ring fixed C e site hx hy]
    exact hc

theorem excluded_incoming {n : Nat}
    (ring : DirectedRing n)
    (A : Fin n → Prop)
    (e before site : Fin n)
    (he : ¬ A e)
    (hbefore : A before)
    (hnext : ring.rightNeighbor before = site) :
    site ≠ ring.rightNeighbor e := by
  intro hsite
  have heBack := ring_predecessor_certSite ring e
  have hbBack := ring_predecessor_certSite ring before
  rw [← hsite] at heBack
  rw [hnext] at hbBack
  have heq : e = before := heBack.trans hbBack.symm
  apply he
  rw [heq]
  exact hbefore

/-- The t+2 launch edges e_(s-2),...,e_(s+t-1). -/
def LaunchEdge {n q : Nat}
    (s e : Fin n) : Prop :=
  ∃ j : Fin ((compileAdvice q).t + 2),
    e = certSite s (n - 2 + j.val)

theorem launchEdge_before {n q : Nat}
    (s : Fin n) :
    LaunchEdge (q := q) s (certSite s (n - 2)) := by
  exact ⟨⟨0, by omega⟩, rfl⟩

theorem launchEdge_launch {n q : Nat}
    (s : Fin n) (hn : 2 ≤ n) :
    LaunchEdge (q := q) s (certSite s (n - 1)) := by
  refine ⟨⟨1, by omega⟩, ?_⟩
  have h : n - 2 + 1 = n - 1 := by omega
  rw [h]

theorem launchEdge_sampled {n q : Nat}
    (s : Fin n) (hn : 2 ≤ n)
    (j : Fin (compileAdvice q).t) :
    LaunchEdge (q := q) s (certSite s j.val) := by
  refine ⟨⟨j.val + 2, by omega⟩, ?_⟩
  have h : n - 2 + (j.val + 2) = n + j.val := by omega
  rw [h, site_add_cycle]

theorem launch_neighbor {n : Nat}
    (ring : DirectedRing n)
    (s : Fin n) (hn : 2 ≤ n) :
    ring.rightNeighbor (certSite s (n - 1)) = s := by
  have h : n - 1 + 1 = n := by omega
  simpa only [h, certSite_n] using
    ring_neighbor_certSite ring s (n - 1)

def ForwardClear {n q : Nat}
    (C : (protocol q).Configuration n) (s : Fin n) : Prop :=
  ∀ j : Fin (compileAdvice q).t,
    SlotClear C (certSite s (j.val + 1))

def LaunchScratch {n q : Nat}
    (C : (protocol q).Configuration n)
    (s : Fin n) (kick : Bool) : Prop :=
  SlotClear C (certSite s (n - 1)) ∧
  (C s).rawTok = none ∧
  (C s).rawKick = kick ∧
  ForwardClear C s

theorem launch_outside_step {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (s e : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (he : ¬ LaunchEdge (q := q) s e) :
    step ring fixed C e (certSite s (n - 1)) =
        C (certSite s (n - 1)) ∧
    step ring fixed C e s = C s ∧
    (ForwardClear C s →
      ForwardClear (step ring fixed C e) s) := by
  have hxMem := launchEdge_launch (q := q) s (by omega)
  have hsMem : LaunchEdge (q := q) s s := by
    simpa only [certSite_zero] using
      launchEdge_sampled (q := q) s (by omega)
        (⟨0, by omega⟩ : Fin (compileAdvice q).t)
  have hx : certSite s (n - 1) ≠ e := by
    intro h
    exact he (h ▸ hxMem)
  have hs : s ≠ e := by
    intro h
    exact he (h ▸ hsMem)
  have hbeforeNext :
      ring.rightNeighbor (certSite s (n - 2)) =
        certSite s (n - 1) := by
    have h : n - 2 + 1 = n - 1 := by omega
    simpa only [h] using
      ring_neighbor_certSite ring s (n - 2)
  have hxIn :
      certSite s (n - 1) ≠ ring.rightNeighbor e :=
    excluded_incoming ring
      (LaunchEdge (q := q) s)
      e (certSite s (n - 2)) (certSite s (n - 1))
      he (launchEdge_before s) hbeforeNext
  have hsIn : s ≠ ring.rightNeighbor e :=
    excluded_incoming ring
      (LaunchEdge (q := q) s)
      e (certSite s (n - 1)) s
      he hxMem (launch_neighbor ring s (by omega))
  refine ⟨other ring fixed C e _ hx hxIn,
    other ring fixed C e s hs hsIn, ?_⟩
  intro hc j
  apply clear_of_no_incoming ring fixed C e
    (certSite s (j.val + 1)) (hc j)
  exact excluded_incoming ring
    (LaunchEdge (q := q) s)
    e (certSite s j.val) (certSite s (j.val + 1))
    he (launchEdge_sampled s (by omega) j)
    (ring_neighbor_certSite ring s j.val)

theorem launch_outside_run {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (s : Fin n) (kick : Bool)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (word : List (Fin n))
    (hc : LaunchScratch C s kick)
    (hword : ∀ e, e ∈ word →
      ¬ LaunchEdge (q := q) s e) :
    LaunchScratch (runList ring fixed C word) s kick := by
  apply runList_preserves ring fixed
    (fun D => LaunchScratch D s kick)
    (fun e => ¬ LaunchEdge (q := q) s e)
    ?_ word C hc hword
  intro D hD e he
  obtain ⟨hx, hy, hf⟩ :=
    launch_outside_step ring fixed D s e ht hn he
  refine ⟨?_, ?_, ?_, hf hD.2.2.2⟩
  · unfold SlotClear
    rw [hx]
    exact hD.1
  · rw [hy]
    exact hD.2.1
  · rw [hy]
    exact hD.2.2.1

theorem launch_forward_clear {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (s : Fin n)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hc : ForwardClear C s) :
    ForwardClear
      (step ring fixed C (certSite s (n - 1))) s := by
  intro j
  have hj := j.isLt
  have hx :
      certSite s (j.val + 1) ≠ certSite s (n - 1) := by
    intro heq
    have hval := site_offset_injective s
      (j.val + 1) (n - 1) (by omega) (by omega) heq
    omega
  have hs : certSite s (j.val + 1) ≠ s := by
    intro heq
    have hzero :
        certSite s (j.val + 1) = certSite s 0 :=
      heq.trans (certSite_zero s).symm
    have hval := site_offset_injective s
      (j.val + 1) 0 (by omega) (by omega) hzero
    omega
  have hy :
      certSite s (j.val + 1) ≠
        ring.rightNeighbor (certSite s (n - 1)) := by
    rw [launch_neighbor ring s (by omega)]
    exact hs
  unfold SlotClear
  rw [other ring fixed C (certSite s (n - 1))
    (certSite s (j.val + 1)) hx hy]
  exact hc j

theorem launch_arm {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (s : Fin n)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hc : LaunchScratch C s false) :
    LaunchScratch
      (step ring fixed C (certSite s (n - 1))) s true := by
  have hne :
      ring.rightNeighbor (certSite s (n - 1)) ≠
        certSite s (n - 1) :=
    Ne.symm (ring_neighbor_distinct ring (by omega)
      (certSite s (n - 1)))
  have hr := target_raw ring fixed C
    (certSite s (n - 1)) hne
  rw [launch_neighbor ring s (by omega)] at hr
  refine ⟨source_clears ring fixed C _,
    ?_, ?_, launch_forward_clear ring fixed C s hn hc.2.2.2⟩
  · simpa [rawD1Step, hc.1.1, hc.2.1, hc.2.2.1] using hr.1
  · simpa [rawD1Step, hc.1.1, hc.2.1, hc.2.2.1] using hr.2

theorem launch_second_row {n q : Nat}
    (C : (protocol q).Configuration n)
    (s : Fin n)
    (hc : LaunchScratch C s true) :
    (rawD1Step (compileAdvice q)
      (C (certSite s (n - 1))) (C s)
      (postEInfo (C (certSite s (n - 1))) (C s))).row =
        "R1c" := by
  simp [rawD1Step, hc.1.1, hc.2.1, hc.2.2.1]

theorem launch_sample {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i, (fixed i).l = false)
    (hFrozen : Frozen fixed C)
    (hc : LaunchScratch C s true) :
    (step ring fixed C (certSite s (n - 1)) s).rawTok =
        some (rawPrefixSample
          (certificateWordOfAgents (compileAdvice q) fixed)
          s ⟨0, by omega⟩) ∧
    ForwardClear
      (step ring fixed C (certSite s (n - 1))) s := by
  have hne :
      ring.rightNeighbor (certSite s (n - 1)) ≠
        certSite s (n - 1) :=
    Ne.symm (ring_neighbor_distinct ring (by omega)
      (certSite s (n - 1)))
  have hr := target_raw ring fixed C
    (certSite s (n - 1)) hne
  rw [launch_neighbor ring s (by omega)] at hr
  have hp := postY_rootless ring fixed C
    hroot hFrozen (certSite s (n - 1))
  rw [launch_neighbor ring s (by omega)] at hp
  have hbit :
      (C s).u =
        certBit
          (certificateWordOfAgents (compileAdvice q) fixed) s :=
    (frozen_fields fixed C hFrozen s).1
  refine ⟨?_, launch_forward_clear ring fixed C s hn hc.2.2.2⟩
  exact hr.1.trans
    (raw_prefix_launch
      (certificateWordOfAgents (compileAdvice q) fixed)
      s ht
      (C (certSite s (n - 1))) (C s)
      (postEInfo (C (certSite s (n - 1))) (C s))
      hc.1.1 hc.2.1 hc.2.2.1 hbit hp)

theorem launchScratch_of_protected_clear {n q : Nat}
    (C : (protocol q).Configuration n)
    (s : Fin n)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hc : ∀ j : Fin ((compileAdvice q).t + 2),
      SlotClear C (certSite s (n - 1 + j.val))) :
    LaunchScratch C s false := by
  have hx : SlotClear C (certSite s (n - 1)) := by
    simpa only [Nat.add_zero] using
      hc (⟨0, by omega⟩ : Fin ((compileAdvice q).t + 2))
  have hy : SlotClear C s := by
    have h := hc
      (⟨1, by omega⟩ : Fin ((compileAdvice q).t + 2))
    have he : n - 1 + 1 = n := by omega
    simpa only [he, certSite_n] using h
  refine ⟨hx, hy.1, hy.2, ?_⟩
  intro j
  have h := hc
    (⟨j.val + 2, by omega⟩ :
      Fin ((compileAdvice q).t + 2))
  have he :
      n - 1 + (j.val + 2) = n + (j.val + 1) := by
    omega
  simpa only [he, site_add_cycle] using h

theorem launch_two_marks {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i, (fixed i).l = false)
    (hFrozen : Frozen fixed C)
    (hclear : ∀ j : Fin ((compileAdvice q).t + 2),
      SlotClear C (certSite s (n - 1 + j.val)))
    (before between : List (Fin n))
    (hbefore : ∀ e, e ∈ before →
      ¬ LaunchEdge (q := q) s e)
    (hbetween : ∀ e, e ∈ between →
      ¬ LaunchEdge (q := q) s e) :
    let final := runList ring fixed C
      (before ++ [certSite s (n - 1)] ++
        between ++ [certSite s (n - 1)])
    Frozen fixed final ∧
    (final s).rawTok =
      some (rawPrefixSample
        (certificateWordOfAgents (compileAdvice q) fixed)
        s ⟨0, by omega⟩) ∧
    (∀ k : Nat, 0 < k → k ≤ (compileAdvice q).t →
      (final (certSite s k)).rawTok = none) := by
  let afterBefore := runList ring fixed C before
  let afterArm :=
    step ring fixed afterBefore (certSite s (n - 1))
  let afterBetween := runList ring fixed afterArm between
  have hInitial := launchScratch_of_protected_clear C s hn hclear
  have hBefore :
      LaunchScratch afterBefore s false :=
    launch_outside_run ring fixed C s false ht hn
      before hInitial hbefore
  have hBeforeFrozen : Frozen fixed afterBefore :=
    runList_frozen ring fixed C before hFrozen
  have hArm : LaunchScratch afterArm s true :=
    launch_arm ring fixed afterBefore s hn hBefore
  have hArmFrozen : Frozen fixed afterArm :=
    step_frozen ring fixed afterBefore hBeforeFrozen
      (certSite s (n - 1))
  have hBetween : LaunchScratch afterBetween s true :=
    launch_outside_run ring fixed afterArm s true ht hn
      between hArm hbetween
  have hBetweenFrozen : Frozen fixed afterBetween :=
    runList_frozen ring fixed afterArm between hArmFrozen
  have hFinalFrozen :
      Frozen fixed
        (step ring fixed afterBetween (certSite s (n - 1))) :=
    step_frozen ring fixed afterBetween hBetweenFrozen
      (certSite s (n - 1))
  obtain ⟨htok, hforward⟩ :=
    launch_sample ring fixed afterBetween s ht hn
      hroot hBetweenFrozen hBetween
  have hRun :
      runList ring fixed C
        (before ++ [certSite s (n - 1)] ++
          between ++ [certSite s (n - 1)]) =
        step ring fixed afterBetween (certSite s (n - 1)) := by
    simp only [runList_append, runList_cons, runList_nil,
      afterBetween, afterArm, afterBefore]
  dsimp only
  rw [hRun]
  refine ⟨hFinalFrozen, htok, ?_⟩
  intro k hk hkt
  have hf :=
    (hforward
      (⟨k - 1, by omega⟩ : Fin (compileAdvice q).t)).1
  have he : k - 1 + 1 = k := by omega
  simpa only [he] using hf

end FreshReference
end L3


namespace L3
namespace FreshReference

theorem finiteRun_frozen {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (hC : Frozen fixed C) :
    ∀ (len : Nat) (word : Fin len → Fin n),
      Frozen fixed
        (finiteRun (step ring fixed) C len word) := by
  intro len
  induction len with
  | zero =>
      intro word
      exact hC
  | succ len ih =>
      intro word
      change Frozen fixed
        (step ring fixed
          (finiteRun (step ring fixed) C len (finitePrefix word))
          (finiteLast word))
      exact step_frozen ring fixed
        (finiteRun (step ring fixed) C len (finitePrefix word))
        (ih (finitePrefix word)) (finiteLast word)

def finiteLetters {n : Nat} :
    (len : Nat) → (Fin len → Fin n) → List (Fin n)
  | 0, _ => []
  | len + 1, word =>
      finiteLetters len (finitePrefix word) ++ [finiteLast word]

theorem finiteRun_eq_runList {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n) :
    ∀ (len : Nat) (word : Fin len → Fin n),
      finiteRun (step ring fixed) C len word =
        runList ring fixed C (finiteLetters len word) := by
  intro len
  induction len with
  | zero =>
      intro word
      rfl
  | succ len ih =>
      intro word
      change
        step ring fixed
          (finiteRun (step ring fixed) C len (finitePrefix word))
          (finiteLast word) =
        runList ring fixed C
          (finiteLetters len (finitePrefix word) ++
            [finiteLast word])
      rw [runList_append, runList_cons, runList_nil,
        ← ih (finitePrefix word)]

end FreshReference
end L3


namespace L3
namespace FreshReference

/-! ## A tolerant sampled traversal

Outside interactions are permitted at every stage. A resident token
survives every incoming collision; an empty future site stays empty
until its own incoming monitored edge is selected.
-/

theorem neighbor_injective {n : Nat}
    (ring : DirectedRing n) (a b : Fin n)
    (h : ring.rightNeighbor a = ring.rightNeighbor b) :
    a = b := by
  calc
    a = certSite (ring.rightNeighbor a) (n - 1) :=
      ring_predecessor_certSite ring a
    _ = certSite (ring.rightNeighbor b) (n - 1) :=
      congrArg (fun i => certSite i (n - 1)) h
    _ = b := (ring_predecessor_certSite ring b).symm

/-- An incoming collision cannot replace the tracked resident. -/
theorem resident_of_no_outgoing {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (e site : Fin n)
    (r : RawTok (compileAdvice q).t)
    (hs : site ≠ e)
    (htok : (C site).rawTok = some r) :
    (step ring fixed C e site).rawTok = some r := by
  by_cases hy : site = ring.rightNeighbor e
  · subst site
    rw [(target_raw ring fixed C e hs).1]
    cases hx : (C e).rawTok <;>
      simp [rawD1Step, hx, htok]
  · rw [other ring fixed C e site hs hy]
    exact htok

theorem empty_of_no_incoming {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (e site : Fin n)
    (hy : site ≠ ring.rightNeighbor e)
    (htok : (C site).rawTok = none) :
    (step ring fixed C e site).rawTok = none := by
  by_cases hx : site = e
  · subst site
    exact (source_clears ring fixed C e).1
  · rw [other ring fixed C e site hx hy]
    exact htok

/-- The exact monitored set B consists of these t outgoing edges. -/
def OutsideCoverage {n q : Nat}
    (s : Fin n) (e : Fin n) : Prop :=
  ∀ j : Fin (compileAdvice q).t, e ≠ certSite s j.val

def SampledStage {n q : Nat}
    (fixed : (protocol q).Configuration n)
    (s : Fin n) (j : Fin (compileAdvice q).t)
    (C : (protocol q).Configuration n) : Prop :=
  (C (certSite s j.val)).rawTok =
    some (rawPrefixSample
      (certificateWordOfAgents (compileAdvice q) fixed) s j) ∧
  ∀ k : Nat, j.val < k → k ≤ (compileAdvice q).t →
    (C (certSite s k)).rawTok = none

/-- Any edge outside B preserves the tracked stage, even when it
enters the occupied source or leaves an empty future site. -/
theorem sampled_stage_wait {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (s : Fin n) (j : Fin (compileAdvice q).t)
    (e : Fin n)
    (hout : OutsideCoverage (q := q) s e)
    (hstage : SampledStage fixed s j C) :
    SampledStage fixed s j (step ring fixed C e) := by
  constructor
  · exact resident_of_no_outgoing ring fixed C e
      (certSite s j.val)
      (rawPrefixSample
        (certificateWordOfAgents (compileAdvice q) fixed) s j)
      (Ne.symm (hout j)) hstage.1
  · intro k hjk hkt
    have hkpos : 0 < k := by omega
    have hprelt : k - 1 < (compileAdvice q).t := by omega
    have hneighbor :
        ring.rightNeighbor (certSite s (k - 1)) =
          certSite s k := by
      have hmath : k - 1 + 1 = k := by omega
      simpa only [hmath] using
        ring_neighbor_certSite ring s (k - 1)
    have hno : certSite s k ≠ ring.rightNeighbor e := by
      intro heq
      have he : e = certSite s (k - 1) :=
        neighbor_injective ring e (certSite s (k - 1))
          (heq.symm.trans hneighbor.symm)
      exact hout ⟨k - 1, hprelt⟩ he
    exact empty_of_no_incoming ring fixed C e (certSite s k)
      hno (hstage.2 k hjk hkt)

/-- A required nonterminal B-edge advances the tracked sampled
token and leaves every later target empty. -/
theorem sampled_stage_advance {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (s : Fin n) (j : Fin (compileAdvice q).t)
    (hj : j.val + 1 < (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hC : Frozen fixed C)
    (hstage : SampledStage fixed s j C) :
    SampledStage fixed s ⟨j.val + 1, hj⟩
      (step ring fixed C (certSite s j.val)) := by
  let W := certificateWordOfAgents (compileAdvice q) fixed
  have hneighbor :
      ring.rightNeighbor (certSite s j.val) =
        certSite s (j.val + 1) :=
    ring_neighbor_certSite ring s j.val
  have hne :
      ring.rightNeighbor (certSite s j.val) ≠
        certSite s j.val :=
    Ne.symm (ring_neighbor_distinct ring (by omega)
      (certSite s j.val))
  have hproject := (target_raw ring fixed C
    (certSite s j.val) hne).1
  rw [hneighbor] at hproject
  constructor
  · have hbit :
        (C (certSite s (j.val + 1))).u =
          certBit W (certSite s (j.val + 1)) :=
      (frozen_fields fixed C hC (certSite s (j.val + 1))).1
    have hbeta :
        (C (certSite s (j.val + 1))).beta =
          certMarker W (certSite s (j.val + 1)) :=
      (frozen_fields fixed C hC (certSite s (j.val + 1))).2.1
    have hpost :
        (postEInfo (C (certSite s j.val))
          (C (certSite s (j.val + 1)))).eY.l = false :=
      raw_postY_rootless _ _
        (frozen_rootless fixed C hroot hC (certSite s j.val))
        (frozen_rootless fixed C hroot hC
          (certSite s (j.val + 1)))
    exact hproject.trans
      (raw_prefix_forward W s j hj
        (C (certSite s j.val)) (C (certSite s (j.val + 1)))
        (postEInfo (C (certSite s j.val))
          (C (certSite s (j.val + 1))))
        hstage.1 (hstage.2 (j.val + 1) (by omega) (by omega))
        hbit hbeta hpost)
  · intro k hjk hkt
    have hno :
        certSite s k ≠
          ring.rightNeighbor (certSite s j.val) := by
      rw [hneighbor]
      intro heq
      have he := site_offset_injective s k (j.val + 1)
        (by omega) (by omega) heq
      have hnew : j.val + 1 < k := hjk
      have hjBound := j.isLt
      omega
    have hold : j.val < k := by
      have hnew : j.val + 1 < k := hjk
      omega
    exact empty_of_no_incoming ring fixed C (certSite s j.val)
      (certSite s k) hno
      (hstage.2 k hold hkt)

/-- A finite word ending at the t-th monitored B-mark, whose
monitored marks occur in the prescribed order. Delays are
arbitrary finite strings of outside-B edges. -/
inductive CoverageWord {n q : Nat} (s : Fin n) :
    Fin (compileAdvice q).t → List (Fin n) → Prop where
  | final (j : Fin (compileAdvice q).t)
      (hlast : j.val + 1 = (compileAdvice q).t) :
      CoverageWord (q := q) s j [certSite s j.val]
  | advance (j : Fin (compileAdvice q).t)
      (hj : j.val + 1 < (compileAdvice q).t)
      (word : List (Fin n))
      (tail : CoverageWord (q := q) s
        ⟨j.val + 1, hj⟩ word) :
      CoverageWord (q := q) s j (certSite s j.val :: word)
  | delay (j : Fin (compileAdvice q).t)
      (e : Fin n) (word : List (Fin n))
      (outside : OutsideCoverage (q := q) s e)
      (tail : CoverageWord (q := q) s j word) :
      CoverageWord (q := q) s j (e :: word)

/-- Readiness just before the word's final actual service. -/
def TerminalReadyAtEnd {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (s : Fin n) (ht : 2 ≤ (compileAdvice q).t)
    (word : List (Fin n)) : Prop :=
  ∃ before : List (Fin n),
    word = before ++ [certSite s ((compileAdvice q).t - 1)] ∧
    (runList ring fixed C before
      (certSite s ((compileAdvice q).t - 1))).rawTok =
      some (rawSampledTerminal
        (certificateWordOfAgents (compileAdvice q) fixed) s ht) ∧
    (runList ring fixed C before
      (certSite s (compileAdvice q).t)).rawTok = none ∧
    Frozen fixed (runList ring fixed C before)

/-- The complete tolerant coverage induction. No hypotheses about
outside-edge state effects are assumed: they were proved above. -/
theorem coverage_terminal_ready {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n) (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false) :
    ∀ (j : Fin (compileAdvice q).t)
      (word : List (Fin n)),
      CoverageWord (q := q) s j word →
      ∀ C : (protocol q).Configuration n,
        Frozen fixed C →
        SampledStage fixed s j C →
        TerminalReadyAtEnd ring fixed C s ht word := by
  intro j word hword
  induction hword with
  | final j hlast =>
      intro C hC hstage
      have hindex : j.val = (compileAdvice q).t - 1 := by
        omega
      have hj :
          j = (⟨(compileAdvice q).t - 1, by omega⟩ :
            Fin (compileAdvice q).t) := by
        apply Fin.ext
        exact hindex
      refine ⟨[], ?_, ?_, ?_, ?_⟩
      · simp only [List.nil_append, hindex]
      · have hs := hstage.1
        rw [hj, ghost_prefix_last_eq_sampled
          (certificateWordOfAgents (compileAdvice q) fixed) s ht] at hs
        exact hs
      · exact hstage.2 (compileAdvice q).t j.isLt (by omega)
      · exact hC
  | advance j hj word tail ih =>
      intro C hC hstage
      have hnext := sampled_stage_advance ring fixed C s j hj
        hn hroot hC hstage
      obtain ⟨before, hw, htok, hempty, hfrozen⟩ :=
        ih (step ring fixed C (certSite s j.val))
          (step_frozen ring fixed C hC (certSite s j.val)) hnext
      refine ⟨certSite s j.val :: before, ?_, ?_, ?_, ?_⟩
      · simpa only [List.cons_append] using
          congrArg (fun w => certSite s j.val :: w) hw
      · simpa only [runList_cons] using htok
      · simpa only [runList_cons] using hempty
      · simpa only [runList_cons] using hfrozen
  | delay j e word outside tail ih =>
      intro C hC hstage
      have hnext := sampled_stage_wait ring fixed C s j e
        outside hstage
      obtain ⟨before, hw, htok, hempty, hfrozen⟩ :=
        ih (step ring fixed C e)
          (step_frozen ring fixed C hC e) hnext
      refine ⟨e :: before, ?_, ?_, ?_, ?_⟩
      · simpa only [List.cons_append] using
          congrArg (fun w => e :: w) hw
      · simpa only [runList_cons] using htok
      · simpa only [runList_cons] using hempty
      · simpa only [runList_cons] using hfrozen

/-- The final monitored service is an actual rejecting R0c row
for any of the three paper failures. -/
theorem coverage_terminal_rejects {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (s : Fin n) (ht : 2 ≤ (compileAdvice q).t)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (word : List (Fin n))
    (hready : TerminalReadyAtEnd ring fixed C s ht word) :
    ∃ before : List (Fin n),
      word = before ++ [certSite s ((compileAdvice q).t - 1)] ∧
      (rawD1Step (compileAdvice q)
        (runList ring fixed C before
          (certSite s ((compileAdvice q).t - 1)))
        (runList ring fixed C before
          (ring.rightNeighbor
            (certSite s ((compileAdvice q).t - 1))))
        (postEInfo
          (runList ring fixed C before
            (certSite s ((compileAdvice q).t - 1)))
          (runList ring fixed C before
            (ring.rightNeighbor
              (certSite s ((compileAdvice q).t - 1)))))).reject = true := by
  obtain ⟨before, hw, htok, hempty, hfrozen⟩ := hready
  refine ⟨before, hw, ?_⟩
  have hneighbor :
      ring.rightNeighbor (certSite s ((compileAdvice q).t - 1)) =
        certSite s (compileAdvice q).t := by
    have hindex : (compileAdvice q).t - 1 + 1 =
        (compileAdvice q).t := by omega
    simpa only [hindex] using
      ring_neighbor_certSite ring s ((compileAdvice q).t - 1)
  rw [hneighbor]
  apply sampled_bad_pair_rejects
    (certificateWordOfAgents (compileAdvice q) fixed) s ht
    (by intro i; exact hroot i) hbad _ _ htok hempty
  · exact (frozen_fields fixed (runList ring fixed C before)
      hfrozen (certSite s (compileAdvice q).t)).1
  · exact frozen_rootless fixed (runList ring fixed C before)
      hroot hfrozen (certSite s ((compileAdvice q).t - 1))
  · exact frozen_rootless fixed (runList ring fixed C before)
      hroot hfrozen (certSite s (compileAdvice q).t)

end FreshReference
end L3


namespace L3
namespace FreshCoupon

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-! ## Exact discrete coupon counts -/

def ordered (n : Nat) : Nat → Nat → Nat
  | 0, k => if k = 0 then 1 else 0
  | len + 1, 0 => n ^ (len + 1)
  | len + 1, k + 1 =>
      (n - (k + 1)) * ordered n len (k + 1) +
        ordered n len k

def covered (n : Nat) : Nat → Nat → Nat
  | 0, k => if k = 0 then 1 else 0
  | len + 1, 0 => n ^ (len + 1)
  | len + 1, k + 1 =>
      (n - (k + 1)) * covered n len (k + 1) +
        (k + 1) * covered n len k

theorem ordered_zero_width (n len : Nat) :
    ordered n len 0 = n ^ len := by
  cases len <;> simp [ordered]

theorem covered_zero_width (n len : Nat) :
    covered n len 0 = n ^ len := by
  cases len <;> simp [covered]

theorem covered_eq_factorial_ordered (n : Nat) :
    ∀ len k,
      covered n len k = freshFact k * ordered n len k := by
  intro len
  induction len with
  | zero =>
      intro k
      cases k <;> simp [covered, ordered, freshFact]
  | succ len ih =>
      intro k
      cases k with
      | zero =>
          simp [covered, ordered, freshFact]
      | succ k =>
          simp only [covered, ordered, ih, freshFact]
          rw [Nat.mul_add]
          congr 1 <;> ac_rfl

theorem ordered_pos (n len k : Nat)
    (hn : 0 < n) (hk : k ≤ len) :
    0 < ordered n len k := by
  induction len generalizing k with
  | zero =>
      have hkzero : k = 0 := by omega
      subst k
      simp [ordered]
  | succ len ih =>
      cases k with
      | zero =>
          rw [ordered_zero_width]
          exact Nat.pow_pos hn
      | succ k =>
          have hpos : 0 < ordered n len k :=
            ih k (by omega)
          change
            0 <
              (n - (k + 1)) * ordered n len (k + 1) +
                ordered n len k
          omega

theorem covered_le_total (n len k : Nat) (hk : k ≤ n) :
    covered n len k ≤ n ^ len := by
  induction len generalizing k with
  | zero =>
      cases k <;> simp [covered]
  | succ len ih =>
      cases k with
      | zero =>
          simp [covered]
      | succ k =>
          have hsame := ih (k + 1) hk
          have hless := ih k (by omega)
          calc
            covered n (len + 1) (k + 1) =
                (n - (k + 1)) * covered n len (k + 1) +
                  (k + 1) * covered n len k := rfl
            _ ≤
                (n - (k + 1)) * n ^ len +
                  (k + 1) * n ^ len :=
              Nat.add_le_add
                (Nat.mul_le_mul_left _ hsame)
                (Nat.mul_le_mul_left _ hless)
            _ = n ^ (len + 1) := by
              rw [← Nat.add_mul, Nat.sub_add_cancel hk,
                Nat.pow_succ]
              ac_rfl

private theorem sum_zero (n : Nat)
    (f : List (Fin n) → Nat) :
    Prob.scheduleSum n 0 f = f [] := by
  simp [Prob.scheduleSum, FixedSpanRenewalPayload.wordSum,
    allSchedules]

private theorem sum_succ (n len : Nat)
    (f : List (Fin n) → Nat) :
    Prob.scheduleSum n (len + 1) f =
      (List.ofFn (fun e : Fin n =>
        Prob.scheduleSum n len (fun w => f (e :: w)))).sum :=
  FixedSpanRenewalPayload.wordSum_succ n len f

private theorem sum_const (n len v : Nat) :
    Prob.scheduleSum n len (fun _ => v) = n ^ len * v := by
  change
    FixedSpanRenewalPayload.wordSum n len (fun _ => v) =
      n ^ len * v
  rw [← FixedSpanRenewalPayload.rawWord_sum n len
    (fun _ => v)]
  exact ofFn_sum_const (n ^ len) v

private theorem sum_spike (n : Nat) :
    ∀ (a : Fin n) (v : Nat),
      (List.ofFn (fun e : Fin n =>
        if e = a then v else 0)).sum = v := by
  induction n with
  | zero =>
      intro a
      exact Fin.elim0 a
  | succ n ih =>
      intro a v
      refine Fin.cases ?_ ?_ a
      · rw [List.ofFn_succ, List.sum_cons]
        have ht :
            (List.ofFn (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1))
              then v else 0)).sum = 0 := by
          have hh := ofFn_sum_eq
            (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1))
              then v else 0)
            (fun _ : Fin n => 0)
            (by
              intro i
              have hn :
                  i.succ ≠ (0 : Fin (n + 1)) := by
                intro he
                have hv := congrArg Fin.val he
                change i.val + 1 = 0 at hv
                omega
              rw [if_neg hn])
          simpa only [ofFn_sum_const, Nat.mul_zero] using hh
        simp [ht]
      · intro a
        rw [List.ofFn_succ, List.sum_cons]
        have hn : (0 : Fin (n + 1)) ≠ a.succ := by
          intro he
          have hv := congrArg Fin.val he
          change 0 = a.val + 1 at hv
          omega
        rw [if_neg hn, Nat.zero_add]
        have hh := ofFn_sum_eq
          (fun i : Fin n =>
            if i.succ = a.succ then v else 0)
          (fun i : Fin n => if i = a then v else 0)
          (by intro i; simp only [Fin.succ_inj])
        rw [hh]
        exact ih a v

private theorem sum_comm {n k : Nat}
    (f : Fin n → Fin k → Nat) :
    (List.ofFn (fun e : Fin n =>
      (List.ofFn (fun g : Fin k => f e g)).sum)).sum =
    (List.ofFn (fun g : Fin k =>
      (List.ofFn (fun e : Fin n => f e g)).sum)).sum := by
  induction k with
  | zero =>
      simp [ofFn_sum_const]
  | succ k ih =>
      calc
        (List.ofFn (fun e : Fin n =>
            (List.ofFn
              (fun g : Fin (k + 1) => f e g)).sum)).sum =
          (List.ofFn (fun e : Fin n =>
            f e 0 +
              (List.ofFn
                (fun g : Fin k => f e g.succ)).sum)).sum := by
                apply ofFn_sum_eq
                intro e
                rw [List.ofFn_succ, List.sum_cons]
        _ =
          (List.ofFn (fun e : Fin n => f e 0)).sum +
            (List.ofFn (fun e : Fin n =>
              (List.ofFn
                (fun g : Fin k => f e g.succ)).sum)).sum :=
          ofFn_sum_add _ _
        _ =
          (List.ofFn (fun e : Fin n => f e 0)).sum +
            (List.ofFn (fun g : Fin k =>
              (List.ofFn
                (fun e : Fin n => f e g.succ)).sum)).sum := by
                rw [ih (fun e g => f e g.succ)]
        _ =
          (List.ofFn (fun g : Fin (k + 1) =>
            (List.ofFn (fun e : Fin n => f e g)).sum)).sum := by
              rw [List.ofFn_succ, List.sum_cons]

private theorem sum_snoc (n len : Nat)
    (f : List (Fin n) → Nat) :
    Prob.scheduleSum n (len + 1) f =
      (List.ofFn (fun e : Fin n =>
        Prob.scheduleSum n len
          (fun w => f (w ++ [e])))).sum := by
  induction len generalizing f with
  | zero =>
      simpa only [sum_zero, List.nil_append] using
        (sum_succ n 0 f)
  | succ len ih =>
      calc
        Prob.scheduleSum n (len + 1 + 1) f =
            (List.ofFn (fun a : Fin n =>
              Prob.scheduleSum n (len + 1)
                (fun w => f (a :: w)))).sum :=
          sum_succ n (len + 1) f
        _ =
            (List.ofFn (fun a : Fin n =>
              (List.ofFn (fun e : Fin n =>
                Prob.scheduleSum n len
                  (fun w => f (a :: (w ++ [e]))))).sum)).sum :=
          ofFn_sum_eq _ _
            (fun a => ih (fun w => f (a :: w)))
        _ =
            (List.ofFn (fun e : Fin n =>
              (List.ofFn (fun a : Fin n =>
                Prob.scheduleSum n len
                  (fun w => f (a :: (w ++ [e]))))).sum)).sum :=
          sum_comm
            (fun a e =>
              Prob.scheduleSum n len
                (fun w => f (a :: (w ++ [e]))))
        _ =
            (List.ofFn (fun e : Fin n =>
              Prob.scheduleSum n (len + 1)
                (fun w => f (w ++ [e])))).sum := by
          apply ofFn_sum_eq
          intro e
          exact
            (sum_succ n len
              (fun w => f (w ++ [e]))).symm

theorem scheduleSum_reverse (n len : Nat)
    (f : List (Fin n) → Nat) :
    Prob.scheduleSum n len (fun w => f w.reverse) =
      Prob.scheduleSum n len f := by
  induction len generalizing f with
  | zero =>
      simp only [sum_zero, List.reverse_nil]
  | succ len ih =>
      calc
        Prob.scheduleSum n (len + 1)
            (fun w => f w.reverse) =
          (List.ofFn (fun e : Fin n =>
            Prob.scheduleSum n len
              (fun w => f (e :: w).reverse))).sum :=
          sum_succ n len (fun w => f w.reverse)
        _ =
          (List.ofFn (fun e : Fin n =>
            Prob.scheduleSum n len
              (fun w => f (w.reverse ++ [e])))).sum := by
          simp only [List.reverse_cons]
        _ =
          (List.ofFn (fun e : Fin n =>
            Prob.scheduleSum n len
              (fun w => f (w ++ [e])))).sum :=
          ofFn_sum_eq _ _
            (fun e => ih (fun w => f (w ++ [e])))
        _ = Prob.scheduleSum n (len + 1) f :=
          (sum_snoc n len f).symm

private theorem sum_relabel {n : Nat}
    (p q : Fin n → Fin n)
    (hpq : ∀ e, q (p e) = e)
    (hqp : ∀ e, p (q e) = e)
    (f : Fin n → Nat) :
    (List.ofFn (fun e => f (p e))).sum =
      (List.ofFn f).sum := by
  calc
    (List.ofFn (fun e => f (p e))).sum =
        (List.ofFn (fun e : Fin n =>
          (List.ofFn (fun i : Fin n =>
            if i = p e then f i else 0)).sum)).sum := by
      apply ofFn_sum_eq
      intro e
      have hs :
          (List.ofFn (fun i : Fin n =>
            if i = p e then f i else 0)).sum =
            f (p e) := by
        calc
          (List.ofFn (fun i : Fin n =>
              if i = p e then f i else 0)).sum =
            (List.ofFn (fun i : Fin n =>
              if i = p e then f (p e) else 0)).sum :=
            ofFn_sum_eq _ _
              (by
                intro i
                by_cases hi : i = p e
                · subst i
                  simp
                · simp [hi])
          _ = f (p e) := sum_spike n (p e) (f (p e))
      exact hs.symm
    _ =
        (List.ofFn (fun i : Fin n =>
          (List.ofFn (fun e : Fin n =>
            if i = p e then f i else 0)).sum)).sum :=
      sum_comm (fun e i => if i = p e then f i else 0)
    _ = (List.ofFn f).sum := by
      apply ofFn_sum_eq
      intro i
      have hequiv (e : Fin n) :
          (i = p e) ↔ (e = q i) := by
        constructor
        · intro he
          have hh := congrArg q he
          rw [hpq e] at hh
          exact hh.symm
        · intro he
          subst e
          exact (hqp i).symm
      calc
        (List.ofFn (fun e : Fin n =>
            if i = p e then f i else 0)).sum =
          (List.ofFn (fun e : Fin n =>
            if e = q i then f i else 0)).sum :=
          ofFn_sum_eq _ _
            (by intro e; simp only [hequiv e])
        _ = f i := sum_spike n (q i) (f i)

theorem scheduleSum_relabel {n : Nat}
    (p q : Fin n → Fin n)
    (hpq : ∀ e, q (p e) = e)
    (hqp : ∀ e, p (q e) = e)
    (len : Nat) (f : List (Fin n) → Nat) :
    Prob.scheduleSum n len (fun w => f (w.map p)) =
      Prob.scheduleSum n len f := by
  induction len generalizing f with
  | zero =>
      simp only [sum_zero, List.map_nil]
  | succ len ih =>
      calc
        Prob.scheduleSum n (len + 1)
            (fun w => f (w.map p)) =
          (List.ofFn (fun e : Fin n =>
            Prob.scheduleSum n len
              (fun w => f ((e :: w).map p)))).sum :=
          sum_succ n len (fun w => f (w.map p))
        _ =
          (List.ofFn (fun e : Fin n =>
            Prob.scheduleSum n len
              (fun w => f (p e :: w)))).sum := by
          apply ofFn_sum_eq
          intro e
          simpa only [List.map_cons] using
            ih (fun w => f (p e :: w))
        _ =
          (List.ofFn (fun e : Fin n =>
            Prob.scheduleSum n len
              (fun w => f (e :: w)))).sum :=
          sum_relabel p q hpq hqp
            (fun e =>
              Prob.scheduleSum n len (fun w => f (e :: w)))
        _ = Prob.scheduleSum n (len + 1) f :=
          (sum_succ n len f).symm

def maskSize {n : Nat} (r : Fin n → Bool) : Nat :=
  (List.ofFn (fun e : Fin n => if r e then 1 else 0)).sum

def maskDrop {n : Nat} (r : Fin n → Bool) (e : Fin n) :
    Fin n → Bool :=
  fun i => if i = e then false else r i

private theorem maskDrop_of_false {n : Nat}
    (r : Fin n → Bool) (e : Fin n) (he : r e = false) :
    maskDrop r e = r := by
  funext i
  by_cases hi : i = e
  · subst i
    simp [maskDrop, he]
  · simp [maskDrop, hi]

private theorem maskDrop_size_of_true {n : Nat}
    (r : Fin n → Bool) (e : Fin n) (he : r e = true) :
    maskSize (maskDrop r e) + 1 = maskSize r := by
  have hrow (i : Fin n) :
      (if r i then 1 else 0) =
        (if maskDrop r e i then 1 else 0) +
          (if i = e then 1 else 0) := by
    by_cases hi : i = e
    · subst i
      simp [maskDrop, he]
    · simp [maskDrop, hi]
  have hs := ofFn_sum_eq _ _ hrow
  rw [ofFn_sum_add, sum_spike n e 1] at hs
  exact hs.symm

theorem maskSize_eq_zero_iff {n : Nat}
    (r : Fin n → Bool) :
    maskSize r = 0 ↔ ∀ e, r e = false := by
  constructor
  · intro hz e
    cases he : r e with
    | false => rfl
    | true =>
        have hh := maskDrop_size_of_true r e he
        rw [hz] at hh
        omega
  · intro h
    have hs := ofFn_sum_eq
      (fun e : Fin n => if r e then 1 else 0)
      (fun _ : Fin n => 0)
      (by intro e; simp [h e])
    simpa only [maskSize, ofFn_sum_const, Nat.mul_zero] using hs

private theorem mask_split_sum {n : Nat}
    (r : Fin n → Bool) (a b : Nat) :
    (List.ofFn
      (fun e : Fin n => if r e then b else a)).sum =
      (n - maskSize r) * a + maskSize r * b := by
  let z :=
    (List.ofFn
      (fun e : Fin n => if r e then 0 else 1)).sum
  have htotal : maskSize r + z = n := by
    have hs := ofFn_sum_eq
      (fun e : Fin n =>
        (if r e then 1 else 0) +
          (if r e then 0 else 1))
      (fun _ : Fin n => 1)
      (by intro e; cases r e <;> rfl)
    rw [ofFn_sum_add, ofFn_sum_const] at hs
    simpa only [Nat.mul_one, maskSize, z] using hs
  have hz : z = n - maskSize r := by omega
  have hrow (e : Fin n) :
      (if r e then b else a) =
        a * (if r e then 0 else 1) +
          b * (if r e then 1 else 0) := by
    cases r e <;> simp
  calc
    (List.ofFn
        (fun e : Fin n => if r e then b else a)).sum =
      (List.ofFn (fun e : Fin n =>
        a * (if r e then 0 else 1) +
          b * (if r e then 1 else 0))).sum :=
      ofFn_sum_eq _ _ hrow
    _ = a * z + b * maskSize r := by
      rw [ofFn_sum_add, ofFn_sum_mul_left,
        ofFn_sum_mul_left]
      simp only [z, maskSize]
    _ = (n - maskSize r) * a + maskSize r * b := by
      rw [hz]
      ac_rfl

def maskCover {n : Nat} :
    (Fin n → Bool) → List (Fin n) → Nat
  | r, [] => if maskSize r = 0 then 1 else 0
  | r, e :: w => maskCover (maskDrop r e) w

theorem maskCover_correct {n : Nat}
    (r : Fin n → Bool) (w : List (Fin n)) :
    maskCover r w = 1 ↔
      ∀ i, r i = true → i ∈ w := by
  induction w generalizing r with
  | nil =>
      constructor
      · intro h i hi
        have hz : maskSize r = 0 := by
          unfold maskCover at h
          split at h <;> omega
        have hf := (maskSize_eq_zero_iff r).mp hz i
        rw [hf] at hi
        cases hi
      · intro h
        have hf : ∀ i, r i = false := by
          intro i
          cases hi : r i with
          | false => rfl
          | true =>
              have hm := h i hi
              cases hm
        have hz := (maskSize_eq_zero_iff r).mpr hf
        simp [maskCover, hz]
  | cons e w ih =>
      change
        maskCover (maskDrop r e) w = 1 ↔
          ∀ i, r i = true → i ∈ e :: w
      rw [ih]
      constructor
      · intro h i hi
        by_cases he : i = e
        · subst i
          simp
        · apply List.mem_cons.mpr
          right
          apply h i
          simp [maskDrop, he, hi]
      · intro h i hi
        have he : i ≠ e := by
          intro heq
          subst i
          simp [maskDrop] at hi
        have hr : r i = true := by
          simpa [maskDrop, he] using hi
        have hm := h i hr
        rcases List.mem_cons.mp hm with heq | htail
        · exact False.elim (he heq)
        · exact htail

theorem maskCover_range {n : Nat}
    (r : Fin n → Bool) (w : List (Fin n)) :
    maskCover r w = 0 ∨ maskCover r w = 1 := by
  induction w generalizing r with
  | nil =>
      by_cases hz : maskSize r = 0 <;>
        simp [maskCover, hz]
  | cons e w ih =>
      exact ih (maskDrop r e)

theorem maskCover_count {n : Nat}
    (len : Nat) (r : Fin n → Bool) :
    Prob.scheduleSum n len (maskCover r) =
      covered n len (maskSize r) := by
  induction len generalizing r with
  | zero =>
      simp only [sum_zero, maskCover, covered]
  | succ len ih =>
      have hrow (e : Fin n) :
          Prob.scheduleSum n len
              (fun w => maskCover r (e :: w)) =
            if r e then
              covered n len (maskSize r - 1)
            else
              covered n len (maskSize r) := by
        change
          Prob.scheduleSum n len (maskCover (maskDrop r e)) = _
        rw [ih]
        cases he : r e with
        | false =>
            have hd := maskDrop_of_false r e he
            simp [he, hd]
        | true =>
            have hs := maskDrop_size_of_true r e he
            have hd :
                maskSize (maskDrop r e) = maskSize r - 1 := by
              omega
            simp [he, hd]
      rw [sum_succ]
      rw [ofFn_sum_eq _ _ hrow]
      rw [mask_split_sum]
      cases hs : maskSize r with
      | zero =>
          simp only [hs, Nat.sub_zero, Nat.zero_mul,
            Nat.add_zero, covered_zero_width, Nat.pow_succ]
          ac_rfl
      | succ k =>
          have hk : k + 1 - 1 = k := by omega
          simp only [hs, hk, covered]

private def choice (k a b v : Nat) : Nat :=
  if v + 1 = k then b else if k ≤ v then a else 0

private theorem choice_shift (k a b v : Nat) :
    choice (k + 1) a b (v + 1) = choice k a b v := by
  have he : (v + 1 + 1 = k + 1) ↔ (v + 1 = k) := by
    omega
  have hl : (k + 1 ≤ v + 1) ↔ (k ≤ v) := by omega
  simp only [choice, he, hl]

private theorem choice_head (k a b : Nat) :
    choice (k + 1) a b 0 =
      if k = 0 then b else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [choice]
  · have he : ¬ 0 + 1 = k + 1 := by omega
    have hl : ¬ k + 1 ≤ 0 := by omega
    simp [choice, he, hl, hk]

private theorem sum_choice (n k a b : Nat) (hk : k ≤ n) :
    (List.ofFn
      (fun e : Fin n => choice k a b e.val)).sum =
      (n - k) * a + if k = 0 then 0 else b := by
  induction n generalizing k with
  | zero =>
      have hkzero : k = 0 := by omega
      subst k
      simp [choice]
  | succ n ih =>
      cases k with
      | zero =>
          have hrow (e : Fin (n + 1)) :
              choice 0 a b e.val = a := by
            simp [choice]
          calc
            (List.ofFn (fun e : Fin (n + 1) =>
                choice 0 a b e.val)).sum =
                (List.ofFn (fun _ : Fin (n + 1) => a)).sum :=
              ofFn_sum_eq _ _ hrow
            _ = (n + 1) * a := ofFn_sum_const (n + 1) a
            _ = (n + 1 - 0) * a +
                  (if (0 : Nat) = 0 then 0 else b) := by
              simp
      | succ k =>
          rw [List.ofFn_succ, List.sum_cons]
          have htail :
              (List.ofFn (fun e : Fin n =>
                choice (k + 1) a b e.succ.val)).sum =
              (List.ofFn (fun e : Fin n =>
                choice k a b e.val)).sum :=
            ofFn_sum_eq _ _
              (by
                intro e
                change
                  choice (k + 1) a b (e.val + 1) =
                    choice k a b e.val
                exact choice_shift k a b e.val)
          have hhead :
              choice (k + 1) a b (0 : Fin (n + 1)).val =
                (if k = 0 then b else 0) := choice_head k a b
          rw [htail, ih k (by omega), hhead]
          have hsub : n + 1 - (k + 1) = n - k := by
            omega
          rw [hsub]
          by_cases hkzero : k = 0 <;>
            simp [hkzero, Nat.add_comm]

/-- Canonical first appearances are k-1,...,0. -/
def orderedAccept {n : Nat} : Nat → List (Fin n) → Nat
  | k, [] => if k = 0 then 1 else 0
  | k, e :: w =>
      if e.val + 1 = k then orderedAccept (k - 1) w
      else if k ≤ e.val then orderedAccept k w
      else 0

theorem orderedAccept_range {n : Nat}
    (k : Nat) (w : List (Fin n)) :
    orderedAccept k w = 0 ∨ orderedAccept k w = 1 := by
  induction w generalizing k with
  | nil =>
      by_cases hk : k = 0 <;>
        simp [orderedAccept, hk]
  | cons e w ih =>
      simp only [orderedAccept]
      split
      · exact ih _
      · split
        · exact ih _
        · exact Or.inl rfl

theorem orderedAccept_count (n len k : Nat) (hk : k ≤ n) :
    Prob.scheduleSum n len
        (orderedAccept (n := n) k) =
      ordered n len k := by
  induction len generalizing k with
  | zero =>
      simp only [sum_zero, orderedAccept, ordered]
  | succ len ih =>
      have hrow (e : Fin n) :
          Prob.scheduleSum n len
              (fun w => orderedAccept k (e :: w)) =
            choice k
              (ordered n len k)
              (ordered n len (k - 1))
              e.val := by
        by_cases he : e.val + 1 = k
        · simpa only [orderedAccept, choice, if_pos he] using
            ih (k - 1) (by omega)
        · by_cases hl : k ≤ e.val
          · simpa only [orderedAccept, choice, if_neg he,
              if_pos hl] using ih k hk
          · simpa only [orderedAccept, choice, if_neg he,
              if_neg hl, Nat.mul_zero] using
                sum_const n len 0
      rw [sum_succ, ofFn_sum_eq _ _ hrow,
        sum_choice n k _ _ hk]
      cases k with
      | zero =>
          simp [ordered_zero_width, Nat.pow_succ, Nat.mul_comm]
      | succ k =>
          have hkne : k + 1 ≠ 0 := by omega
          have hsub : k + 1 - 1 = k := by omega
          rw [if_neg hkne, hsub]
          rfl

def lastAccept {n : Nat} (k : Nat) (w : List (Fin n)) : Nat :=
  orderedAccept k w.reverse

theorem lastAccept_count (n len k : Nat) (hk : k ≤ n) :
    Prob.scheduleSum n len (lastAccept (n := n) k) =
      ordered n len k := by
  calc
    Prob.scheduleSum n len (lastAccept (n := n) k) =
        Prob.scheduleSum n len
          (orderedAccept (n := n) k) :=
      scheduleSum_reverse n len (orderedAccept (n := n) k)
    _ = ordered n len k :=
      orderedAccept_count n len k hk

def canonicalMask {n : Nat} (k : Nat) (e : Fin n) : Bool :=
  decide (e.val < k)

private theorem sum_below (n k : Nat) (hk : k ≤ n) :
    (List.ofFn
      (fun e : Fin n => if e.val < k then 1 else 0)).sum =
      k := by
  induction n generalizing k with
  | zero =>
      have hkzero : k = 0 := by omega
      subst k
      simp
  | succ n ih =>
      cases k with
      | zero =>
          simp [ofFn_sum_const]
      | succ k =>
          rw [List.ofFn_succ, List.sum_cons]
          have hz : (0 : Fin (n + 1)).val < k + 1 := by
            change 0 < k + 1
            omega
          rw [if_pos hz]
          have htail :
              (List.ofFn (fun e : Fin n =>
                if e.succ.val < k + 1 then 1 else 0)).sum =
              (List.ofFn (fun e : Fin n =>
                if e.val < k then 1 else 0)).sum :=
            ofFn_sum_eq _ _
              (by
                intro e
                have he :
                    (e.succ.val < k + 1) ↔ (e.val < k) := by
                  change
                    (e.val + 1 < k + 1) ↔ (e.val < k)
                  omega
                simp only [he])
          rw [htail, ih k (by omega)]
          omega

theorem canonicalMask_size (n k : Nat) (hk : k ≤ n) :
    maskSize (canonicalMask (n := n) k) = k := by
  simpa [maskSize, canonicalMask] using sum_below n k hk

theorem cover_eq_factorial_last
    (n len k : Nat) (hk : k ≤ n) :
    Prob.scheduleSum n len
        (maskCover (canonicalMask (n := n) k)) =
      freshFact k *
        Prob.scheduleSum n len
          (lastAccept (n := n) k) := by
  rw [maskCover_count, canonicalMask_size n k hk,
    lastAccept_count n len k hk,
    covered_eq_factorial_ordered]

theorem relabeled_mask_size {n : Nat}
    (p q : Fin n → Fin n)
    (hpq : ∀ e, q (p e) = e)
    (hqp : ∀ e, p (q e) = e)
    (k : Nat) (hk : k ≤ n) :
    maskSize (fun e => canonicalMask k (q e)) = k := by
  have hs := sum_relabel q p hqp hpq
    (fun e : Fin n => if canonicalMask k e then 1 else 0)
  exact hs.trans (canonicalMask_size n k hk)

theorem relabeled_last_count {n : Nat}
    (p q : Fin n → Fin n)
    (hpq : ∀ e, q (p e) = e)
    (hqp : ∀ e, p (q e) = e)
    (len k : Nat) (hk : k ≤ n) :
    Prob.scheduleSum n len
        (fun w => lastAccept k (w.map q)) =
      ordered n len k := by
  calc
    Prob.scheduleSum n len
        (fun w => lastAccept k (w.map q)) =
      Prob.scheduleSum n len
        (lastAccept (n := n) k) :=
      scheduleSum_relabel q p hqp hpq len
        (lastAccept (n := n) k)
    _ = ordered n len k :=
      lastAccept_count n len k hk

theorem relabeled_cover_eq_factorial_last {n : Nat}
    (p q : Fin n → Fin n)
    (hpq : ∀ e, q (p e) = e)
    (hqp : ∀ e, p (q e) = e)
    (len k : Nat) (hk : k ≤ n) :
    Prob.scheduleSum n len
        (maskCover (fun e => canonicalMask k (q e))) =
      freshFact k *
        Prob.scheduleSum n len
          (fun w => lastAccept k (w.map q)) := by
  calc
    Prob.scheduleSum n len
        (maskCover (fun e => canonicalMask k (q e))) =
      covered n len
        (maskSize (fun e => canonicalMask k (q e))) :=
      maskCover_count len _
    _ = covered n len k := by
      rw [relabeled_mask_size p q hpq hqp k hk]
    _ = freshFact k * ordered n len k :=
      covered_eq_factorial_ordered n len k
    _ =
      freshFact k *
        Prob.scheduleSum n len
          (fun w => lastAccept k (w.map q)) := by
      rw [relabeled_last_count p q hpq hqp len k hk]

def clearCount (n t : Nat) : Nat :=
  ordered n (3 * n) (t + 3)

def discreteFactorNumerator (n t : Nat) : Nat :=
  t ^ t *
    (3 * (t + 2) ^ 2 * n ^ (3 * n) +
      (2 * t + 5) * clearCount n t)

def discreteFactorDenominator (n t : Nat) : Nat :=
  clearCount n t

/-- Exact renewal coefficient; no protocol cost bound is asserted here. -/
def discreteFactor (n t : Nat) : Rat :=
  (discreteFactorNumerator n t : Rat) /
    (discreteFactorDenominator n t : Rat)

theorem clearCount_pos (n t : Nat) (hwidth : t + 3 ≤ n) :
    0 < clearCount n t := by
  unfold clearCount
  apply ordered_pos
  · omega
  · omega

theorem clearCount_eq_relabeled {n : Nat}
    (p q : Fin n → Fin n)
    (hpq : ∀ e, q (p e) = e)
    (hqp : ∀ e, p (q e) = e)
    (t : Nat) (hwidth : t + 3 ≤ n) :
    Prob.scheduleSum n (3 * n)
        (fun w => lastAccept (t + 3) (w.map q)) =
      clearCount n t :=
  relabeled_last_count p q hpq hqp
    (3 * n) (t + 3) hwidth

end FreshCoupon
end L3


namespace L3
namespace FreshCoupon

/-! ## Explicit exact discrete correction -/

def discreteDeficit (n t : Nat) : Nat :=
  n ^ (3 * n) * 19 ^ (t + 3) -
    20 ^ (t + 3) * freshFact (t + 3) * clearCount n t

def discreteSurplus (n t : Nat) : Nat :=
  20 ^ (t + 3) * freshFact (t + 3) * clearCount n t -
    n ^ (3 * n) * 19 ^ (t + 3)

theorem discrete_count_exact_correction (n t : Nat) :
    20 ^ (t + 3) * freshFact (t + 3) * clearCount n t +
        discreteDeficit n t =
      n ^ (3 * n) * 19 ^ (t + 3) +
        discreteSurplus n t := by
  unfold discreteDeficit discreteSurplus
  omega

theorem discrete_count_lower_with_deficit (n t : Nat) :
    n ^ (3 * n) * 19 ^ (t + 3) ≤
      20 ^ (t + 3) * freshFact (t + 3) * clearCount n t +
        discreteDeficit n t := by
  unfold discreteDeficit
  omega

theorem discreteDeficit_eq_zero_iff (n t : Nat) :
    discreteDeficit n t = 0 ↔
      n ^ (3 * n) * 19 ^ (t + 3) ≤
        20 ^ (t + 3) * freshFact (t + 3) * clearCount n t := by
  unfold discreteDeficit
  omega

theorem relabeled_count_lower_with_deficit {n : Nat}
    (p q : Fin n → Fin n)
    (hpq : ∀ e, q (p e) = e)
    (hqp : ∀ e, p (q e) = e)
    (t : Nat) (hwidth : t + 3 ≤ n) :
    n ^ (3 * n) * 19 ^ (t + 3) ≤
      20 ^ (t + 3) * freshFact (t + 3) *
          Prob.scheduleSum n (3 * n)
            (fun w => lastAccept (t + 3) (w.map q)) +
        discreteDeficit n t := by
  rw [clearCount_eq_relabeled p q hpq hqp t hwidth]
  exact discrete_count_lower_with_deficit n t

private theorem scaled_correction_identity
    (scale lead tail total count paperDen paperMass : Nat) :
    scale * (lead * total + tail * count) * paperDen +
        scale * lead * (count * paperMass - total * paperDen) =
      scale * (lead * paperMass + tail * paperDen) * count +
        scale * lead * (total * paperDen - count * paperMass) := by
  have hbase :
      total * paperDen +
          (count * paperMass - total * paperDen) =
        count * paperMass +
          (total * paperDen - count * paperMass) := by
    omega
  calc
    scale * (lead * total + tail * count) * paperDen +
        scale * lead * (count * paperMass - total * paperDen) =
      scale * lead *
          (total * paperDen +
            (count * paperMass - total * paperDen)) +
        scale * tail * (count * paperDen) := by
      simp only [Nat.mul_add, Nat.add_mul] <;> ac_rfl
    _ =
      scale * lead *
          (count * paperMass +
            (total * paperDen - count * paperMass)) +
        scale * tail * (count * paperDen) := by
      rw [hbase]
    _ =
      scale * (lead * paperMass + tail * paperDen) * count +
        scale * lead * (total * paperDen - count * paperMass) := by
      simp only [Nat.mul_add, Nat.add_mul] <;> ac_rfl

theorem discreteFactor_exact_correction (n t : Nat) :
    discreteFactorNumerator n t * freshFactorDenominator t +
        t ^ t * (3 * (t + 2) ^ 2) * discreteSurplus n t =
      freshFactorNumerator t * clearCount n t +
        t ^ t * (3 * (t + 2) ^ 2) * discreteDeficit n t := by
  have h := scaled_correction_identity
    (t ^ t) (3 * (t + 2) ^ 2) (2 * t + 5)
    (n ^ (3 * n)) (clearCount n t)
    (19 ^ (t + 3)) (20 ^ (t + 3) * freshFact (t + 3))
  simpa only [discreteFactorNumerator, freshFactorDenominator,
    freshFactorNumerator, discreteDeficit, discreteSurplus,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem discreteFactor_le_paper_of_zero_deficit
    (n t : Nat) (hzero : discreteDeficit n t = 0) :
    discreteFactorNumerator n t * freshFactorDenominator t ≤
      freshFactorNumerator t * clearCount n t := by
  have h := discreteFactor_exact_correction n t
  rw [hzero, Nat.mul_zero, Nat.add_zero] at h
  omega

/-- The length-six-n window, recorded without a kernel zero-deficit theorem. -/
def clearCountSix (n t : Nat) : Nat :=
  ordered n (6 * n) (t + 3)

def sixWindowDeficit (n t : Nat) : Nat :=
  n ^ (6 * n) * 19 ^ (t + 3) -
    20 ^ (t + 3) * freshFact (t + 3) * clearCountSix n t

theorem sixWindow_exact_correction (n t : Nat) :
    20 ^ (t + 3) * freshFact (t + 3) * clearCountSix n t +
        sixWindowDeficit n t =
      n ^ (6 * n) * 19 ^ (t + 3) +
        (20 ^ (t + 3) * freshFact (t + 3) * clearCountSix n t -
          n ^ (6 * n) * 19 ^ (t + 3)) := by
  unfold sixWindowDeficit
  omega

theorem clearCountSix_pos (n t : Nat) (hwidth : t + 3 ≤ n) :
    0 < clearCountSix n t := by
  unfold clearCountSix
  apply ordered_pos
  · omega
  · omega

def sixWindowFactorNumerator (n t : Nat) : Nat :=
  t ^ t *
    (6 * (t + 2) ^ 2 * n ^ (6 * n) +
      (2 * t + 5) * clearCountSix n t)

def sixWindowFactorDenominator (n t : Nat) : Nat :=
  clearCountSix n t

def sixWindowFactor (n t : Nat) : Rat :=
  (sixWindowFactorNumerator n t : Rat) /
    (sixWindowFactorDenominator n t : Rat)


end FreshCoupon
end L3


namespace L3
namespace FreshReference

/-! ## The counted recognizer implies actual clearing -/

def extendIndex {len : Nat} (i : Fin len) : Fin (len + 1) :=
  ⟨i.val, by omega⟩

def CanonicalLastOrder {n len : Nat}
    (k : Nat) (word : Fin len → Fin n) : Prop :=
  ∃ last : Fin k → Fin len,
    (∀ j : Fin k,
      (word (last j)).val = j.val ∧
      ∀ p : Fin len, (last j).val < p.val →
        (word p).val ≠ j.val) ∧
    (∀ i j : Fin k, i.val < j.val →
      (last i).val < (last j).val)

theorem canonicalLastOrder_zero {n len : Nat}
    (word : Fin len → Fin n) :
    CanonicalLastOrder 0 word := by
  refine ⟨(fun j => Fin.elim0 j), ?_, ?_⟩
  · intro j
    exact Fin.elim0 j
  · intro i
    exact Fin.elim0 i

theorem canonicalLastOrder_snoc_outside {n len : Nat}
    (k : Nat) (word : Fin (len + 1) → Fin n)
    (horder : CanonicalLastOrder k (finitePrefix word))
    (hout : k ≤ (finiteLast word).val) :
    CanonicalLastOrder k word := by
  obtain ⟨last, hlast, hsorted⟩ := horder
  refine ⟨fun j => extendIndex (last j), ?_, ?_⟩
  · intro j
    constructor
    · exact (hlast j).1
    · intro p hp
      by_cases hprefix : p.val < len
      · exact (hlast j).2 ⟨p.val, hprefix⟩ hp
      · have hpTop : p.val = len := by
          have hbound := p.isLt
          omega
        have hpEq :
            p = (⟨len, by omega⟩ : Fin (len + 1)) :=
          Fin.ext hpTop
        intro heq
        rw [hpEq] at heq
        change (finiteLast word).val = j.val at heq
        have hj := j.isLt
        omega
  · intro i j hij
    exact hsorted i j hij

theorem canonicalLastOrder_snoc_new {n len : Nat}
    (k : Nat) (word : Fin (len + 1) → Fin n)
    (horder : CanonicalLastOrder k (finitePrefix word))
    (hfinal : (finiteLast word).val = k) :
    CanonicalLastOrder (k + 1) word := by
  obtain ⟨last, hlast, hsorted⟩ := horder
  let chosen : Fin (k + 1) → Fin (len + 1) :=
    fun j =>
      if hj : j.val < k then
        extendIndex (last ⟨j.val, hj⟩)
      else ⟨len, by omega⟩
  refine ⟨chosen, ?_, ?_⟩
  · intro j
    by_cases hj : j.val < k
    · have hchosen :
          chosen j = extendIndex (last ⟨j.val, hj⟩) := by
        simp only [chosen, dif_pos hj]
      rw [hchosen]
      constructor
      · exact (hlast ⟨j.val, hj⟩).1
      · intro p hp
        by_cases hprefix : p.val < len
        · exact (hlast ⟨j.val, hj⟩).2
            ⟨p.val, hprefix⟩ hp
        · have hpTop : p.val = len := by
            have hbound := p.isLt
            omega
          have hpEq :
              p = (⟨len, by omega⟩ : Fin (len + 1)) :=
            Fin.ext hpTop
          intro heq
          rw [hpEq] at heq
          change (finiteLast word).val = j.val at heq
          rw [hfinal] at heq
          omega
    · have hjTop : j.val = k := by
        have hbound := j.isLt
        omega
      have hchosen :
          chosen j = (⟨len, by omega⟩ : Fin (len + 1)) := by
        simp only [chosen, dif_neg hj]
      rw [hchosen]
      constructor
      · change (finiteLast word).val = j.val
        exact hfinal.trans hjTop.symm
      · intro p hp
        intro heq
        have hbound := p.isLt
        change len < p.val at hp
        omega
  · intro i j hij
    by_cases hj : j.val < k
    · have hi : i.val < k := by omega
      have hs := hsorted
        (⟨i.val, hi⟩ : Fin k)
        (⟨j.val, hj⟩ : Fin k) hij
      simpa only [chosen, dif_pos hi, dif_pos hj,
        extendIndex] using hs
    · have hi : i.val < k := by
        have hbound := j.isLt
        omega
      have hs :
          (last (⟨i.val, hi⟩ : Fin k)).val < len :=
        (last (⟨i.val, hi⟩ : Fin k)).isLt
      simpa only [chosen, dif_pos hi, dif_neg hj,
        extendIndex] using hs

theorem lastAccept_snoc {n : Nat}
    (k : Nat) (word : List (Fin n)) (e : Fin n) :
    FreshCoupon.lastAccept k (word ++ [e]) =
      (if e.val + 1 = k then
        FreshCoupon.lastAccept (k - 1) word
      else if k ≤ e.val then
        FreshCoupon.lastAccept k word
      else 0) := by
  simp [FreshCoupon.lastAccept, List.reverse_append,
    FreshCoupon.orderedAccept]

theorem lastAccept_finiteLetters_sound {n : Nat} :
    ∀ (len : Nat) (word : Fin len → Fin n) (k : Nat),
      FreshCoupon.lastAccept k (finiteLetters len word) = 1 →
      CanonicalLastOrder k word := by
  intro len
  induction len with
  | zero =>
      intro word k haccept
      by_cases hk : k = 0
      · subst k
        exact canonicalLastOrder_zero word
      · simp [finiteLetters, FreshCoupon.lastAccept,
          FreshCoupon.orderedAccept, hk] at haccept
  | succ len ih =>
      intro word k haccept
      have hscan :
          (if (finiteLast word).val + 1 = k then
            FreshCoupon.lastAccept (k - 1)
              (finiteLetters len (finitePrefix word))
          else if k ≤ (finiteLast word).val then
            FreshCoupon.lastAccept k
              (finiteLetters len (finitePrefix word))
          else 0) = 1 := by
        simpa only [finiteLetters, lastAccept_snoc] using haccept
      by_cases htop : (finiteLast word).val + 1 = k
      · have hprefix :
            FreshCoupon.lastAccept (k - 1)
              (finiteLetters len (finitePrefix word)) = 1 := by
          simpa only [if_pos htop] using hscan
        have hsub : k - 1 = (finiteLast word).val := by omega
        rw [hsub] at hprefix
        have hbefore :=
          ih (finitePrefix word) (finiteLast word).val hprefix
        have hafter :=
          canonicalLastOrder_snoc_new
            (finiteLast word).val word hbefore rfl
        simpa only [htop] using hafter
      · by_cases hout : k ≤ (finiteLast word).val
        · have hprefix :
              FreshCoupon.lastAccept k
                (finiteLetters len (finitePrefix word)) = 1 := by
            simpa only [if_neg htop, if_pos hout] using hscan
          exact canonicalLastOrder_snoc_outside
            k word (ih (finitePrefix word) k hprefix) hout
        · have hfalse : (0 : Nat) = 1 := by
            simpa only [if_neg htop, if_neg hout] using hscan
          omega

theorem canonicalLastOrder_to_protected {n q len : Nat}
    (s : Fin n)
    (word : Fin len → Fin n)
    (label : Fin n → Fin n)
    (hdecode :
      ∀ (e : Fin n) (j : Fin ((compileAdvice q).t + 3)),
        (label e).val = j.val ↔
          e = certSite s (n - 2 + j.val))
    (horder : CanonicalLastOrder ((compileAdvice q).t + 3)
      (fun p => label (word p))) :
    ProtectedLastOrder (q := q) s word := by
  obtain ⟨last, hlast, hsorted⟩ := horder
  refine ⟨last, ?_, ?_⟩
  · intro j
    refine ⟨(hdecode (word (last j)) j).mp (hlast j).1, ?_⟩
    intro p hp heq
    exact (hlast j).2 p hp
      ((hdecode (word p) j).mpr heq)
  · intro j
    exact hsorted
      (⟨j.val, by omega⟩ :
        Fin ((compileAdvice q).t + 3))
      (⟨j.val + 1, by omega⟩ :
        Fin ((compileAdvice q).t + 3))
      (by exact Nat.lt_succ_self j.val)

end FreshReference
end L3


namespace L3
namespace FreshReference

/-! ## Actual cyclic labels for the protected interval -/

def rotate {n : Nat} (base i : Fin n) : Fin n :=
  certSite base i.val

def unrotate {n : Nat} (base i : Fin n) : Fin n :=
  certSite i (n - base.val)

theorem unrotate_rotate {n : Nat} (base i : Fin n) :
    unrotate base (rotate base i) = i := by
  apply Fin.ext
  change ((base.val + i.val) % n + (n - base.val)) % n = i.val
  rw [Nat.mod_add_mod]
  have hbase := base.isLt
  have hsum : base.val + i.val + (n - base.val) = i.val + n := by
    omega
  rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

theorem rotate_unrotate {n : Nat} (base i : Fin n) :
    rotate base (unrotate base i) = i := by
  apply Fin.ext
  change (base.val + (i.val + (n - base.val)) % n) % n = i.val
  rw [Nat.add_comm base.val ((i.val + (n - base.val)) % n),
    Nat.mod_add_mod]
  have hbase := base.isLt
  have hsum : i.val + (n - base.val) + base.val = i.val + n := by
    omega
  rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

def protectedLabel {n : Nat} (s e : Fin n) : Fin n :=
  unrotate (certSite s (n - 2)) e

theorem protectedLabel_decode {n q : Nat}
    (s : Fin n) (hn : (compileAdvice q).t + 3 ≤ n)
    (e : Fin n) (j : Fin ((compileAdvice q).t + 3)) :
    (protectedLabel s e).val = j.val ↔
      e = certSite s (n - 2 + j.val) := by
  let a : Fin n := ⟨j.val, by have hj := j.isLt; omega⟩
  let base := certSite s (n - 2)
  have hencode :
      rotate base a = certSite s (n - 2 + j.val) :=
    certSite_add s (n - 2) j.val
  constructor
  · intro h
    have he : protectedLabel s e = a := by
      apply Fin.ext
      exact h
    calc
      e = rotate base (protectedLabel s e) :=
        (rotate_unrotate base e).symm
      _ = rotate base a := congrArg (rotate base) he
      _ = certSite s (n - 2 + j.val) := hencode
  · intro h
    have he : e = rotate base a := h.trans hencode.symm
    change (unrotate base e).val = j.val
    rw [he, unrotate_rotate]

theorem finiteLetters_map {n : Nat}
    (f : Fin n → Fin n) :
    ∀ (len : Nat) (word : Fin len → Fin n),
      finiteLetters len (fun i => f (word i)) =
        (finiteLetters len word).map f := by
  intro len
  induction len with
  | zero =>
      intro word
      rfl
  | succ len ih =>
      intro word
      change
        finiteLetters len (fun i => f (finitePrefix word i)) ++
          [f (finiteLast word)] =
        (finiteLetters len (finitePrefix word) ++
          [finiteLast word]).map f
      rw [ih (finitePrefix word), List.map_append,
        List.map_cons, List.map_nil]

theorem recognized_protected_last_order {n q len : Nat}
    (s : Fin n) (word : Fin len → Fin n)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (haccept :
      FreshCoupon.lastAccept ((compileAdvice q).t + 3)
        ((finiteLetters len word).map (protectedLabel s)) = 1) :
    ProtectedLastOrder (q := q) s word := by
  have hc :
      FreshCoupon.lastAccept ((compileAdvice q).t + 3)
        (finiteLetters len (fun i => protectedLabel s (word i))) = 1 := by
    rw [finiteLetters_map]
    exact haccept
  exact canonicalLastOrder_to_protected s word (protectedLabel s)
    (protectedLabel_decode s hn)
    (lastAccept_finiteLetters_sound len
      (fun i => protectedLabel s (word i))
      ((compileAdvice q).t + 3) hc)

/-- The very event counted below clears the actual reference slots. -/
theorem recognized_protected_clears {n q len : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (s : Fin n) (word : Fin len → Fin n)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (haccept :
      FreshCoupon.lastAccept ((compileAdvice q).t + 3)
        ((finiteLetters len word).map (protectedLabel s)) = 1) :
    ∀ j : Fin ((compileAdvice q).t + 2),
      SlotClear
        (finiteRun (step ring fixed) C len word)
        (certSite s (n - 1 + j.val)) :=
  protected_last_order_clears ring fixed C s word hn
    (recognized_protected_last_order s word hn haccept)

theorem protected_last_count {n q : Nat}
    (s : Fin n) (len : Nat)
    (hn : (compileAdvice q).t + 3 ≤ n) :
    Prob.scheduleSum n len
        (fun word => FreshCoupon.lastAccept ((compileAdvice q).t + 3)
          (word.map (protectedLabel s))) =
      FreshCoupon.ordered n len ((compileAdvice q).t + 3) :=
  FreshCoupon.relabeled_last_count
    (rotate (certSite s (n - 2)))
    (unrotate (certSite s (n - 2)))
    (unrotate_rotate (certSite s (n - 2)))
    (rotate_unrotate (certSite s (n - 2)))
    len ((compileAdvice q).t + 3) hn

theorem protected_mask_exact {n q : Nat}
    (s : Fin n) (hn : (compileAdvice q).t + 3 ≤ n)
    (e : Fin n) :
    FreshCoupon.canonicalMask ((compileAdvice q).t + 3)
        (protectedLabel s e) = true ↔
      ∃ j : Fin ((compileAdvice q).t + 3),
        e = certSite s (n - 2 + j.val) := by
  constructor
  · intro h
    have hk :
        (protectedLabel s e).val < (compileAdvice q).t + 3 := by
      simpa [FreshCoupon.canonicalMask] using h
    refine ⟨⟨(protectedLabel s e).val, hk⟩, ?_⟩
    exact (protectedLabel_decode s hn e
      ⟨(protectedLabel s e).val, hk⟩).mp rfl
  · intro h
    obtain ⟨j, hj⟩ := h
    have he := (protectedLabel_decode s hn e j).mpr hj
    have hk :
        (protectedLabel s e).val < (compileAdvice q).t + 3 := by
      rw [he]
      exact j.isLt
    simpa [FreshCoupon.canonicalMask] using hk

theorem protected_cover_eq_factorial_last {n q : Nat}
    (s : Fin n) (len : Nat)
    (hn : (compileAdvice q).t + 3 ≤ n) :
    Prob.scheduleSum n len
        (FreshCoupon.maskCover
          (fun e => FreshCoupon.canonicalMask
            ((compileAdvice q).t + 3) (protectedLabel s e))) =
      freshFact ((compileAdvice q).t + 3) *
        Prob.scheduleSum n len
          (fun word =>
            FreshCoupon.lastAccept ((compileAdvice q).t + 3)
              (word.map (protectedLabel s))) :=
  FreshCoupon.relabeled_cover_eq_factorial_last
    (rotate (certSite s (n - 2)))
    (unrotate (certSite s (n - 2)))
    (unrotate_rotate (certSite s (n - 2)))
    (rotate_unrotate (certSite s (n - 2)))
    len ((compileAdvice q).t + 3) hn

theorem protected_count_lower_with_deficit {n q : Nat}
    (s : Fin n) (hn : (compileAdvice q).t + 3 ≤ n) :
    n ^ (3 * n) * 19 ^ ((compileAdvice q).t + 3) ≤
      20 ^ ((compileAdvice q).t + 3) *
          freshFact ((compileAdvice q).t + 3) *
          Prob.scheduleSum n (3 * n)
            (fun word =>
              FreshCoupon.lastAccept ((compileAdvice q).t + 3)
                (word.map (protectedLabel s))) +
        FreshCoupon.discreteDeficit n (compileAdvice q).t := by
  rw [protected_last_count s (3 * n) hn]
  exact FreshCoupon.discrete_count_lower_with_deficit
    n (compileAdvice q).t

/-- Every finite scheduler list has an indexed finite-word
representation. No unproved word-enumeration convention is used
when applying the deterministic clearing lemma to counted lists. -/
theorem finiteLetters_surjective {n : Nat}
    (word : List (Fin n)) :
    ∃ len : Nat, ∃ indexed : Fin len → Fin n,
      finiteLetters len indexed = word := by
  have hreverse :
      ∀ w : List (Fin n),
        ∃ len : Nat, ∃ indexed : Fin len → Fin n,
          finiteLetters len indexed = w.reverse := by
    intro w
    induction w with
    | nil =>
        exact ⟨0, (fun i => Fin.elim0 i), rfl⟩
    | cons e w ih =>
        obtain ⟨len, indexed, heq⟩ := ih
        let extended : Fin (len + 1) → Fin n :=
          fun i => if hi : i.val < len then
            indexed ⟨i.val, hi⟩ else e
        have hprefix : finitePrefix extended = indexed := by
          funext i
          simp [finitePrefix, extended, i.isLt]
        have hlast : finiteLast extended = e := by
          simp [finiteLast, extended]
        refine ⟨len + 1, extended, ?_⟩
        simp only [finiteLetters, hprefix, hlast, heq,
          List.reverse_cons]
  obtain ⟨len, indexed, heq⟩ := hreverse word.reverse
  refine ⟨len, indexed, ?_⟩
  simpa only [List.reverse_reverse] using heq

/-- The exact list event used in scheduleSum clears the reference
configuration, for every finite list and every initial scratch. -/
theorem recognized_list_clears {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (s : Fin n) (word : List (Fin n))
    (hn : (compileAdvice q).t + 3 ≤ n)
    (haccept :
      FreshCoupon.lastAccept ((compileAdvice q).t + 3)
        (word.map (protectedLabel s)) = 1) :
    ∀ j : Fin ((compileAdvice q).t + 2),
      SlotClear (runList ring fixed C word)
        (certSite s (n - 1 + j.val)) := by
  obtain ⟨len, indexed, heq⟩ := finiteLetters_surjective word
  have hindexed :
      FreshCoupon.lastAccept ((compileAdvice q).t + 3)
        ((finiteLetters len indexed).map (protectedLabel s)) = 1 := by
    rw [heq]
    exact haccept
  have hclear := recognized_protected_clears ring fixed C s
    indexed hn hindexed
  rw [finiteRun_eq_runList] at hclear
  simpa only [heq] using hclear

end FreshReference
end L3


namespace L3
namespace FreshReference

/-! ## Assemble the deterministic paper experiment -/

def rawResult {n q : Nat}
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (e : Fin n) : RawResult (compileAdvice q).t :=
  rawD1Step (compileAdvice q) (C e) (C (ring.rightNeighbor e))
    (postEInfo (C e) (C (ring.rightNeighbor e)))

theorem launch_word_second_row {n q : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hclear : ∀ j : Fin ((compileAdvice q).t + 2),
      SlotClear C (certSite s (n - 1 + j.val)))
    (before between : List (Fin n))
    (hbefore : ∀ e, e ∈ before →
      ¬ LaunchEdge (q := q) s e)
    (hbetween : ∀ e, e ∈ between →
      ¬ LaunchEdge (q := q) s e) :
    (rawResult ring
      (runList ring fixed C
        (before ++ [certSite s (n - 1)] ++ between))
      (certSite s (n - 1))).row = "R1c" := by
  let first := runList ring fixed C before
  let armed := step ring fixed first (certSite s (n - 1))
  let ready := runList ring fixed armed between
  have hi := launchScratch_of_protected_clear C s hn hclear
  have hf : LaunchScratch first s false :=
    launch_outside_run ring fixed C s false ht hn
      before hi hbefore
  have ha : LaunchScratch armed s true :=
    launch_arm ring fixed first s hn hf
  have hr : LaunchScratch ready s true :=
    launch_outside_run ring fixed armed s true ht hn
      between ha hbetween
  have hrow := launch_second_row ready s hr
  have hrun :
      runList ring fixed C
        (before ++ [certSite s (n - 1)] ++ between) = ready := by
    simp only [runList_append, runList_cons, runList_nil,
      first, armed, ready]
  rw [hrun]
  unfold rawResult
  rw [launch_neighbor ring s (by omega)]
  exact hrow

/-- From arbitrary frozen scratch, the counted clearing event,
the first two prescribed A-marks, and the prescribed B-marks
produce a literal rejection at the final service. No state reset
or condition on outside scheduler selections is introduced. -/
theorem clearing_launch_coverage_report {n q len : Nat}
    (ring : DirectedRing n)
    (fixed C : (protocol q).Configuration n)
    (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hC : Frozen fixed C)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (clearWord : Fin len → Fin n)
    (hclearWord :
      FreshCoupon.lastAccept ((compileAdvice q).t + 3)
        ((finiteLetters len clearWord).map (protectedLabel s)) = 1)
    (before between coverage : List (Fin n))
    (hbefore : ∀ e, e ∈ before →
      ¬ LaunchEdge (q := q) s e)
    (hbetween : ∀ e, e ∈ between →
      ¬ LaunchEdge (q := q) s e)
    (hcoverage : CoverageWord (q := q) s ⟨0, by omega⟩ coverage) :
    let launchWord :=
      before ++ [certSite s (n - 1)] ++
        between ++ [certSite s (n - 1)]
    ∃ terminalPrefix : List (Fin n),
      (finiteLetters len clearWord ++ launchWord) ++ coverage =
        terminalPrefix ++ [certSite s ((compileAdvice q).t - 1)] ∧
      (rawResult ring (runList ring fixed C terminalPrefix)
        (certSite s ((compileAdvice q).t - 1))).reject = true := by
  let clearState := finiteRun (step ring fixed) C len clearWord
  let launchWord :=
    before ++ [certSite s (n - 1)] ++
      between ++ [certSite s (n - 1)]
  let launchState := runList ring fixed clearState launchWord
  have hclear :
      ∀ j : Fin ((compileAdvice q).t + 2),
        SlotClear clearState (certSite s (n - 1 + j.val)) :=
    recognized_protected_clears ring fixed C s clearWord hn hclearWord
  have hclearFrozen : Frozen fixed clearState :=
    finiteRun_frozen ring fixed C hC len clearWord
  have hlaunch := launch_two_marks ring fixed clearState s ht hn
    hroot hclearFrozen hclear before between hbefore hbetween
  have hlaunchFrozen : Frozen fixed launchState := hlaunch.1
  have hstage :
      SampledStage fixed s ⟨0, by omega⟩ launchState := by
    constructor
    · simpa only [certSite_zero] using hlaunch.2.1
    · exact hlaunch.2.2
  have hready := coverage_terminal_ready ring fixed s ht hn hroot
    ⟨0, by omega⟩ coverage hcoverage
    launchState hlaunchFrozen hstage
  obtain ⟨terminalTail, hword, hreport⟩ :=
    coverage_terminal_rejects ring fixed launchState s ht
      hroot hbad coverage hready
  have hprefix :
      runList ring fixed C
        (finiteLetters len clearWord ++ launchWord) = launchState := by
    rw [runList_append, ← finiteRun_eq_runList ring fixed C len clearWord]
  dsimp only
  refine ⟨(finiteLetters len clearWord ++ launchWord) ++ terminalTail,
    ?_, ?_⟩
  · simp only [hword, launchWord, List.append_assoc]
  · rw [runList_append, hprefix]
    exact hreport

end FreshReference
end L3


namespace L3.Prob.ScaledRenewal

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal
  (AttemptNode RetryKernel attemptCostNumerator retryCount
   repeatCostActive repeatCostNumerator)

/-!
## Exact rational reserve for the existing renewal calculus

This generic extension retains the rational coefficient. It does not
construct the fresh-scan experiment or prove its combined budget.
-/

private def continuation {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n)
    (z : AttemptNode A Seed) (T : Nat) : Nat :=
  match z with
  | .active a => repeatCostActive K a T
  | .success => 0
  | .retry s => repeatCostNumerator K s T

private def nodeValid {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n)
    (z : AttemptNode A Seed) : Prop :=
  match z with
  | .retry s => K.valid s
  | _ => True

private theorem child_valid {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n)
    (a : A) (e : Fin n) :
    nodeValid K (K.step a e) := by
  cases h : K.step a e with
  | active a' =>
      trivial
  | success =>
      trivial
  | retry s =>
      exact K.retry_valid a e s h

private theorem attempt_active_succ {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) (a : A) (T : Nat) :
    attemptCostNumerator K (.active a) (T + 1) =
      n ^ (T + 1) +
        (List.ofFn (fun e : Fin n =>
          attemptCostNumerator K (K.step a e) T)).sum := by
  simp only [attemptCostNumerator]

private theorem retry_active_succ {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) (a : A) (T : Nat) :
    retryCount K (.active a) (T + 1) =
      (List.ofFn (fun e : Fin n =>
        retryCount K (K.step a e) T)).sum := by
  simp only [retryCount]

private theorem repeat_active_succ {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) (a : A) (T : Nat) :
    repeatCostActive K a (T + 1) =
      n ^ (T + 1) +
        (List.ofFn (fun e : Fin n =>
          continuation K (K.step a e) T)).sum := by
  simp only [repeatCostActive]
  exact congrArg (fun v : Nat => n ^ (T + 1) + v)
    (ofFn_sum_eq _ _ (fun e => by
      cases K.step a e <;> rfl))


private theorem reserve {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n)
    (D P T : Nat)
    (hbound : ∀ t ≤ T, ∀ s, K.valid s →
      D * repeatCostNumerator K s t ≤ n ^ t * P) :
    ∀ z, nodeValid K z →
      D * continuation K z T ≤
        D * attemptCostNumerator K z T +
          P * retryCount K z T := by
  induction T with
  | zero =>
      intro z hz
      cases z <;>
        simp [continuation, repeatCostNumerator, repeatCostActive,
          attemptCostNumerator, retryCount]
  | succ T ih =>
      intro z hz
      cases z with
      | success =>
          simp [continuation, attemptCostNumerator, retryCount]
      | retry s =>
          have hs := hbound (T + 1) (Nat.le_refl _) s hz
          simpa [continuation, attemptCostNumerator, retryCount,
            Nat.mul_comm] using hs
      | active a =>
          have hc (e : Fin n) :
              D * continuation K (K.step a e) T ≤
                D * attemptCostNumerator K (K.step a e) T +
                  P * retryCount K (K.step a e) T := by
            apply ih
            · intro t ht s hs
              exact hbound t (by omega) s hs
            · exact child_valid K a e
          rw [show continuation K (.active a) (T + 1) =
              repeatCostActive K a (T + 1) from rfl,
            repeat_active_succ, attempt_active_succ,
            retry_active_succ]
          have hsum := ofFn_sum_le
            (fun e : Fin n =>
              D * continuation K (K.step a e) T)
            (fun e : Fin n =>
              D * attemptCostNumerator K (K.step a e) T +
                P * retryCount K (K.step a e) T) hc
          simp only [ofFn_sum_add, ofFn_sum_mul_left] at hsum
          simp only [Nat.mul_add]
          omega

theorem retry_cost_le_scaled_budget
    {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n)
    (D P : Nat)
    (hbudget : ∀ s, K.valid s → ∀ T,
      D * attemptCostNumerator K (.active (K.start s)) T +
        P * retryCount K (.active (K.start s)) T ≤
          n ^ T * P) :
    ∀ s, K.valid s → ∀ T,
      D * repeatCostNumerator K s T ≤ n ^ T * P := by
  intro s hs T
  induction T using Nat.strongRecOn generalizing s with
  | ind T ih =>
      cases T with
      | zero =>
          simp [repeatCostNumerator, repeatCostActive]
      | succ T =>
          have hbound : ∀ t ≤ T, ∀ s', K.valid s' →
              D * repeatCostNumerator K s' t ≤ n ^ t * P := by
            intro t ht s' hs'
            exact ih t (by omega) s' hs'
          have hc (e : Fin n) :
              D * continuation K (K.step (K.start s) e) T ≤
                D * attemptCostNumerator K
                  (K.step (K.start s) e) T +
                  P * retryCount K (K.step (K.start s) e) T :=
            reserve K D P T hbound _
              (child_valid K (K.start s) e)
          have hdecomp :
              D * repeatCostNumerator K s (T + 1) ≤
                D * attemptCostNumerator K
                  (.active (K.start s)) (T + 1) +
                  P * retryCount K
                    (.active (K.start s)) (T + 1) := by
            have e1 :
                repeatCostNumerator K s (T + 1) =
                  repeatCostActive K (K.start s) (T + 1) := rfl
            rw [e1, repeat_active_succ, attempt_active_succ,
              retry_active_succ]
            have hsum := ofFn_sum_le
              (fun e : Fin n =>
                D * continuation K (K.step (K.start s) e) T)
              (fun e : Fin n =>
                D * attemptCostNumerator K
                  (K.step (K.start s) e) T +
                  P * retryCount K (K.step (K.start s) e) T) hc
            simp only [ofFn_sum_add, ofFn_sum_mul_left] at hsum
            simp only [Nat.mul_add]
            omega
          exact Nat.le_trans hdecomp (hbudget s hs (T + 1))

private theorem physical_le_repeat
    {X A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n)
    (next : X → Fin n → X)
    (Good : X → Prop)
    (Rel : X → A → Prop)
    (hsim : RetrySimulation K next Good Rel) :
    ∀ x a, Rel x a → ∀ T,
      costNumerator next Good x T ≤ repeatCostActive K a T := by
  classical
  intro x a hrel T
  induction T generalizing x a with
  | zero =>
      simp [repeatCostActive]
  | succ T ih =>
      by_cases hx : Good x
      · rw [costNumerator_terminal next Good x hx (T + 1)]
        exact Nat.zero_le _
      · rw [costNumerator_succ next Good x hx T]
        have hc (e : Fin n) :
            costNumerator next Good (next x e) T ≤
              continuation K (K.step a e) T := by
          have hh := hsim x a hrel hx e
          cases he : K.step a e with
          | success =>
              have hg : Good (next x e) := by
                simpa only [he] using hh
              rw [costNumerator_terminal next Good (next x e) hg T]
              exact Nat.zero_le _
          | active a' =>
              have hr : Rel (next x e) a' := by
                simpa only [he] using hh
              exact ih (next x e) a' hr
          | retry s' =>
              have hr : Rel (next x e) (K.start s') := by
                simpa only [he] using hh
              exact ih (next x e) (K.start s') hr
        rw [repeat_active_succ]
        exact Nat.add_le_add_left (ofFn_sum_le _ _ hc) _

/-- Generic exact numerator transfer. The actual kernel, simulation,
and finite-horizon budget remain obligations of its caller. -/
theorem costNumerator_renewal_scaled_le
    {X A Seed : Type} {n : Nat}
    (next : X → Fin n → X)
    (Good : X → Prop)
    (K : RetryKernel A Seed n)
    (Rel : X → A → Prop)
    (hsim : RetrySimulation K next Good Rel)
    (D P : Nat)
    (hbudget : ∀ s, K.valid s → ∀ T,
      D * costNumerator (attemptStepper K)
        (fun z => attemptGood z ∨ attemptFail z)
        (.active (K.start s)) T +
        P * retryCount K (.active (K.start s)) T ≤
          n ^ T * P)
    (x : X) (s : Seed)
    (hs : K.valid s)
    (hrel : Rel x (K.start s)) :
    ∀ T, D * costNumerator next Good x T ≤ n ^ T * P := by
  have hb : ∀ s', K.valid s' → ∀ T,
      D * attemptCostNumerator K (.active (K.start s')) T +
        P * retryCount K (.active (K.start s')) T ≤
          n ^ T * P := by
    intro s' hs' T
    simpa only [attempt_costNumerator_eq] using hbudget s' hs' T
  intro T
  calc
    D * costNumerator next Good x T ≤
        D * repeatCostActive K (K.start s) T :=
      Nat.mul_le_mul_left D
        (physical_le_repeat K next Good Rel hsim
          x (K.start s) hrel T)
    _ = D * repeatCostNumerator K s T := by
      rfl
    _ ≤ n ^ T * P :=
      retry_cost_le_scaled_budget K D P hb s hs T

end L3.Prob.ScaledRenewal

set_option autoImplicit false
set_option Elab.async false

namespace L3.FreshCoupon

/-!
Conditional exact Nat recolouring count and 6n factor.
The missing global fibre double count is exposed as SixRecolourPairs.
-/

/-- Numerical triple-choice estimate for 2 <= n and k < n. -/
private theorem six_triple_numeric (n k : Nat)
    (hn : 2 ≤ n) (hk : k < n) :
    114 * (n - 1) ^ 3 ≤
      (6 * n - k) * (6 * n - k - 1) * (6 * n - k - 2) := by
  have hfirst : 5 * (n - 1) ≤ 6 * n - k := by omega
  have hsecond : 5 * (n - 1) ≤ 6 * n - k - 1 := by omega
  have hthird : 5 * (n - 1) ≤ 6 * n - k - 2 := by omega
  have hprod :
      (5 * (n - 1)) * (5 * (n - 1)) * (5 * (n - 1)) ≤
        (6 * n - k) * (6 * n - k - 1) * (6 * n - k - 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul hfirst hsecond) hthird
  have hcube :
      (5 * (n - 1)) * (5 * (n - 1)) * (5 * (n - 1)) =
        125 * (n - 1) ^ 3 := by
    rw [show (125 : Nat) = 5 * 5 * 5 by decide]
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    ac_rfl
  calc
    114 * (n - 1) ^ 3 ≤ 125 * (n - 1) ^ 3 :=
      Nat.mul_le_mul_right _ (by decide)
    _ = (5 * (n - 1)) * (5 * (n - 1)) *
          (5 * (n - 1)) := hcube.symm
    _ ≤ (6 * n - k) * (6 * n - k - 1) *
          (6 * n - k - 2) := hprod

/-- Exact combinatorial obligation for three nonessential recolours:
the 3! ordering and (n-1)^3 preimage factor are visible. -/
def SixRecolourPairs (n k : Nat) : Prop :=
  ((6 * n - k) * (6 * n - k - 1) * (6 * n - k - 2)) *
      (covered n (6 * n) k - covered n (6 * n) (k + 1)) ≤
    6 * (n - 1) ^ 3 * covered n (6 * n) (k + 1)

/-- Required one-letter bound, assuming the preceding fibre count. -/
theorem six_step_of_recolour_pairs (n k : Nat)
    (hn : 2 ≤ n) (hk : k < n)
    (hpair : SixRecolourPairs n k) :
    19 * covered n (6 * n) k ≤
      20 * covered n (6 * n) (k + 1) := by
  have hnumer := six_triple_numeric n k hn hk
  have hscaled := Nat.mul_le_mul_right
    (covered n (6 * n) k - covered n (6 * n) (k + 1)) hnumer
  have hcombined :
      (6 * (n - 1) ^ 3) *
          (19 * (covered n (6 * n) k -
            covered n (6 * n) (k + 1))) ≤
        (6 * (n - 1) ^ 3) *
          covered n (6 * n) (k + 1) := by
    calc
      _ = (114 * (n - 1) ^ 3) *
          (covered n (6 * n) k -
            covered n (6 * n) (k + 1)) := by
        rw [show (114 : Nat) = 6 * 19 by decide]
        ac_rfl
      _ ≤ ((6 * n - k) * (6 * n - k - 1) *
          (6 * n - k - 2)) *
          (covered n (6 * n) k -
            covered n (6 * n) (k + 1)) := hscaled
      _ ≤ (6 * (n - 1) ^ 3) *
          covered n (6 * n) (k + 1) := hpair
  have hpositive : 0 < 6 * (n - 1) ^ 3 := by
    apply Nat.mul_pos
    · decide
    · exact Nat.pow_pos (by omega)
  have hshort :
      19 * (covered n (6 * n) k -
          covered n (6 * n) (k + 1)) ≤
        covered n (6 * n) (k + 1) :=
    Nat.le_of_mul_le_mul_left hcombined hpositive
  omega

/-- Multiplication of the k-to-k+1 inequalities to width m. -/
theorem six_covered_iter (n : Nat) :
    ∀ m : Nat,
      (∀ k : Nat, k < m →
        19 * covered n (6 * n) k ≤
          20 * covered n (6 * n) (k + 1)) →
      n ^ (6 * n) * 19 ^ m ≤
        20 ^ m * covered n (6 * n) m := by
  intro m
  induction m with
  | zero =>
      intro _
      simp [covered_zero_width]
  | succ m ih =>
      intro hstep
      have hprev :
          ∀ k : Nat, k < m →
            19 * covered n (6 * n) k ≤
              20 * covered n (6 * n) (k + 1) := by
        intro k hk
        exact hstep k (by omega)
      have hbefore := ih hprev
      have hlast := hstep m (by omega)
      calc
        n ^ (6 * n) * 19 ^ (m + 1) =
            19 * (n ^ (6 * n) * 19 ^ m) := by
          simp only [Nat.pow_succ]
          ac_rfl
        _ ≤ 19 * (20 ^ m * covered n (6 * n) m) :=
          Nat.mul_le_mul_left 19 hbefore
        _ = 20 ^ m * (19 * covered n (6 * n) m) := by
          ac_rfl
        _ ≤ 20 ^ m * (20 * covered n (6 * n) (m + 1)) :=
          Nat.mul_le_mul_left _ hlast
        _ = 20 ^ (m + 1) * covered n (6 * n) (m + 1) := by
          simp only [Nat.pow_succ]
          ac_rfl

/-- Exact Nat deficit zero using the factorial/order identity,
but only with an explicit one-letter count hypothesis. -/
theorem sixWindowDeficit_zero_of_steps (n t : Nat)
    (hsteps : ∀ k : Nat, k < t + 3 →
      19 * covered n (6 * n) k ≤
        20 * covered n (6 * n) (k + 1)) :
    sixWindowDeficit n t = 0 := by
  have h := six_covered_iter n (t + 3) hsteps
  rw [covered_eq_factorial_ordered n (6 * n) (t + 3)] at h
  unfold sixWindowDeficit clearCountSix
  apply Nat.sub_eq_zero_of_le
  calc
    n ^ (6 * n) * 19 ^ (t + 3) ≤
        20 ^ (t + 3) *
          (freshFact (t + 3) * ordered n (6 * n) (t + 3)) := h
    _ = 20 ^ (t + 3) * freshFact (t + 3) *
          ordered n (6 * n) (t + 3) := by ac_rfl

theorem sixWindowDeficit_zero_of_recolour_pairs (n t : Nat)
    (hn : 2 ≤ n)
    (hwidth : t + 3 ≤ n)
    (hpairs : ∀ k : Nat, k < t + 3 → SixRecolourPairs n k) :
    sixWindowDeficit n t = 0 := by
  apply sixWindowDeficit_zero_of_steps n t
  intro k hk
  exact six_step_of_recolour_pairs n k hn
    (by omega) (hpairs k hk)

/-- Exact finite-n integer coefficient ceiling. -/
def sixWindowFactorCeiling (n t : Nat) : Nat :=
  (sixWindowFactorNumerator n t +
      sixWindowFactorDenominator n t - 1) /
    sixWindowFactorDenominator n t

def sixWindowCostCeiling (n t : Nat) : Nat :=
  n * sixWindowFactorCeiling n t

end L3.FreshCoupon


namespace L3.FreshReference

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal
  (AttemptNode RetryKernel retryCount)

/-! A concrete online 6n / launch / ordered-coverage observer. -/

inductive SixPhase (n : Nat) where
  | clearing (remaining : Nat) (word : List (Fin n))
  | launching (hits : Nat)
  | scanning (hits : Nat)
  | succeeded
  | failed

def sixTrialStart (n : Nat) : SixPhase n :=
  .clearing (6 * n) []

def sixLaunchContains {n q : Nat}
    (s e : Fin n) : Bool :=
  (List.ofFn (fun j : Fin ((compileAdvice q).t + 2) =>
    certSite s (n - 2 + j.val))).any (fun v => decide (v = e))

def sixScanContains {n q : Nat}
    (s e : Fin n) : Bool :=
  (List.ofFn (fun j : Fin (compileAdvice q).t =>
    certSite s j.val)).any (fun v => decide (v = e))

/-- Interleaved non-A/non-B edges cause observational self-loops.
The clearing buffer is chronological. -/
def sixPhaseNext {n q : Nat} (s : Fin n) :
    SixPhase n → Fin n → SixPhase n
  | .clearing 0 _, _ => .failed
  | .clearing (remaining + 1) word, e =>
      let gathered := word ++ [e]
      if remaining = 0 then
        if FreshCoupon.lastAccept ((compileAdvice q).t + 3)
            (gathered.map (protectedLabel s)) = 1
        then .launching 0 else .failed
      else .clearing remaining gathered
  | .launching hits, e =>
      if sixLaunchContains (q := q) s e then
        if e = certSite s (n - 1) then
          if hits = 0 then .launching 1
          else if hits = 1 then .scanning 0
          else .failed
        else .failed
      else .launching hits
  | .scanning hits, e =>
      if sixScanContains (q := q) s e then
        if e = certSite s hits then
          if hits + 1 = (compileAdvice q).t
          then .succeeded else .scanning (hits + 1)
        else .failed
      else .scanning hits
  | .succeeded, _ => .succeeded
  | .failed, _ => .failed

/-- Retry reinitializes only the observer at the reached
literal reference physical state. -/
def sixTrialKernel {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n) :
    RetryKernel
      ((protocol q).Configuration n × SixPhase n)
      ((protocol q).Configuration n) n :=
  { start := fun C => (C, sixTrialStart n)
    step := fun a e =>
      let nextC := step ring fixed a.1 e
      match sixPhaseNext (q := q) s a.2 e with
      | .succeeded => .success
      | .failed => .retry nextC
      | phase => .active (nextC, phase)
    valid := fun _ => True
    retry_valid := by
      intro a e C h
      trivial }

def sixReplayStep {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n)
    (a : (protocol q).Configuration n × SixPhase n)
    (e : Fin n) :
    (protocol q).Configuration n × SixPhase n :=
  let nextC := step ring fixed a.1 e
  match sixPhaseNext (q := q) s a.2 e with
  | .failed => (nextC, sixTrialStart n)
  | phase => (nextC, phase)

theorem sixReplayPhysical {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n)
    (a : (protocol q).Configuration n × SixPhase n)
    (e : Fin n) :
    (sixReplayStep ring fixed s a e).1 =
      step ring fixed a.1 e := by
  unfold sixReplayStep
  cases sixPhaseNext (q := q) s a.2 e <;> rfl

/-- Same-letter RetrySimulation for augmented observer replay. -/
theorem sixTrialReplaySimulation {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n) :
    Prob.RetrySimulation
      (sixTrialKernel ring fixed s)
      (sixReplayStep ring fixed s)
      (fun a => a.2 = SixPhase.succeeded)
      (fun x a => x = a) := by
  intro x a hrel hnot e
  subst x
  cases hp : sixPhaseNext (q := q) s a.2 e with
  | clearing remaining word =>
      simp [sixTrialKernel, sixReplayStep, hp]
  | launching hits =>
      simp [sixTrialKernel, sixReplayStep, hp]
  | scanning hits =>
      simp [sixTrialKernel, sixReplayStep, hp]
  | succeeded =>
      simp [sixTrialKernel, sixReplayStep, hp]
  | failed =>
      simp [sixTrialKernel, sixReplayStep, hp]

/-- Required state-uniform per-attempt cost and first-retry mass.
This is a *named unproved obligation*, not a theorem. -/
def SixExactBudget {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n) (D P : Nat) : Prop :=
  ∀ seed : (protocol q).Configuration n, ∀ T : Nat,
    D *
      costNumerator (Prob.attemptStepper (sixTrialKernel ring fixed s))
        (fun z => Prob.attemptGood z ∨ Prob.attemptFail z)
        (.active ((sixTrialKernel ring fixed s).start seed)) T +
      P * retryCount (sixTrialKernel ring fixed s)
        (.active ((sixTrialKernel ring fixed s).start seed)) T ≤
      n ^ T * P

/-- Conditional scaled-renewal transfer on the concrete replay. -/
theorem sixReplayCost_of_budget {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n) (D P : Nat)
    (hbudget : SixExactBudget ring fixed s D P)
    (seed : (protocol q).Configuration n) :
    ∀ T,
      D * costNumerator (sixReplayStep ring fixed s)
        (fun a => a.2 = SixPhase.succeeded)
        (seed, sixTrialStart n) T ≤
      n ^ T * P := by
  exact Prob.ScaledRenewal.costNumerator_renewal_scaled_le
    (sixReplayStep ring fixed s)
    (fun a => a.2 = SixPhase.succeeded)
    (sixTrialKernel ring fixed s)
    (fun x a => x = a)
    (sixTrialReplaySimulation ring fixed s)
    D P
    (by
      intro child hvalid T
      exact hbudget child T)
    (seed, sixTrialStart n) seed
    (by trivial) (by rfl)

def SixPaperBudget {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n) : Prop :=
  SixExactBudget ring fixed s
    (FreshCoupon.clearCountSix n (compileAdvice q).t)
    (n * FreshCoupon.sixWindowFactorNumerator n (compileAdvice q).t)

theorem sixReplayCost_of_paper_budget {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n)
    (hbudget : SixPaperBudget ring fixed s)
    (seed : (protocol q).Configuration n) :
    ∀ T,
      FreshCoupon.clearCountSix n (compileAdvice q).t *
        costNumerator (sixReplayStep ring fixed s)
          (fun a => a.2 = SixPhase.succeeded)
          (seed, sixTrialStart n) T ≤
        n ^ T * (n *
          FreshCoupon.sixWindowFactorNumerator n (compileAdvice q).t) := by
  exact sixReplayCost_of_budget ring fixed s
    (FreshCoupon.clearCountSix n (compileAdvice q).t)
    (n * FreshCoupon.sixWindowFactorNumerator n (compileAdvice q).t)
    hbudget seed

end L3.FreshReference

set_option autoImplicit false
set_option Elab.async false

namespace L3.FreshReference

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal
  (AttemptNode RetryKernel retryCount)

/-!
Operational after-cut genealogy of a literal R1c/R0b
scanner, with sticky success only on its selected rejecting R0c.
The OLD physical state is used for every raw-row observation.
-/

/-- A raw scanner born at origin after the cut, with hops consecutive
R0b transfers from its R1c launch target. -/
structure FreshTrail (n : Nat) where
  origin : Fin n
  hops : Nat

/-- No provenance is inherited at the cut, even when the physical
Cartesian scanner slots are arbitrarily occupied. -/
structure FreshGhost (n : Nat) where
  trail : Fin n → Option (FreshTrail n)
  phase : SixPhase n
  seen : Bool

abbrev FreshGhostConfig (n q : Nat) :=
  (protocol q).Configuration n × FreshGhost n

def freshGhostInitial (n : Nat) : FreshGhost n :=
  { trail := fun _ => none
    phase := sixTrialStart n
    seen := false }

theorem freshGhostInitial_no_trail (n : Nat) (i : Fin n) :
    (freshGhostInitial n).trail i = none := by
  rfl

theorem freshGhostInitial_flag (n : Nat) :
    (freshGhostInitial n).seen = false := by
  rfl

/-- Old resident provenance survives a collision. A new provenance
is created only at literal R1c with a produced scanner. An R0b
transfers only an existing tagged source with correct stage/edge. -/
def freshTargetTrail {n q : Nat}
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (g : FreshGhost n) (e : Fin n) : Option (FreshTrail n) :=
  let y := ring.rightNeighbor e
  let raw := rawResult ring C e
  match (C y).rawTok with
  | some _ => g.trail y
  | none =>
      if raw.row = "R1c" then
        match raw.tokY with
        | none => none
        | some _ => some { origin := y, hops := 0 }
      else if raw.row = "R0b" then
        match g.trail e, (C e).rawTok with
        | some tr, some tok =>
            if tok.j = tr.hops + 1 ∧
                e = certSite tr.origin tr.hops then
              some { origin := tr.origin, hops := tr.hops + 1 }
            else none
        | _, _ => none
      else none

/-- At the selected source the outgoing scanner is retired;
the target retains its resident or receives a valid new tag. -/
def freshTrailStep {n q : Nat}
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (g : FreshGhost n) (e : Fin n) :
    Fin n → Option (FreshTrail n) :=
  let y := ring.rightNeighbor e
  fun i =>
    if i = e then none
    else if i = y then freshTargetTrail ring C g e
    else g.trail i

/-- A selected R0c report is credited only to a scanner whose
post-cut R1c launch and all t-1 consecutive R0b hops were
tracked, ending at the terminal edge of the very same window. -/
def freshSelectedReject {n q : Nat}
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (g : FreshGhost n) (e : Fin n) : Bool :=
  let raw := rawResult ring C e
  match g.trail e with
  | none => false
  | some tr =>
      decide (tr.hops + 1 = (compileAdvice q).t) &&
      decide (e = certSite tr.origin tr.hops) &&
      decide (raw.row = "R0c") &&
      raw.reject

theorem freshSelectedReject_implies_raw {n q : Nat}
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (g : FreshGhost n) (e : Fin n)
    (h : freshSelectedReject ring C g e = true) :
    (rawResult ring C e).reject = true := by
  unfold freshSelectedReject at h
  cases ht : g.trail e with
  | none =>
      simp [ht] at h
  | some tr =>
      simp only [ht, Bool.and_eq_true] at h
      exact h.2

/-- Ghost transition on exactly the same physical selected edge.
Only the proof-only phase can restart; never the physical state. -/
def freshGhostStep {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n)
    (z : FreshGhostConfig n q)
    (e : Fin n) : FreshGhostConfig n q :=
  let C := z.1
  let g := z.2
  let phaseNext := sixPhaseNext (q := q) s g.phase e
  let nextPhase := match phaseNext with
    | .failed => sixTrialStart n
    | phase => phase
  (step ring fixed C e,
    { trail := freshTrailStep ring C g e
      phase := nextPhase
      seen := g.seen || freshSelectedReject ring C g e })

def freshGhostGood {n q : Nat}
    (z : FreshGhostConfig n q) : Prop :=
  z.2.seen = true

/-- Projection onto the exact existing reference stepper. -/
theorem freshGhost_projection {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n)
    (z : FreshGhostConfig n q) (e : Fin n) :
    (freshGhostStep ring fixed s z e).1 =
      step ring fixed z.1 e := by
  rfl

theorem freshGhost_flag_step {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n)
    (z : FreshGhostConfig n q) (e : Fin n) :
    (freshGhostStep ring fixed s z e).2.seen =
      (z.2.seen || freshSelectedReject ring z.1 z.2 e) := by
  rfl

/-- A successful report is latched permanently, independently of
future selected edges and all future public/certificate proposals. -/
theorem freshGhost_flag_sticky {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n)
    (z : FreshGhostConfig n q) (e : Fin n)
    (h : freshGhostGood z) :
    freshGhostGood (freshGhostStep ring fixed s z e) := by
  unfold freshGhostGood at h ⊢
  rw [freshGhost_flag_step, h]
  try rfl

/-- When the flag is still false, its first transition to true is
equivalent to the selected, genuinely after-cut raw R0c event. -/
theorem freshGhost_first_event {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n)
    (z : FreshGhostConfig n q) (e : Fin n)
    (h : z.2.seen = false) :
    freshGhostGood (freshGhostStep ring fixed s z e) ↔
      freshSelectedReject ring z.1 z.2 e = true := by
  cases he : freshSelectedReject ring z.1 z.2 e with
  | false =>
      simp [freshGhostGood, freshGhost_flag_step, h, he]
  | true =>
      simp [freshGhostGood, freshGhost_flag_step, h, he]

theorem freshGhost_source_tag_clears {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n)
    (z : FreshGhostConfig n q) (e : Fin n) :
    (freshGhostStep ring fixed s z e).2.trail e = none := by
  simp [freshGhostStep, freshTrailStep]

theorem freshGhost_other_tag {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n)
    (z : FreshGhostConfig n q)
    (e i : Fin n)
    (hi : i ≠ e)
    (hj : i ≠ ring.rightNeighbor e) :
    (freshGhostStep ring fixed s z e).2.trail i =
      z.2.trail i := by
  simp [freshGhostStep, freshTrailStep, hi, hj]

/-- Forget only the provenance and sticky bit. This maps the ghost
run to exactly the online phase replay. -/
def freshGhostForget {n q : Nat}
    (z : FreshGhostConfig n q) :
    (protocol q).Configuration n × SixPhase n :=
  (z.1, z.2.phase)

theorem freshGhost_forget_step {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n)
    (z : FreshGhostConfig n q) (e : Fin n) :
    freshGhostForget (freshGhostStep ring fixed s z e) =
      sixReplayStep ring fixed s (freshGhostForget z) e := by
  unfold freshGhostForget freshGhostStep sixReplayStep
  dsimp only
  cases hp : sixPhaseNext (q := q) s z.2.phase e <;> rfl


/-- Reachability from the literal cut and empty after-cut genealogy.
No arbitrary forged tag can enter the simulation relation. -/
inductive FreshGhostReachable {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n)
    (seed : (protocol q).Configuration n) :
    FreshGhostConfig n q → Prop where
  | initial :
      FreshGhostReachable ring fixed s seed
        (seed, freshGhostInitial n)
  | next (z : FreshGhostConfig n q)
      (hz : FreshGhostReachable ring fixed s seed z)
      (e : Fin n) :
      FreshGhostReachable ring fixed s seed
        (freshGhostStep ring fixed s z e)

/-- Exact outstanding deterministic soundness contract. On all
pre-success reached states, the online clearing/launch/coverage
success transition must actually have reached a tagged rejecting
R0c scanner. The original frozen public/native hypotheses and
bad fixed window are expected inputs to its eventual proof. -/
def FreshPhaseSound {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n)
    (seed : (protocol q).Configuration n) : Prop :=
  ∀ z : FreshGhostConfig n q,
    FreshGhostReachable ring fixed s seed z →
    z.2.seen = false →
      z.2.phase ≠ SixPhase.succeeded ∧
      ∀ e : Fin n,
        (sixTrialKernel ring fixed s).step (freshGhostForget z) e =
            .success →
          freshSelectedReject ring z.1 z.2 e = true

/-- Same physical state and the same phase, with ghost reachability. -/
def FreshGhostRelation {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n)
    (seed : (protocol q).Configuration n)
    (z : FreshGhostConfig n q)
    (a : (protocol q).Configuration n × SixPhase n) : Prop :=
  FreshGhostReachable ring fixed s seed z ∧
    freshGhostForget z = a

/-- Actual Prob.RetrySimulation for the ghost event. The only
scientific premise is the named reachable success-soundness fact. -/
theorem freshGhost_retrySimulation {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n)
    (seed : (protocol q).Configuration n)
    (hsound : FreshPhaseSound ring fixed s seed) :
    Prob.RetrySimulation
      (sixTrialKernel ring fixed s)
      (freshGhostStep ring fixed s)
      freshGhostGood
      (FreshGhostRelation ring fixed s seed) := by
  intro z a hrel hnot e
  obtain ⟨hreach, hagree⟩ := hrel
  have hfalse : z.2.seen = false := by
    cases hs : z.2.seen with
    | false => rfl
    | true => exact False.elim (hnot hs)
  have hphase :
      (freshGhostForget z).2 ≠ SixPhase.succeeded :=
    (hsound z hreach hfalse).1
  have hbase := (sixTrialReplaySimulation ring fixed s)
    (freshGhostForget z) a hagree hphase e
  cases hk : (sixTrialKernel ring fixed s).step a e with
  | success =>
      have hselected :
          (sixTrialKernel ring fixed s).step
            (freshGhostForget z) e = .success := by
        simpa only [hagree] using hk
      have hfresh := (hsound z hreach hfalse).2 e hselected
      exact (freshGhost_first_event ring fixed s z e hfalse).2 hfresh
  | active a' =>
      have ha :
          sixReplayStep ring fixed s (freshGhostForget z) e =
            a' := by
        simpa only [hk] using hbase
      exact ⟨FreshGhostReachable.next z hreach e,
        (freshGhost_forget_step ring fixed s z e).trans ha⟩
  | retry seed' =>
      have ha :
          sixReplayStep ring fixed s (freshGhostForget z) e =
            (sixTrialKernel ring fixed s).start seed' := by
        simpa only [hk] using hbase
      exact ⟨FreshGhostReachable.next z hreach e,
        (freshGhost_forget_step ring fixed s z e).trans ha⟩


/-- Exact 6n attempt-cost and retry-mass hypothesis, already defined
as SixPaperBudget. It applies to every reached
physical seed, not only the original scanner assignment. -/
theorem freshGhost_scaled_cost {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n)
    (seed : (protocol q).Configuration n)
    (hsound : FreshPhaseSound ring fixed s seed)
    (hbudget : SixPaperBudget ring fixed s) :
    ∀ T,
      FreshCoupon.clearCountSix n (compileAdvice q).t *
        costNumerator (freshGhostStep ring fixed s)
          freshGhostGood (seed, freshGhostInitial n) T ≤
        n ^ T * (n *
          FreshCoupon.sixWindowFactorNumerator n (compileAdvice q).t) := by
  exact Prob.ScaledRenewal.costNumerator_renewal_scaled_le
    (freshGhostStep ring fixed s)
    freshGhostGood
    (sixTrialKernel ring fixed s)
    (FreshGhostRelation ring fixed s seed)
    (freshGhost_retrySimulation ring fixed s seed hsound)
    (FreshCoupon.clearCountSix n (compileAdvice q).t)
    (n * FreshCoupon.sixWindowFactorNumerator n (compileAdvice q).t)
    (by
      intro child hvalid T
      exact hbudget child T)
    (seed, freshGhostInitial n) seed
    (by trivial)
    (show FreshGhostRelation ring fixed s seed
      (seed, freshGhostInitial n)
      ((sixTrialKernel ring fixed s).start seed) from
        ⟨FreshGhostReachable.initial, rfl⟩)

/-- All arithmetic in the ceiling transfer is Nat arithmetic.
The right side is the least quotient bound used by the existing
sixWindowFactorCeiling definition. -/
private theorem freshNat_ceil_mul (P D : Nat) (hD : 0 < D) :
    P ≤ D * ((P + D - 1) / D) := by
  have hdivision := Nat.div_add_mod (P + D - 1) D
  have hremainder := Nat.mod_lt (P + D - 1) hD
  have hpositive : 0 < P + D := by omega
  have hlt := Nat.lt_div_mul_add (a := P + D - 1) hD
  calc
    P ≤ ((P + D - 1) / D) * D := by omega
    _ = D * ((P + D - 1) / D) := by ac_rfl

/-- This is a genuine Nat-ceiling first-hit inequality for the
sticky, actually selected after-cut scanner event. Neither
soundness nor the finite-horizon attempt budget is smuggled
into the definition of its event. -/
theorem freshGhost_cost_ceiling_of_budget {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n)
    (seed : (protocol q).Configuration n)
    (hwidth : (compileAdvice q).t + 3 ≤ n)
    (hsound : FreshPhaseSound ring fixed s seed)
    (hbudget : SixPaperBudget ring fixed s) :
    ∀ T,
      costNumerator (freshGhostStep ring fixed s)
        freshGhostGood (seed, freshGhostInitial n) T ≤
        n ^ T *
          FreshCoupon.sixWindowCostCeiling n (compileAdvice q).t := by
  let t := (compileAdvice q).t
  let R := FreshCoupon.clearCountSix n t
  let N := FreshCoupon.sixWindowFactorNumerator n t
  let Q := FreshCoupon.sixWindowFactorCeiling n t
  have hR : 0 < R := FreshCoupon.clearCountSix_pos n t hwidth
  have hceil : N ≤ R * Q := by
    unfold N R Q
    change FreshCoupon.sixWindowFactorNumerator n t ≤
      FreshCoupon.clearCountSix n t *
        ((FreshCoupon.sixWindowFactorNumerator n t +
          FreshCoupon.clearCountSix n t - 1) /
            FreshCoupon.clearCountSix n t)
    exact freshNat_ceil_mul _ _ hR
  intro T
  have hscaled := freshGhost_scaled_cost
    ring fixed s seed hsound hbudget T
  have hbound :
      R * costNumerator (freshGhostStep ring fixed s)
          freshGhostGood (seed, freshGhostInitial n) T ≤
        R * (n ^ T * FreshCoupon.sixWindowCostCeiling n t) := by
    calc
      R * costNumerator (freshGhostStep ring fixed s)
            freshGhostGood (seed, freshGhostInitial n) T ≤
          n ^ T * (n * N) := hscaled
      _ ≤ n ^ T * (n * (R * Q)) :=
        Nat.mul_le_mul_left (n ^ T) (Nat.mul_le_mul_left n hceil)
      _ = R * (n ^ T * (n * Q)) := by ac_rfl
      _ = R * (n ^ T * FreshCoupon.sixWindowCostCeiling n t) := by
        rfl
  exact Nat.le_of_mul_le_mul_left hbound hR

/-- The requested paper interface retains the unproved 6n
recolouring family as an explicit argument. Rootlessness, the
frozen snapshot, and the actual false relation are visible.
Phase soundness and the uniform attempt budget remain the exact
two missing scientific lemmas for this reference process. -/
theorem freshGhost_cost_sixWindow {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n)
    (seed : (protocol q).Configuration n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hwidth : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hfrozen : Frozen fixed seed)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (hrecolour : ∀ k : Nat,
      k < (compileAdvice q).t + 3 →
        FreshCoupon.SixRecolourPairs n k)
    (hsound : FreshPhaseSound ring fixed s seed)
    (hbudget : SixPaperBudget ring fixed s) :
    ∀ T,
      costNumerator (freshGhostStep ring fixed s)
        freshGhostGood (seed, freshGhostInitial n) T ≤
        n ^ T *
          FreshCoupon.sixWindowCostCeiling n (compileAdvice q).t := by
  have hzero :
      FreshCoupon.sixWindowDeficit n (compileAdvice q).t = 0 :=
    FreshCoupon.sixWindowDeficit_zero_of_recolour_pairs
      n (compileAdvice q).t (by omega) hwidth hrecolour
  exact freshGhost_cost_ceiling_of_budget
    ring fixed s seed hwidth hsound hbudget

end L3.FreshReference

/-!
Fixed-length attempts.
The probabilistic obligation is discharged by fixed-word counting and
fixed-block induction. FixedWordGenealogy isolates the deterministic
terminal-tag premise; the old variable-duration observer is not used
to define these attempts.
-/

namespace L3.FreshFixed

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

theorem sum_zero (n : Nat) (f : List (Fin n) → Nat) :
    Prob.scheduleSum n 0 f = f [] := by
  simp [Prob.scheduleSum, FixedSpanRenewalPayload.wordSum, allSchedules]

theorem sum_succ (n len : Nat) (f : List (Fin n) → Nat) :
    Prob.scheduleSum n (len + 1) f =
      (List.ofFn (fun e : Fin n =>
        Prob.scheduleSum n len (fun w => f (e :: w)))).sum :=
  FixedSpanRenewalPayload.wordSum_succ n len f

theorem sum_const (n len v : Nat) :
    Prob.scheduleSum n len (fun _ => v) = n ^ len * v := by
  change FixedSpanRenewalPayload.wordSum n len (fun _ => v) = _
  rw [← FixedSpanRenewalPayload.rawWord_sum n len (fun _ => v)]
  exact ofFn_sum_const (n ^ len) v

theorem sum_ext (n len : Nat) (f g : List (Fin n) → Nat)
    (h : ∀ w, f w = g w) :
    Prob.scheduleSum n len f = Prob.scheduleSum n len g := by
  have he : f = g := funext h
  rw [he]

theorem sum_mul_left (n len c : Nat) (f : List (Fin n) → Nat) :
    Prob.scheduleSum n len (fun w => c * f w) =
      c * Prob.scheduleSum n len f := by
  change FixedSpanRenewalPayload.wordSum n len (fun w => c * f w) =
    c * FixedSpanRenewalPayload.wordSum n len f
  rw [← FixedSpanRenewalPayload.rawWord_sum n len (fun w => c * f w),
    ← FixedSpanRenewalPayload.rawWord_sum n len f, ofFn_sum_mul_left]

theorem sum_mul_right (n len c : Nat) (f : List (Fin n) → Nat) :
    Prob.scheduleSum n len (fun w => f w * c) =
      Prob.scheduleSum n len f * c := by
  calc
    _ = Prob.scheduleSum n len (fun w => c * f w) :=
      sum_ext n len _ _ (fun w => Nat.mul_comm (f w) c)
    _ = c * Prob.scheduleSum n len f := sum_mul_left n len c f
    _ = _ := Nat.mul_comm _ _

/-- Exact product count for the two fixed pieces of a word. -/
theorem sum_split_product (n left right : Nat)
    (f g : List (Fin n) → Nat) :
    Prob.scheduleSum n (left + right)
        (fun w => f (w.take left) * g (w.drop left)) =
      Prob.scheduleSum n left f * Prob.scheduleSum n right g := by
  induction left generalizing f with
  | zero =>
      simpa only [Nat.zero_add, List.take_zero, List.drop_zero,
        sum_zero] using sum_mul_left n right (f []) g
  | succ left ih =>
      have hlen : left + 1 + right = (left + right) + 1 := by omega
      rw [hlen, sum_succ, sum_succ]
      calc
        _ = (List.ofFn (fun e : Fin n =>
              Prob.scheduleSum n left (fun u => f (e :: u)) *
                Prob.scheduleSum n right g)).sum := by
          apply ofFn_sum_eq
          intro e
          simpa only [List.take_succ_cons, List.drop_succ_cons] using
            ih (fun u => f (e :: u))
        _ = (List.ofFn (fun e : Fin n =>
              Prob.scheduleSum n right g *
                Prob.scheduleSum n left (fun u => f (e :: u)))).sum :=
          ofFn_sum_eq _ _ (fun e => Nat.mul_comm _ _)
        _ = Prob.scheduleSum n right g *
              (List.ofFn (fun e : Fin n =>
                Prob.scheduleSum n left (fun u => f (e :: u)))).sum := by
          rw [ofFn_sum_mul_left]
        _ = _ := Nat.mul_comm _ _

theorem sum_spike (n : Nat) :
    ∀ (a : Fin n) (v : Nat),
      (List.ofFn (fun e : Fin n => if e = a then v else 0)).sum = v := by
  induction n with
  | zero => intro a; exact Fin.elim0 a
  | succ n ih =>
      intro a v
      refine Fin.cases ?_ ?_ a
      · rw [List.ofFn_succ, List.sum_cons]
        have ht : (List.ofFn (fun i : Fin n =>
            if i.succ = (0 : Fin (n + 1)) then v else 0)).sum = 0 := by
          have hh := ofFn_sum_eq
            (fun i : Fin n => if i.succ = (0 : Fin (n + 1)) then v else 0)
            (fun _ : Fin n => 0)
            (by
              intro i
              have hn : i.succ ≠ (0 : Fin (n + 1)) := by
                intro he
                have hv := congrArg Fin.val he
                change i.val + 1 = 0 at hv
                omega
              rw [if_neg hn])
          simpa only [ofFn_sum_const, Nat.mul_zero] using hh
        simp [ht]
      · intro a
        rw [List.ofFn_succ, List.sum_cons]
        have hn : (0 : Fin (n + 1)) ≠ a.succ := by
          intro he
          have hv := congrArg Fin.val he
          change 0 = a.val + 1 at hv
          omega
        rw [if_neg hn, Nat.zero_add]
        have hh := ofFn_sum_eq
          (fun i : Fin n => if i.succ = a.succ then v else 0)
          (fun i : Fin n => if i = a then v else 0)
          (by intro i; simp only [Fin.succ_inj])
        rw [hh]
        exact ih a v

theorem sum_mask (n : Nat) (outside : Fin n → Bool) (v : Nat) :
    (List.ofFn (fun e : Fin n => if outside e then v else 0)).sum =
      FreshCoupon.maskSize outside * v := by
  calc
    _ = (List.ofFn (fun e : Fin n =>
          v * (if outside e then 1 else 0))).sum := by
      apply ofFn_sum_eq
      intro e
      cases outside e <;> simp
    _ = v * FreshCoupon.maskSize outside := by
      simp only [ofFn_sum_mul_left, FreshCoupon.maskSize]
    _ = _ := Nat.mul_comm _ _

def outsideWord {n : Nat} (outside : Fin n → Bool) :
    List (Fin n) → Nat
  | [] => 1
  | e :: w => if outside e then outsideWord outside w else 0

def oneMark {n : Nat} (outside : Fin n → Bool) (a : Fin n) :
    List (Fin n) → Nat
  | [] => 0
  | e :: w =>
      if e = a then outsideWord outside w
      else if outside e then oneMark outside a w else 0

def markedSlots {n : Nat} (width : Nat) (outside : Fin n → Bool) :
    List (Fin n) → List (Fin n) → Nat
  | [], _ => 1
  | a :: marks, w =>
      oneMark outside a (w.take width) *
        markedSlots width outside marks (w.drop width)

theorem outsideWord_range {n : Nat} (outside : Fin n → Bool)
    (w : List (Fin n)) :
    outsideWord outside w = 0 ∨ outsideWord outside w = 1 := by
  induction w with
  | nil => exact Or.inr rfl
  | cons e w ih =>
      cases he : outside e <;> simp [outsideWord, he, ih]

theorem oneMark_range {n : Nat} (outside : Fin n → Bool)
    (a : Fin n) (w : List (Fin n)) :
    oneMark outside a w = 0 ∨ oneMark outside a w = 1 := by
  induction w with
  | nil => exact Or.inl rfl
  | cons e w ih =>
      by_cases he : e = a
      · simpa [oneMark, he] using outsideWord_range outside w
      · cases ho : outside e <;> simp [oneMark, he, ho, ih]

theorem markedSlots_range {n : Nat} (width : Nat)
    (outside : Fin n → Bool) (marks w : List (Fin n)) :
    markedSlots width outside marks w = 0 ∨
      markedSlots width outside marks w = 1 := by
  induction marks generalizing w with
  | nil => exact Or.inr rfl
  | cons a marks ih =>
      obtain h | h := oneMark_range outside a (w.take width)
      · exact Or.inl (by simp [markedSlots, h])
      · simpa [markedSlots, h] using ih (w.drop width)

theorem outsideWord_sound {n : Nat} (outside : Fin n → Bool)
    (w : List (Fin n)) (h : outsideWord outside w = 1) :
    ∀ e, e ∈ w → outside e = true := by
  revert h
  induction w with
  | nil => intro h e he; cases he
  | cons a w ih =>
      intro h
      cases ha : outside a with
      | false => simp [outsideWord, ha] at h
      | true =>
          have ht : outsideWord outside w = 1 := by
            simpa [outsideWord, ha] using h
          intro e he
          rcases List.mem_cons.mp he with he | he
          · subst e; exact ha
          · exact ih ht e he

theorem oneMark_sound {n : Nat} (outside : Fin n → Bool)
    (a : Fin n) (w : List (Fin n)) (h : oneMark outside a w = 1) :
    ∃ before after : List (Fin n),
      w = before ++ [a] ++ after ∧
      (∀ e, e ∈ before → outside e = true) ∧
      (∀ e, e ∈ after → outside e = true) := by
  revert h
  induction w with
  | nil => intro h; simp [oneMark] at h
  | cons e w ih =>
      intro h
      by_cases he : e = a
      · subst e
        have ht : outsideWord outside w = 1 := by
          simpa [oneMark] using h
        refine ⟨[], w, ?_, ?_, outsideWord_sound outside w ht⟩
        · simp
        · intro e he; cases he
      · cases ho : outside e with
        | false => simp [oneMark, he, ho] at h
        | true =>
            have ht : oneMark outside a w = 1 := by
              simpa [oneMark, he, ho] using h
            obtain ⟨before, after, hw, hb, ha⟩ := ih ht
            refine ⟨e :: before, after, ?_, ?_, ha⟩
            · simpa only [List.cons_append] using
                congrArg (fun v => e :: v) hw
            · intro b hbmem
              rcases List.mem_cons.mp hbmem with hbmem | hbmem
              · subst b; exact ho
              · exact hb b hbmem

theorem outsideWord_count (n len : Nat) (outside : Fin n → Bool) :
    Prob.scheduleSum n len (outsideWord outside) =
      (FreshCoupon.maskSize outside) ^ len := by
  induction len with
  | zero => simp [sum_zero, outsideWord]
  | succ len ih =>
      have hrow (e : Fin n) :
          Prob.scheduleSum n len (fun w => outsideWord outside (e :: w)) =
            if outside e then (FreshCoupon.maskSize outside) ^ len else 0 := by
        cases he : outside e <;> simp [outsideWord, he, ih, sum_const]
      rw [sum_succ, ofFn_sum_eq _ _ hrow, sum_mask, Nat.pow_succ]
      ac_rfl

theorem oneMark_count_step (n len : Nat) (outside : Fin n → Bool)
    (a : Fin n) (ha : outside a = false) :
    Prob.scheduleSum n (len + 1) (oneMark outside a) =
      (FreshCoupon.maskSize outside) ^ len +
        FreshCoupon.maskSize outside *
          Prob.scheduleSum n len (oneMark outside a) := by
  have hrow (e : Fin n) :
      Prob.scheduleSum n len (fun w => oneMark outside a (e :: w)) =
        (if e = a then (FreshCoupon.maskSize outside) ^ len else 0) +
          (if outside e then Prob.scheduleSum n len (oneMark outside a) else 0) := by
    by_cases he : e = a
    · subst e
      simpa [oneMark, ha] using outsideWord_count n len outside
    · cases ho : outside e <;> simp [oneMark, he, ho, sum_const]
  rw [sum_succ, ofFn_sum_eq _ _ hrow, ofFn_sum_add,
    sum_spike, sum_mask]

theorem oneMark_count (n len : Nat) (outside : Fin n → Bool)
    (a : Fin n) (ha : outside a = false) :
    Prob.scheduleSum n len (oneMark outside a) =
      len * (FreshCoupon.maskSize outside) ^ (len - 1) := by
  induction len with
  | zero => simp [sum_zero, oneMark]
  | succ len ih =>
      have hpower : FreshCoupon.maskSize outside *
            (len * (FreshCoupon.maskSize outside) ^ (len - 1)) =
          len * (FreshCoupon.maskSize outside) ^ len := by
        cases len <;>
          simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [oneMark_count_step n len outside a ha, ih, hpower]
      simp only [Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul]
      omega

theorem markedSlots_count (n width : Nat) (outside : Fin n → Bool)
    (marks : List (Fin n))
    (hmarks : ∀ a, a ∈ marks → outside a = false) :
    Prob.scheduleSum n (width * marks.length)
        (markedSlots width outside marks) =
      (width * (FreshCoupon.maskSize outside) ^ (width - 1)) ^ marks.length := by
  revert hmarks
  induction marks with
  | nil =>
      intro _
      simp [markedSlots, sum_const]
  | cons a marks ih =>
      intro hmarks
      have ha : outside a = false := hmarks a (by simp)
      have hm : ∀ b, b ∈ marks → outside b = false := by
        intro b hb
        exact hmarks b (List.mem_cons_of_mem a hb)
      have hlen : width * (a :: marks).length =
          width + width * marks.length := by
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
        omega
      rw [hlen]
      change Prob.scheduleSum n (width + width * marks.length)
          (fun w => oneMark outside a (w.take width) *
            markedSlots width outside marks (w.drop width)) =
        (width * (FreshCoupon.maskSize outside) ^ (width - 1)) ^
          (marks.length + 1)
      rw [sum_split_product, oneMark_count n width outside a ha,
        ih hm, Nat.pow_succ]
      ac_rfl

def outsideLaunch {n q : Nat} (s e : Fin n) : Bool :=
  !(FreshCoupon.canonicalMask ((compileAdvice q).t + 2)
    (FreshReference.protectedLabel s e))

def outsideCoverage {n q : Nat} (s e : Fin n) : Bool :=
  !(FreshCoupon.canonicalMask (compileAdvice q).t
    (FreshReference.unrotate s e))

theorem maskSize_not {n : Nat} (r : Fin n → Bool) :
    FreshCoupon.maskSize (fun e => !(r e)) =
      n - FreshCoupon.maskSize r := by
  have hs := ofFn_sum_eq
    (fun e : Fin n => (if r e then 1 else 0) +
      (if !(r e) then 1 else 0))
    (fun _ : Fin n => 1)
    (by intro e; cases r e <;> rfl)
  rw [ofFn_sum_add, ofFn_sum_const] at hs
  have ht : FreshCoupon.maskSize r +
      FreshCoupon.maskSize (fun e => !(r e)) = n := by
    simpa only [FreshCoupon.maskSize, Nat.mul_one] using hs
  omega

theorem outsideLaunch_size {n q : Nat} (s : Fin n)
    (hn : (compileAdvice q).t + 3 ≤ n) :
    FreshCoupon.maskSize (outsideLaunch (q := q) s) =
      n - ((compileAdvice q).t + 2) := by
  change FreshCoupon.maskSize (fun e =>
    !(FreshCoupon.canonicalMask ((compileAdvice q).t + 2)
      (FreshReference.unrotate (certSite s (n - 2)) e))) = _
  rw [maskSize_not, FreshCoupon.relabeled_mask_size
    (FreshReference.rotate (certSite s (n - 2)))
    (FreshReference.unrotate (certSite s (n - 2)))
    (FreshReference.unrotate_rotate (certSite s (n - 2)))
    (FreshReference.rotate_unrotate (certSite s (n - 2)))
    ((compileAdvice q).t + 2) (by omega)]

theorem outsideCoverage_size {n q : Nat} (s : Fin n)
    (hn : (compileAdvice q).t + 3 ≤ n) :
    FreshCoupon.maskSize (outsideCoverage (q := q) s) =
      n - (compileAdvice q).t := by
  change FreshCoupon.maskSize (fun e =>
    !(FreshCoupon.canonicalMask (compileAdvice q).t
      (FreshReference.unrotate s e))) = _
  rw [maskSize_not, FreshCoupon.relabeled_mask_size
    (FreshReference.rotate s) (FreshReference.unrotate s)
    (FreshReference.unrotate_rotate s) (FreshReference.rotate_unrotate s)
    (compileAdvice q).t (by omega)]

theorem outsideLaunch_true_iff {n q : Nat} (s : Fin n)
    (hn : (compileAdvice q).t + 3 ≤ n) (e : Fin n) :
    outsideLaunch (q := q) s e = true ↔
      ¬ FreshReference.LaunchEdge (q := q) s e := by
  have hlabel : (FreshReference.protectedLabel s e).val <
      (compileAdvice q).t + 2 ↔
      FreshReference.LaunchEdge (q := q) s e := by
    constructor
    · intro h
      refine ⟨⟨(FreshReference.protectedLabel s e).val, h⟩, ?_⟩
      exact (FreshReference.protectedLabel_decode s hn e
        ⟨(FreshReference.protectedLabel s e).val, by omega⟩).mp rfl
    · intro h
      obtain ⟨j, hj⟩ := h
      have he := (FreshReference.protectedLabel_decode s hn e
        ⟨j.val, by have hlt := j.isLt; omega⟩).mpr hj
      rw [he]
      exact j.isLt
  constructor
  · intro h hedge
    have hnot : ¬ (FreshReference.protectedLabel s e).val <
        (compileAdvice q).t + 2 := by
      simpa [outsideLaunch, FreshCoupon.canonicalMask] using h
    exact hnot (hlabel.mpr hedge)
  · intro h
    have hnot : ¬ (FreshReference.protectedLabel s e).val <
        (compileAdvice q).t + 2 := fun hlt => h (hlabel.mp hlt)
    simpa [outsideLaunch, FreshCoupon.canonicalMask] using hnot

theorem outsideCoverage_true_iff {n q : Nat} (s : Fin n)
    (hn : (compileAdvice q).t + 3 ≤ n) (e : Fin n) :
    outsideCoverage (q := q) s e = true ↔
      FreshReference.OutsideCoverage (q := q) s e := by
  constructor
  · intro h j he
    have hnot : ¬ (FreshReference.unrotate s e).val <
        (compileAdvice q).t := by
      simpa [outsideCoverage, FreshCoupon.canonicalMask] using h
    have hjn : j.val < n := by have hj := j.isLt; omega
    have hlabel : FreshReference.unrotate s e =
        (⟨j.val, hjn⟩ : Fin n) := by
      rw [he]
      exact FreshReference.unrotate_rotate s ⟨j.val, hjn⟩
    apply hnot
    rw [hlabel]
    exact j.isLt
  · intro h
    have hnot : ¬ (FreshReference.unrotate s e).val <
        (compileAdvice q).t := by
      intro hlt
      exact h ⟨(FreshReference.unrotate s e).val, hlt⟩
        (FreshReference.rotate_unrotate s e).symm
    simpa [outsideCoverage, FreshCoupon.canonicalMask] using hnot

theorem outsideLaunch_mark_false {n q : Nat} (s : Fin n)
    (hn : (compileAdvice q).t + 3 ≤ n) :
    outsideLaunch (q := q) s (certSite s (n - 1)) = false := by
  cases he : outsideLaunch (q := q) s (certSite s (n - 1)) with
  | false => rfl
  | true =>
      exact False.elim ((outsideLaunch_true_iff s hn
        (certSite s (n - 1))).mp he
          (FreshReference.launchEdge_launch s (by omega)))

theorem outsideCoverage_mark_false {n q : Nat} (s : Fin n)
    (hn : (compileAdvice q).t + 3 ≤ n) (j : Nat)
    (hj : j < (compileAdvice q).t) :
    outsideCoverage (q := q) s (certSite s j) = false := by
  cases he : outsideCoverage (q := q) s (certSite s j) with
  | false => rfl
  | true =>
      exact False.elim ((outsideCoverage_true_iff s hn (certSite s j)).mp he
        ⟨j, hj⟩ rfl)

end L3.FreshFixed

namespace L3.FreshFixed

set_option autoImplicit false
set_option Elab.async false

/-- A short fixed slot; its length depends only on n and the monitored
alphabet size, never on the letters actually read. -/
def slotWidth (n k : Nat) : Nat := n / (2 * k) + 1

def slotCount (n k : Nat) : Nat :=
  slotWidth n k * (n - k) ^ (slotWidth n k - 1)

def launchLength (n t : Nat) : Nat := slotWidth n (t + 2) * 2

def coverageLength (n t : Nat) : Nat := slotWidth n t * t

def attemptLength (n t : Nat) : Nat :=
  6 * n + (launchLength n t + coverageLength n t)

def launchLower (n t : Nat) : Nat := slotCount n (t + 2) ^ 2

def coverageLower (n t : Nat) : Nat := slotCount n t ^ t

def successLower (n t : Nat) : Nat :=
  FreshCoupon.clearCountSix n t * launchLower n t * coverageLower n t

def attemptCeiling (n t : Nat) : Nat :=
  Prob.ceilNat (attemptLength n t * n ^ attemptLength n t)
    (successLower n t)

def segmentPenalty (t : Nat) : Nat :=
  (4 * (t + 2)) ^ 2 * (4 * t) ^ t

/-- The explicit n-independent coefficient reported below. -/
def fixedFactorNumerator (t : Nat) : Nat :=
  8 * segmentPenalty t * freshFact (t + 3) * 20 ^ (t + 3)

def fixedFactorDenominator (t : Nat) : Nat := 19 ^ (t + 3)

theorem slotWidth_pos (n k : Nat) : 0 < slotWidth n k := by
  unfold slotWidth
  exact Nat.zero_lt_succ _

theorem slotCount_pos (n k : Nat) (hk : k < n) :
    0 < slotCount n k := by
  unfold slotCount
  exact Nat.mul_pos (slotWidth_pos n k) (Nat.pow_pos (by omega))

theorem power_mono (a b r : Nat) (h : a ≤ b) : a ^ r ≤ b ^ r := by
  induction r with
  | zero => exact Nat.le_refl 1
  | succ r ih =>
      simpa only [Nat.pow_succ] using Nat.mul_le_mul ih h

/-- An integral Bernoulli inequality, with no division or real numbers. -/
theorem power_gap_bound (a b r : Nat) :
    (a + b) ^ (r + 1) ≤
      (a + b) * a ^ r + (r * b) * (a + b) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hm := Nat.mul_le_mul_left a ih
      have hs :
          (r * b) * (a * (a + b) ^ r) ≤
            (r * b) * (a + b) ^ (r + 1) := by
        calc
          (r * b) * (a * (a + b) ^ r) ≤
              (r * b) * ((a + b) * (a + b) ^ r) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
              (Nat.le_add_right a b))
          _ = (r * b) * (a + b) ^ (r + 1) := by
            rw [Nat.pow_succ]
            ac_rfl
      calc
        (a + b) ^ (r + 1 + 1) =
            a * (a + b) ^ (r + 1) + b * (a + b) ^ (r + 1) := by
          rw [Nat.pow_succ (a + b) (r + 1), Nat.mul_add]
          ac_rfl
        _ ≤ a * ((a + b) * a ^ r + (r * b) * (a + b) ^ r) +
              b * (a + b) ^ (r + 1) :=
          Nat.add_le_add_right hm _
        _ = (a + b) * a ^ (r + 1) +
              (r * b) * (a * (a + b) ^ r) +
              b * (a + b) ^ (r + 1) := by
          rw [Nat.mul_add, Nat.pow_succ a r]
          ac_rfl
        _ ≤ (a + b) * a ^ (r + 1) +
              (r * b) * (a + b) ^ (r + 1) +
              b * (a + b) ^ (r + 1) :=
          Nat.add_le_add_right (Nat.add_le_add_left hs _) _
        _ = (a + b) * a ^ (r + 1) +
              ((r + 1) * b) * (a + b) ^ (r + 1) := by
          simp only [Nat.add_mul, Nat.one_mul, Nat.add_assoc]

theorem power_half (n k r : Nat)
    (hn : 0 < n) (hk : k ≤ n) (hsmall : 2 * r * k ≤ n) :
    n ^ r ≤ 2 * (n - k) ^ r := by
  have hg := power_gap_bound (n - k) k r
  rw [Nat.sub_add_cancel hk] at hg
  have hd := Nat.mul_le_mul_left 2 hg
  have hm := Nat.mul_le_mul_right (n ^ r) hsmall
  have hh :
      2 * (n * n ^ r) ≤ 2 * (n * (n - k) ^ r) + n * n ^ r := by
    calc
      2 * (n * n ^ r) = 2 * n ^ (r + 1) := by
        rw [Nat.pow_succ]
        ac_rfl
      _ ≤ 2 * (n * (n - k) ^ r + (r * k) * n ^ r) := hd
      _ = 2 * (n * (n - k) ^ r) + (2 * r * k) * n ^ r := by
        rw [Nat.mul_add]
        ac_rfl
      _ ≤ 2 * (n * (n - k) ^ r) + n * n ^ r :=
        Nat.add_le_add_left hm _
  have he : 2 * (n * (n - k) ^ r) = n * (2 * (n - k) ^ r) := by
    ac_rfl
  rw [he] at hh
  have hc : n * n ^ r ≤ n * (2 * (n - k) ^ r) := by omega
  exact Nat.le_of_mul_le_mul_left hc hn

/-- Each fixed slot succeeds on at least a 1/(4k) fraction of words. -/
theorem slot_count_fraction (n k : Nat)
    (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n) :
    n ^ slotWidth n k ≤ (4 * k) * slotCount n k := by
  let r := n / (2 * k)
  have hden : 0 < 2 * k := by omega
  have hd : (n / (2 * k)) * (2 * k) + n % (2 * k) = n := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod n (2 * k)
  have hr := Nat.mod_lt n hden
  have hl : r * (2 * k) ≤ n := by
    dsimp only [r]
    omega
  have he : r * (2 * k) = 2 * r * k := by ac_rfl
  have hsmall : 2 * r * k ≤ n := by simpa only [he] using hl
  have hu : n ≤ (2 * k) * (r + 1) := by
    have heq : (2 * k) * (r + 1) = r * (2 * k) + 2 * k := by
      rw [Nat.mul_add, Nat.mul_one]
      ac_rfl
    rw [heq]
    dsimp only [r]
    omega
  have hh := power_half n k r hn hkn hsmall
  change n ^ (r + 1) ≤ (4 * k) * ((r + 1) * (n - k) ^ (r + 1 - 1))
  rw [Nat.add_sub_cancel]
  calc
    n ^ (r + 1) = n * n ^ r := by rw [Nat.pow_succ, Nat.mul_comm]
    _ ≤ n * (2 * (n - k) ^ r) := Nat.mul_le_mul_left n hh
    _ ≤ ((2 * k) * (r + 1)) * (2 * (n - k) ^ r) :=
      Nat.mul_le_mul_right _ hu
    _ = (4 * k) * ((r + 1) * (n - k) ^ r) := by
      change _ = ((2 * 2) * k) * ((r + 1) * (n - k) ^ r)
      ac_rfl

theorem slotWidth_weight (n k : Nat)
    (hk : 0 < k) (hkn : k ≤ n) :
    k * slotWidth n k ≤ n := by
  let r := n / (2 * k)
  have hd : (n / (2 * k)) * (2 * k) + n % (2 * k) = n := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod n (2 * k)
  have hl : r * (2 * k) ≤ n := by
    dsimp only [r]
    omega
  change k * (r + 1) ≤ n
  by_cases hz : r = 0
  · simpa only [hz, Nat.zero_add, Nat.mul_one] using hkn
  · have hr : r + 1 ≤ 2 * r := by omega
    calc
      k * (r + 1) ≤ k * (2 * r) := Nat.mul_le_mul_left k hr
      _ = r * (2 * k) := by ac_rfl
      _ ≤ n := hl

theorem attemptLength_pos (n t : Nat) (hn : 0 < n) :
    0 < attemptLength n t := by
  unfold attemptLength
  omega

theorem attemptLength_le (n t : Nat)
    (ht : 2 ≤ t) (hwidth : t + 3 ≤ n) :
    attemptLength n t ≤ 8 * n := by
  have hlaunch := slotWidth_weight n (t + 2) (by omega) (by omega)
  have hcover := slotWidth_weight n t (by omega) (by omega)
  have htwo : slotWidth n (t + 2) * 2 ≤
      (t + 2) * slotWidth n (t + 2) := by
    calc
      slotWidth n (t + 2) * 2 ≤ slotWidth n (t + 2) * (t + 2) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = _ := Nat.mul_comm _ _
  have hc : slotWidth n t * t ≤ n := by
    simpa only [Nat.mul_comm] using hcover
  unfold attemptLength launchLength coverageLength
  omega

theorem successLower_pos (n t : Nat) (hwidth : t + 3 ≤ n) :
    0 < successLower n t := by
  unfold successLower launchLower coverageLower
  exact Nat.mul_pos
    (Nat.mul_pos (FreshCoupon.clearCountSix_pos n t hwidth)
      (Nat.pow_pos (slotCount_pos n (t + 2) (by omega))))
    (Nat.pow_pos (slotCount_pos n t (by omega)))

theorem launch_fraction (n t : Nat) (hwidth : t + 3 ≤ n) :
    n ^ launchLength n t ≤ (4 * (t + 2)) ^ 2 * launchLower n t := by
  have h := power_mono _ _ 2
    (slot_count_fraction n (t + 2) (by omega) (by omega) (by omega))
  simpa only [launchLength, launchLower, Nat.pow_mul, Nat.mul_pow] using h

theorem coverage_fraction (n t : Nat)
    (ht : 0 < t) (hwidth : t + 3 ≤ n) :
    n ^ coverageLength n t ≤ (4 * t) ^ t * coverageLower n t := by
  have h := power_mono _ _ t
    (slot_count_fraction n t (by omega) ht (by omega))
  simpa only [coverageLength, coverageLower, Nat.pow_mul, Nat.mul_pow] using h

theorem segments_fraction (n t : Nat)
    (ht : 0 < t) (hwidth : t + 3 ≤ n) :
    n ^ (launchLength n t + coverageLength n t) ≤
      segmentPenalty t * (launchLower n t * coverageLower n t) := by
  have h := Nat.mul_le_mul
    (launch_fraction n t hwidth) (coverage_fraction n t ht hwidth)
  rw [Nat.pow_add]
  calc
    n ^ launchLength n t * n ^ coverageLength n t ≤
        ((4 * (t + 2)) ^ 2 * launchLower n t) *
          ((4 * t) ^ t * coverageLower n t) := h
    _ = segmentPenalty t * (launchLower n t * coverageLower n t) := by
      unfold segmentPenalty
      ac_rfl

end L3.FreshFixed

namespace L3.FreshFixed

open FreshReference

def LaunchSegment {n q : Nat} (s : Fin n)
    (word : List (Fin n)) : Prop :=
  ∃ before between after : List (Fin n),
    word = (before ++ [certSite s (n - 1)] ++
      between ++ [certSite s (n - 1)]) ++ after ∧
    (∀ e, e ∈ before → ¬ LaunchEdge (q := q) s e) ∧
    (∀ e, e ∈ between → ¬ LaunchEdge (q := q) s e) ∧
    (∀ e, e ∈ after → ¬ LaunchEdge (q := q) s e)

def CoverageSegment {n q : Nat} (s : Fin n)
    (j : Fin (compileAdvice q).t) (word : List (Fin n)) : Prop :=
  ∃ front tail : List (Fin n),
    word = front ++ tail ∧ CoverageWord (q := q) s j front

def coverageMarks {n : Nat} (s : Fin n) :
    Nat → Nat → List (Fin n)
  | _, 0 => []
  | start, remaining + 1 =>
      certSite s start :: coverageMarks s (start + 1) remaining

theorem coverageMarks_length {n : Nat} (s : Fin n)
    (remaining : Nat) :
    ∀ start, (coverageMarks s start remaining).length = remaining := by
  induction remaining with
  | zero => intro start; rfl
  | succ remaining ih =>
      intro start
      simp only [coverageMarks, List.length_cons, ih]

theorem coverageMarks_forall {n : Nat} (s : Fin n)
    (P : Fin n → Prop) (remaining : Nat) :
    ∀ start,
      (∀ j, start ≤ j → j < start + remaining → P (certSite s j)) →
      ∀ a, a ∈ coverageMarks s start remaining → P a := by
  induction remaining with
  | zero =>
      intro start hP a ha
      simp [coverageMarks] at ha
  | succ remaining ih =>
      intro start hP a ha
      simp only [coverageMarks, List.mem_cons] at ha
      rcases ha with ha | ha
      · subst a
        exact hP start (Nat.le_refl _) (by omega)
      · exact ih (start + 1)
          (by
            intro j hj hjtop
            apply hP j <;> omega) a ha

private theorem mul_one_factors (a b : Nat) (h : a * b = 1) :
    a = 1 ∧ b = 1 := by
  have ha : 0 < a := by
    by_cases hz : a = 0
    · simp [hz] at h
    · omega
  have hb : 0 < b := by
    by_cases hz : b = 0
    · simp [hz] at h
    · omega
  have haOne : 1 ≤ a := by omega
  have hbOne : 1 ≤ b := by omega
  have hleft : a ≤ 1 := by
    calc
      a = a * 1 := (Nat.mul_one a).symm
      _ ≤ a * b := Nat.mul_le_mul_left a hbOne
      _ = 1 := h
  have hright : b ≤ 1 := by
    calc
      b = 1 * b := (Nat.one_mul b).symm
      _ ≤ a * b := Nat.mul_le_mul_right b haOne
      _ = 1 := h
  exact ⟨by omega, by omega⟩

theorem markedSlots_launch_sound {n q : Nat}
    (width : Nat) (outside : Fin n → Bool) (s : Fin n)
    (hOutside : ∀ e, outside e = true → ¬ LaunchEdge (q := q) s e)
    (word : List (Fin n)) (hlen : word.length = width * 2)
    (haccept : markedSlots width outside
      [certSite s (n - 1), certSite s (n - 1)] word = 1) :
    LaunchSegment (q := q) s word := by
  simp only [markedSlots] at haccept
  have hfirst := (mul_one_factors _ _ haccept).1
  have hsecond := (mul_one_factors _ _ (mul_one_factors _ _ haccept).2).1
  obtain ⟨firstBefore, firstAfter, hfirstWord, hfirstBefore, hfirstAfter⟩ :=
    oneMark_sound outside (certSite s (n - 1)) (word.take width) hfirst
  obtain ⟨secondBefore, secondAfter, hsecondWord, hsecondBefore, hsecondAfter⟩ :=
    oneMark_sound outside (certSite s (n - 1))
      ((word.drop width).take width) hsecond
  have hrestLength : ((word.drop width).drop width).length = 0 := by
    simp only [List.length_drop, hlen]
    omega
  have hrest : (word.drop width).drop width = [] := by
    cases he : (word.drop width).drop width with
    | nil => rfl
    | cons e tail =>
        simp only [he, List.length_cons] at hrestLength
        omega
  refine ⟨firstBefore, firstAfter ++ secondBefore, secondAfter, ?_, ?_, ?_, ?_⟩
  · calc
      word = word.take width ++ word.drop width :=
        (List.take_append_drop width word).symm
      _ = (firstBefore ++ [certSite s (n - 1)] ++ firstAfter) ++
          ((word.drop width).take width ++ (word.drop width).drop width) :=
        (congrArg (· ++ word.drop width) hfirstWord).trans
          (congrArg (_ ++ ·)
            (List.take_append_drop width (word.drop width)).symm)
      _ = (firstBefore ++ [certSite s (n - 1)] ++
          (firstAfter ++ secondBefore) ++ [certSite s (n - 1)]) ++
          secondAfter := by
        simp only [hsecondWord, hrest, List.append_nil, List.append_assoc]
  · intro e he
    exact hOutside e (hfirstBefore e he)
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hOutside e (hfirstAfter e he)
    · exact hOutside e (hsecondBefore e he)
  · intro e he
    exact hOutside e (hsecondAfter e he)

theorem coverageWord_prepend_outside {n q : Nat}
    (s : Fin n) (j : Fin (compileAdvice q).t)
    (word : List (Fin n)) (hword : CoverageWord (q := q) s j word) :
    ∀ before : List (Fin n),
      (∀ e, e ∈ before → OutsideCoverage (q := q) s e) →
      CoverageWord (q := q) s j (before ++ word) := by
  intro before
  induction before with
  | nil =>
      intro hbefore
      exact hword
  | cons e rest ih =>
      intro hbefore
      exact CoverageWord.delay (q := q) j e (rest ++ word)
        (hbefore e (by simp))
        (ih (by
          intro a ha
          exact hbefore a (by simp [ha])))

theorem markedSlots_coverage_sound {n q : Nat}
    (width : Nat) (outside : Fin n → Bool) (s : Fin n)
    (hOutside : ∀ e, outside e = true → OutsideCoverage (q := q) s e)
    (remaining : Nat) :
    ∀ (j : Fin (compileAdvice q).t) (word : List (Fin n)),
      j.val + remaining = (compileAdvice q).t →
      0 < remaining →
      markedSlots width outside (coverageMarks s j.val remaining) word = 1 →
      CoverageSegment (q := q) s j word := by
  induction remaining with
  | zero =>
      intro j word hsum hpositive haccept
      omega
  | succ remaining ih =>
      intro j word hsum hpositive haccept
      simp only [coverageMarks, markedSlots] at haccept
      have hfirst := (mul_one_factors _ _ haccept).1
      have hrestAccept := (mul_one_factors _ _ haccept).2
      obtain ⟨before, after, hslot, hbefore, hafter⟩ :=
        oneMark_sound outside (certSite s j.val) (word.take width) hfirst
      have hbeforeOutside : ∀ e, e ∈ before → OutsideCoverage (q := q) s e := by
        intro e he
        exact hOutside e (hbefore e he)
      have hafterOutside : ∀ e, e ∈ after → OutsideCoverage (q := q) s e := by
        intro e he
        exact hOutside e (hafter e he)
      have hsplit :
          word = before ++ [certSite s j.val] ++ (after ++ word.drop width) := by
        calc
          word = word.take width ++ word.drop width :=
            (List.take_append_drop width word).symm
          _ = before ++ [certSite s j.val] ++ (after ++ word.drop width) := by
            simp only [hslot, List.append_assoc]
      by_cases hzero : remaining = 0
      · subst remaining
        have hlast : j.val + 1 = (compileAdvice q).t := by omega
        refine ⟨before ++ [certSite s j.val], after ++ word.drop width, hsplit, ?_⟩
        exact coverageWord_prepend_outside (q := q) s j [certSite s j.val]
          (CoverageWord.final (q := q) j hlast) before hbeforeOutside
      · have hremaining : 0 < remaining := by omega
        have hnext : j.val + 1 < (compileAdvice q).t := by omega
        let next : Fin (compileAdvice q).t := ⟨j.val + 1, hnext⟩
        have hnextsum : next.val + remaining = (compileAdvice q).t := by
          dsimp only [next]
          omega
        obtain ⟨front, tail, hrest, hcoverage⟩ :=
          ih next (word.drop width) hnextsum hremaining hrestAccept
        have hafterCoverage :
            CoverageWord (q := q) s next (after ++ front) :=
          coverageWord_prepend_outside (q := q) s next front hcoverage after hafterOutside
        let newFront := (before ++ [certSite s j.val] ++ after) ++ front
        have hnewCoverage : CoverageWord (q := q) s j newFront := by
          simpa only [newFront, List.append_assoc, List.cons_append, List.nil_append] using
            coverageWord_prepend_outside (q := q) s j
              (certSite s j.val :: (after ++ front))
              (CoverageWord.advance (q := q) j hnext (after ++ front) hafterCoverage)
              before hbeforeOutside
        refine ⟨newFront, tail, ?_, hnewCoverage⟩
        calc
          word = before ++ [certSite s j.val] ++ (after ++ word.drop width) := hsplit
          _ = newFront ++ tail := by
            simp only [hrest, newFront, List.append_assoc]

end L3.FreshFixed

namespace L3.FreshFixed

open FreshReference

theorem fixedRun_append {S E : Type} (next : S → E → S)
    (x : S) (left right : List E) :
    LDSinkBoundedKernel.run next x (left ++ right) =
      LDSinkBoundedKernel.run next
        (LDSinkBoundedKernel.run next x left) right := by
  induction left generalizing x with
  | nil => rfl
  | cons e rest ih => exact ih (next x e)

theorem fixedGhostRun_projection {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (z : FreshGhostConfig n q) (word : List (Fin n)) :
    (LDSinkBoundedKernel.run (freshGhostStep ring fixed s) z word).1 =
      runList ring fixed z.1 word := by
  induction word generalizing z with
  | nil => rfl
  | cons e rest ih => exact ih (freshGhostStep ring fixed s z e)

theorem fixedGhostRun_sticky {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (word : List (Fin n)) :
    ∀ z : FreshGhostConfig n q, freshGhostGood z →
      freshGhostGood
        (LDSinkBoundedKernel.run (freshGhostStep ring fixed s) z word) := by
  induction word with
  | nil => intro z hz; exact hz
  | cons e rest ih =>
      intro z hz
      exact ih (freshGhostStep ring fixed s z e)
        (freshGhost_flag_sticky ring fixed s z e hz)

theorem fixed_raw_reject_row (c : Compiled)
    (x y : Agent c) (post : PostE)
    (hreport : (rawD1Step c x y post).reject = true) :
    (rawD1Step c x y post).row = "R0c" := by
  cases hx : x.rawTok with
  | none =>
      cases hy : y.rawTok with
      | none =>
          cases hk : y.rawKick <;>
            simp [rawD1Step, hx, hy, hk] at hreport
      | some resident =>
          simp [rawD1Step, hx, hy] at hreport
  | some tok =>
      cases hy : y.rawTok with
      | some resident =>
          simp [rawD1Step, hx, hy] at hreport
      | none =>
          by_cases hj : tok.j < c.t
          · simp [rawD1Step, hx, hy, hj] at hreport
          · simp [rawD1Step, hx, hy, hj]

theorem outsideLaunch_implies_outsideCoverage {n q : Nat}
    (s e : Fin n) (hn : 2 ≤ n)
    (hout : ¬ LaunchEdge (q := q) s e) :
    OutsideCoverage (q := q) s e := by
  intro j he
  apply hout
  rw [he]
  exact launchEdge_sampled s hn j

/-- The outstanding deterministic premise is only genealogy at the
terminal service of a guarded word. It contains no rejection, flag,
success-count, retry-cost, or finite-horizon-budget assertion. -/
def FixedWordGenealogy {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t) : Prop :=
  ∀ (z : FreshGhostConfig n q)
    (clear before between coverage : List (Fin n)),
    Frozen fixed z.1 →
    FreshCoupon.lastAccept ((compileAdvice q).t + 3)
      (clear.map (protectedLabel s)) = 1 →
    (∀ e, e ∈ before → ¬ LaunchEdge (q := q) s e) →
    (∀ e, e ∈ between → ¬ LaunchEdge (q := q) s e) →
    CoverageWord (q := q) s ⟨0, by omega⟩ coverage →
    ∀ front : List (Fin n),
      ((clear ++ (before ++ [certSite s (n - 1)] ++
        between ++ [certSite s (n - 1)])) ++ coverage) =
          front ++ [certSite s ((compileAdvice q).t - 1)] →
      (LDSinkBoundedKernel.run
        (freshGhostStep ring fixed s) z front).2.trail
          (certSite s ((compileAdvice q).t - 1)) =
        some { origin := s, hops := (compileAdvice q).t - 1 }

/-- The physical report plus the explicitly isolated genealogy
premise makes the sticky ghost flag true. Trailing padding is arbitrary. -/
theorem fixed_segments_ghost_flag {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (hgenealogy : FixedWordGenealogy ring fixed s ht)
    (z : FreshGhostConfig n q) (hFrozen : Frozen fixed z.1)
    (clear launch coverage : List (Fin n))
    (hclear : FreshCoupon.lastAccept ((compileAdvice q).t + 3)
      (clear.map (protectedLabel s)) = 1)
    (hlaunch : LaunchSegment (q := q) s launch)
    (hcoverage : CoverageSegment (q := q) s ⟨0, by omega⟩ coverage) :
    freshGhostGood (LDSinkBoundedKernel.run
      (freshGhostStep ring fixed s) z ((clear ++ launch) ++ coverage)) := by
  obtain ⟨before, between, after, hlaunchWord, hbefore, hbetween, hafter⟩ := hlaunch
  obtain ⟨coverFront, coverTail, hcoverageWord, hcoverFront⟩ := hcoverage
  have hafterCoverage : ∀ e, e ∈ after → OutsideCoverage (q := q) s e := by
    intro e he
    exact outsideLaunch_implies_outsideCoverage (q := q) s e (by omega) (hafter e he)
  have hwholeCoverage :
      CoverageWord (q := q) s ⟨0, by omega⟩ (after ++ coverFront) :=
    coverageWord_prepend_outside (q := q) s ⟨0, by omega⟩ coverFront hcoverFront
      after hafterCoverage
  obtain ⟨len, indexed, hindexedWord⟩ := finiteLetters_surjective clear
  have hindexed :
      FreshCoupon.lastAccept ((compileAdvice q).t + 3)
        ((finiteLetters len indexed).map (protectedLabel s)) = 1 := by
    simpa only [hindexedWord] using hclear
  obtain ⟨front, hcore, hreport⟩ :=
    clearing_launch_coverage_report ring fixed z.1 s ht hn hroot
      hFrozen hbad indexed hindexed before between (after ++ coverFront)
      hbefore hbetween hwholeCoverage
  have hcoreList :
      ((clear ++ (before ++ [certSite s (n - 1)] ++
        between ++ [certSite s (n - 1)])) ++ (after ++ coverFront)) =
        front ++ [certSite s ((compileAdvice q).t - 1)] := by
    simpa only [hindexedWord] using hcore
  let terminal := certSite s ((compileAdvice q).t - 1)
  let atTerminal := LDSinkBoundedKernel.run
    (freshGhostStep ring fixed s) z front
  have hphysical : atTerminal.1 = runList ring fixed z.1 front :=
    fixedGhostRun_projection ring fixed s z front
  have htrail : atTerminal.2.trail terminal =
      some { origin := s, hops := (compileAdvice q).t - 1 } :=
    hgenealogy z clear before between (after ++ coverFront)
      hFrozen hclear hbefore hbetween hwholeCoverage front hcoreList
  have hreportPhysical :
      (rawResult ring (runList ring fixed z.1 front) terminal).reject = true :=
    hreport
  have hrowPhysical :
      (rawResult ring (runList ring fixed z.1 front) terminal).row = "R0c" :=
    fixed_raw_reject_row _ _ _ _ hreportPhysical
  have hreportGhost : (rawResult ring atTerminal.1 terminal).reject = true := by
    simpa only [hphysical] using hreportPhysical
  have hrowGhost : (rawResult ring atTerminal.1 terminal).row = "R0c" := by
    simpa only [hphysical] using hrowPhysical
  have hterminalIndex : (compileAdvice q).t - 1 + 1 = (compileAdvice q).t := by
    omega
  have hselected :
      freshSelectedReject ring atTerminal.1 atTerminal.2 terminal = true := by
    simp [freshSelectedReject, htrail, hterminalIndex, terminal,
      hrowGhost, hreportGhost]
  have hgood : freshGhostGood
      (freshGhostStep ring fixed s atTerminal terminal) := by
    simp [freshGhostGood, freshGhost_flag_step, hselected]
  have hword :
      (clear ++ launch) ++ coverage = (front ++ [terminal]) ++ coverTail := by
    calc
      (clear ++ launch) ++ coverage =
          (((clear ++ (before ++ [certSite s (n - 1)] ++
            between ++ [certSite s (n - 1)])) ++
              (after ++ coverFront)) ++ coverTail) := by
        simp only [hlaunchWord, hcoverageWord, List.append_assoc]
      _ = (front ++ [terminal]) ++ coverTail := by
        rw [hcoreList]
  have hpadded := fixedGhostRun_sticky ring fixed s coverTail
    (freshGhostStep ring fixed s atTerminal terminal) hgood
  simpa only [hword, fixedRun_append, LDSinkBoundedKernel.run, atTerminal] using hpadded

end L3.FreshFixed

namespace L3.Prob.FixedAttempts

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open LeaderCountDyadicTail
open LDSinkBoundedKernel

set_option autoImplicit false
set_option Elab.async false

theorem accepted_count_le_total {n : Nat}
    (W : Nat) (accept : List (Fin n) → Nat)
    (hrange : ∀ w, w.length = W → accept w ≤ 1) :
    scheduleSum n W accept ≤ n ^ W := by
  change FixedSpanRenewalPayload.wordSum n W accept ≤ n ^ W
  rw [← FixedSpanRenewalPayload.rawWord_sum]
  have hs := ofFn_sum_le
    (fun i : Fin (n ^ W) => accept (FixedSpanRenewalPayload.rawWord n W i))
    (fun _ : Fin (n ^ W) => 1)
    (fun i => hrange _ (FixedSpanRenewalPayload.rawWord_length n W i))
  simpa only [ofFn_sum_const, Nat.mul_one] using hs

/-- Accepted words and missed endpoints are disjoint on the same word. -/
theorem accepted_add_miss_le_total {S : Type} {n : Nat}
    (next : S → Fin n → S) (Good : S → Prop)
    (W : Nat) (accept : List (Fin n) → Nat)
    (hrange : ∀ w, w.length = W → accept w ≤ 1)
    (x : S)
    (hsound : ∀ w, w.length = W → accept w = 1 →
      Good (run next x w)) :
    scheduleSum n W accept + wordSum next (miss Good) x W ≤ n ^ W := by
  classical
  have hpoint (i : Fin (n ^ W)) :
      accept (FixedSpanRenewalPayload.rawWord n W i) +
        miss Good (run next x (FixedSpanRenewalPayload.rawWord n W i)) ≤ 1 := by
    have hl := FixedSpanRenewalPayload.rawWord_length n W i
    have ha := hrange _ hl
    by_cases he : accept (FixedSpanRenewalPayload.rawWord n W i) = 1
    · have hg := hsound _ hl he
      simpa only [miss, if_pos hg, Nat.add_zero] using ha
    · have hz : accept (FixedSpanRenewalPayload.rawWord n W i) = 0 := by omega
      simpa only [hz, Nat.zero_add] using
        miss_le_one Good (run next x (FixedSpanRenewalPayload.rawWord n W i))
  have hs := ofFn_sum_le
    (fun i : Fin (n ^ W) =>
      accept (FixedSpanRenewalPayload.rawWord n W i) +
        miss Good (run next x (FixedSpanRenewalPayload.rawWord n W i)))
    (fun _ : Fin (n ^ W) => 1) hpoint
  rw [ofFn_sum_add] at hs
  have hfirst :
      (List.ofFn (fun i : Fin (n ^ W) =>
        accept (FixedSpanRenewalPayload.rawWord n W i))).sum =
        scheduleSum n W accept :=
    FixedSpanRenewalPayload.rawWord_sum n W accept
  have hsecond :
      (List.ofFn (fun i : Fin (n ^ W) =>
        miss Good (run next x
          (FixedSpanRenewalPayload.rawWord n W i)))).sum =
        wordSum next (miss Good) x W := by
    calc
      _ = FixedSpanRenewalPayload.wordSum n W
          (fun es => miss Good (run next x es)) :=
        FixedSpanRenewalPayload.rawWord_sum n W
          (fun es => miss Good (run next x es))
      _ = wordSum next (miss Good) x W :=
        K2FiniteSafeEliminationExpected.wordSum_run next (miss Good) x W
  rw [hfirst, hsecond, ofFn_sum_const, Nat.mul_one] at hs
  exact hs

/-- Strong induction over fixed blocks of W raw scheduler letters.
Continuation starts at the actual endpoint of each failed block. -/
theorem fixed_cost_of_miss_count {S : Type} {n : Nat}
    (next : S → Fin n → S) (Good Eligible : S → Prop)
    (hsticky : ∀ x e, Good x → Good (next x e))
    (hclosed : ∀ x e, Eligible x → Eligible (next x e))
    (W K : Nat) (hW : 0 < W) (hK : 0 < K) (hKtotal : K ≤ n ^ W)
    (hmiss : ∀ x, Eligible x →
      wordSum next (miss Good) x W ≤ n ^ W - K) :
    ∀ T x, Eligible x →
      costNumerator next Good x T ≤ n ^ T * ceilNat (W * n ^ W) K := by
  classical
  let C := ceilNat (W * n ^ W) K
  have hN : 0 < n ^ W := Nat.lt_of_lt_of_le hK hKtotal
  have hrho : n ^ W - K < n ^ W := by omega
  have hsub : n ^ W - (n ^ W - K) = K := by omega
  have hbudget : n ^ W * W + (n ^ W - K) * C ≤ n ^ W * C := by
    have hh := renewalCeiling_budget W (n ^ W - K) (n ^ W) hrho
    simpa only [renewalCeiling, hsub, C] using hh
  have hbase : W ≤ C := by
    have hm : n ^ W * W ≤ n ^ W * C :=
      Nat.le_trans (Nat.le_add_right _ _) hbudget
    exact Nat.le_of_mul_le_mul_left hm hN
  intro T
  induction T using Nat.strongRecOn with
  | ind T ih =>
      intro x hx
      by_cases hsmall : T ≤ W
      · exact Nat.le_trans (costNumerator_le_horizon next Good x T)
          (Nat.mul_le_mul_left _ (Nat.le_trans hsmall hbase))
      · let U := T - W
        have hU : U < T := by dsimp [U]; omega
        have hT : T = W + U := by dsimp [U]; omega
        have hpoint : ∀ y, Eligible y →
            costNumerator next Good y U ≤ (n ^ U * C) * miss Good y := by
          intro y hy
          by_cases hg : Good y
          · rw [costNumerator_terminal next Good y hg]
            exact Nat.zero_le _
          · simpa only [miss, if_neg hg, Nat.mul_one] using ih U hU y hy
        have htail := wordSum_mono_on next Eligible hclosed
          (fun y => costNumerator next Good y U)
          (fun y => (n ^ U * C) * miss Good y)
          hpoint W x hx
        rw [wordSum_mul] at htail
        rw [hT, costNumerator_split next Good hsticky]
        calc
          n ^ U * costNumerator next Good x W +
              wordSum next (fun y => costNumerator next Good y U) x W ≤
              n ^ U * (n ^ W * W) +
                (n ^ U * C) * wordSum next (miss Good) x W :=
            Nat.add_le_add
              (Nat.mul_le_mul_left _ (costNumerator_le_horizon next Good x W)) htail
          _ ≤ n ^ U * (n ^ W * W) + (n ^ U * C) * (n ^ W - K) :=
            Nat.add_le_add_left (Nat.mul_le_mul_left _ (hmiss x hx)) _
          _ = n ^ U * (n ^ W * W + (n ^ W - K) * C) := by
            rw [Nat.mul_add]
            congr 1
            ac_rfl
          _ ≤ n ^ U * (n ^ W * C) := Nat.mul_le_mul_left _ hbudget
          _ = n ^ (W + U) * ceilNat (W * n ^ W) K := by
            change n ^ U * (n ^ W * C) = n ^ (W + U) * C
            rw [Nat.pow_add]
            ac_rfl

/-- The count is established once for words; soundness applies uniformly
on a closed state domain. No finite-horizon attempt budget is assumed. -/
theorem fixed_attempt_cost {S : Type} {n : Nat}
    (next : S → Fin n → S) (Good Eligible : S → Prop)
    (hsticky : ∀ x e, Good x → Good (next x e))
    (hclosed : ∀ x e, Eligible x → Eligible (next x e))
    (W K : Nat) (hW : 0 < W) (hK : 0 < K)
    (accept : List (Fin n) → Nat)
    (hrange : ∀ w, w.length = W → accept w ≤ 1)
    (hcount : K ≤ scheduleSum n W accept)
    (hsound : ∀ x, Eligible x → ∀ w,
      w.length = W → accept w = 1 → Good (run next x w)) :
    ∀ T x, Eligible x →
      costNumerator next Good x T ≤ n ^ T * ceilNat (W * n ^ W) K := by
  have hKtotal : K ≤ n ^ W :=
    Nat.le_trans hcount (accepted_count_le_total W accept hrange)
  have hm : ∀ x, Eligible x →
      wordSum next (miss Good) x W ≤ n ^ W - K := by
    intro x hx
    have hh := accepted_add_miss_le_total next Good W accept hrange x (hsound x hx)
    omega
  exact fixed_cost_of_miss_count next Good Eligible hsticky hclosed
    W K hW hK hKtotal hm

end L3.Prob.FixedAttempts

namespace L3.FreshFixed

open FreshReference
open K2ArbitraryElimination.FiniteAccounting

theorem coverageMarks_outside_false {n q : Nat}
    (s : Fin n) (hn : (compileAdvice q).t + 3 ≤ n)
    (start remaining : Nat)
    (hbound : start + remaining ≤ (compileAdvice q).t) :
    ∀ a, a ∈ coverageMarks s start remaining →
      outsideCoverage (q := q) s a = false := by
  apply coverageMarks_forall s
    (fun a => outsideCoverage (q := q) s a = false) remaining start
  intro j hj hjtop
  exact outsideCoverage_mark_false s hn j (by omega)

def launchAccept {n q : Nat} (s : Fin n) (word : List (Fin n)) : Nat :=
  markedSlots (slotWidth n ((compileAdvice q).t + 2))
    (outsideLaunch (q := q) s)
    [certSite s (n - 1), certSite s (n - 1)] word

def coverageAccept {n q : Nat} (s : Fin n) (word : List (Fin n)) : Nat :=
  markedSlots (slotWidth n (compileAdvice q).t)
    (outsideCoverage (q := q) s)
    (coverageMarks s 0 (compileAdvice q).t) word

/-- A state-independent zero/one predicate on exactly one fixed block.
No phase counter, stopping time, or physical state occurs here. -/
def attemptAccept {n q : Nat} (s : Fin n) (word : List (Fin n)) : Nat :=
  FreshCoupon.lastAccept ((compileAdvice q).t + 3)
    ((word.take (6 * n)).map (protectedLabel s)) *
  (launchAccept (q := q) s
      ((word.drop (6 * n)).take (launchLength n (compileAdvice q).t)) *
    coverageAccept (q := q) s
      ((word.drop (6 * n)).drop (launchLength n (compileAdvice q).t)))

theorem launch_count {n q : Nat} (s : Fin n)
    (hwidth : (compileAdvice q).t + 3 ≤ n) :
    Prob.scheduleSum n (launchLength n (compileAdvice q).t)
      (launchAccept (q := q) s) = launchLower n (compileAdvice q).t := by
  have hmarks : ∀ a,
      a ∈ [certSite s (n - 1), certSite s (n - 1)] →
        outsideLaunch (q := q) s a = false := by
    intro a ha
    have he : a = certSite s (n - 1) := by simpa using ha
    subst a
    exact outsideLaunch_mark_false s hwidth
  have h := markedSlots_count n (slotWidth n ((compileAdvice q).t + 2))
    (outsideLaunch (q := q) s)
    [certSite s (n - 1), certSite s (n - 1)] hmarks
  rw [outsideLaunch_size s hwidth] at h
  change Prob.scheduleSum n (launchLength n (compileAdvice q).t)
    (launchAccept (q := q) s) = launchLower n (compileAdvice q).t at h
  exact h

theorem coverage_count {n q : Nat} (s : Fin n)
    (hwidth : (compileAdvice q).t + 3 ≤ n) :
    Prob.scheduleSum n (coverageLength n (compileAdvice q).t)
      (coverageAccept (q := q) s) = coverageLower n (compileAdvice q).t := by
  have h := markedSlots_count n (slotWidth n (compileAdvice q).t)
    (outsideCoverage (q := q) s)
    (coverageMarks s 0 (compileAdvice q).t)
    (coverageMarks_outside_false s hwidth 0 (compileAdvice q).t (by omega))
  rw [outsideCoverage_size s hwidth,
    coverageMarks_length s (compileAdvice q).t 0] at h
  change Prob.scheduleSum n (coverageLength n (compileAdvice q).t)
    (coverageAccept (q := q) s) = coverageLower n (compileAdvice q).t at h
  exact h

/-- Exact count, hence in particular the required R * Sl * Sc lower bound. -/
theorem attempt_count {n q : Nat} (s : Fin n)
    (hwidth : (compileAdvice q).t + 3 ≤ n) :
    Prob.scheduleSum n (attemptLength n (compileAdvice q).t)
      (attemptAccept (q := q) s) = successLower n (compileAdvice q).t := by
  let t := (compileAdvice q).t
  let A : List (Fin n) → Nat :=
    fun w => FreshCoupon.lastAccept (t + 3) (w.map (protectedLabel s))
  let L : List (Fin n) → Nat := launchAccept (q := q) s
  let C : List (Fin n) → Nat := coverageAccept (q := q) s
  change Prob.scheduleSum n
      (6 * n + (launchLength n t + coverageLength n t))
      (fun word => A (word.take (6 * n)) *
        (L ((word.drop (6 * n)).take (launchLength n t)) *
          C ((word.drop (6 * n)).drop (launchLength n t)))) =
    successLower n t
  calc
    _ = Prob.scheduleSum n (6 * n) A *
          Prob.scheduleSum n (launchLength n t + coverageLength n t)
            (fun rest => L (rest.take (launchLength n t)) *
              C (rest.drop (launchLength n t))) :=
        sum_split_product n (6 * n)
          (launchLength n t + coverageLength n t) A
          (fun rest => L (rest.take (launchLength n t)) *
            C (rest.drop (launchLength n t)))
    _ = Prob.scheduleSum n (6 * n) A *
          (Prob.scheduleSum n (launchLength n t) L *
            Prob.scheduleSum n (coverageLength n t) C) := by
        rw [sum_split_product n (launchLength n t) (coverageLength n t) L C]
    _ = successLower n t := by
        dsimp only [A, L, C, t]
        rw [protected_last_count s (6 * n) hwidth,
          launch_count s hwidth, coverage_count s hwidth]
        unfold successLower FreshCoupon.clearCountSix
        ac_rfl

theorem launchAccept_le_one {n q : Nat}
    (s : Fin n) (word : List (Fin n)) :
    launchAccept (q := q) s word ≤ 1 := by
  have h := markedSlots_range
    (slotWidth n ((compileAdvice q).t + 2))
    (outsideLaunch (q := q) s)
    [certSite s (n - 1), certSite s (n - 1)] word
  change launchAccept (q := q) s word = 0 ∨
    launchAccept (q := q) s word = 1 at h
  omega

theorem coverageAccept_le_one {n q : Nat}
    (s : Fin n) (word : List (Fin n)) :
    coverageAccept (q := q) s word ≤ 1 := by
  have h := markedSlots_range
    (slotWidth n (compileAdvice q).t)
    (outsideCoverage (q := q) s)
    (coverageMarks s 0 (compileAdvice q).t) word
  change coverageAccept (q := q) s word = 0 ∨
    coverageAccept (q := q) s word = 1 at h
  omega

theorem attemptAccept_le_one {n q : Nat}
    (s : Fin n) (word : List (Fin n)) :
    attemptAccept (q := q) s word ≤ 1 := by
  have hc :
      FreshCoupon.lastAccept ((compileAdvice q).t + 3)
        ((word.take (6 * n)).map (protectedLabel s)) ≤ 1 := by
    have h := FreshCoupon.orderedAccept_range ((compileAdvice q).t + 3)
      (((word.take (6 * n)).map (protectedLabel s)).reverse)
    change FreshCoupon.lastAccept ((compileAdvice q).t + 3)
        ((word.take (6 * n)).map (protectedLabel s)) = 0 ∨
      FreshCoupon.lastAccept ((compileAdvice q).t + 3)
        ((word.take (6 * n)).map (protectedLabel s)) = 1 at h
    omega
  unfold attemptAccept
  exact Nat.mul_le_mul hc
    (Nat.mul_le_mul
      (launchAccept_le_one s
        ((word.drop (6 * n)).take (launchLength n (compileAdvice q).t)))
      (coverageAccept_le_one s
        ((word.drop (6 * n)).drop (launchLength n (compileAdvice q).t))))

/-- Wordwise soundness uses the existing physical report theorem and
only the named terminal-genealogy premise. -/
theorem attempt_sound {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hwidth : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (hgenealogy : FixedWordGenealogy ring fixed s ht)
    (z : FreshGhostConfig n q) (hz : Frozen fixed z.1)
    (word : List (Fin n))
    (hlen : word.length = attemptLength n (compileAdvice q).t)
    (haccept : attemptAccept (q := q) s word = 1) :
    freshGhostGood
      (LDSinkBoundedKernel.run (freshGhostStep ring fixed s) z word) := by
  let clear := word.take (6 * n)
  let rest := word.drop (6 * n)
  let launch := rest.take (launchLength n (compileAdvice q).t)
  let cover := rest.drop (launchLength n (compileAdvice q).t)
  have hparts :
      FreshCoupon.lastAccept ((compileAdvice q).t + 3)
          (clear.map (protectedLabel s)) *
        (launchAccept (q := q) s launch * coverageAccept (q := q) s cover) = 1 :=
    haccept
  have hc := (mul_one_factors _ _ hparts).1
  have hl := (mul_one_factors _ _ (mul_one_factors _ _ hparts).2).1
  have hb := (mul_one_factors _ _ (mul_one_factors _ _ hparts).2).2
  have hrest : rest.length =
      launchLength n (compileAdvice q).t + coverageLength n (compileAdvice q).t := by
    dsimp only [rest]
    rw [List.length_drop, hlen]
    unfold attemptLength
    omega
  have hlaunch : launch.length = slotWidth n ((compileAdvice q).t + 2) * 2 := by
    dsimp only [launch]
    rw [List.length_take, hrest]
    unfold launchLength
    omega
  have hlaunchSound : LaunchSegment (q := q) s launch :=
    markedSlots_launch_sound (q := q)
      (slotWidth n ((compileAdvice q).t + 2)) (outsideLaunch (q := q) s) s
      (fun e he => (outsideLaunch_true_iff s hwidth e).mp he)
      launch hlaunch hl
  have hcoverageSound :
      CoverageSegment (q := q) s ⟨0, by omega⟩ cover :=
    markedSlots_coverage_sound (q := q)
      (slotWidth n (compileAdvice q).t) (outsideCoverage (q := q) s) s
      (fun e he => (outsideCoverage_true_iff s hwidth e).mp he)
      (compileAdvice q).t ⟨0, by omega⟩ cover (by simp) (by omega) hb
  have hw : (clear ++ launch) ++ cover = word := by
    dsimp only [clear, launch, cover, rest]
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  have h := fixed_segments_ghost_flag ring fixed s ht hwidth hroot hbad
    hgenealogy z hz clear launch cover hc hlaunchSound hcoverageSound
  simpa only [hw] using h

/-- Fixed attempts solve the finite-horizon cost obligation. The sole
non-arithmetic scientific premise is the explicitly stated genealogy
fact; neither SixPaperBudget nor FreshPhaseSound is used. -/
theorem freshGhost_cost_fixedAttempts {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hwidth : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (hgenealogy : FixedWordGenealogy ring fixed s ht)
    (z : FreshGhostConfig n q) (hz : Frozen fixed z.1) :
    ∀ T,
      costNumerator (freshGhostStep ring fixed s) freshGhostGood z T ≤
        n ^ T * attemptCeiling n (compileAdvice q).t := by
  intro T
  exact Prob.FixedAttempts.fixed_attempt_cost
    (freshGhostStep ring fixed s) freshGhostGood (fun x => Frozen fixed x.1)
    (freshGhost_flag_sticky ring fixed s)
    (by
      intro x e hx
      exact step_frozen ring fixed x.1 hx e)
    (attemptLength n (compileAdvice q).t)
    (successLower n (compileAdvice q).t)
    (attemptLength_pos n (compileAdvice q).t (by omega))
    (successLower_pos n (compileAdvice q).t hwidth)
    (attemptAccept (q := q) s)
    (fun word _ => attemptAccept_le_one s word)
    (Nat.le_of_eq (attempt_count s hwidth).symm)
    (fun x hx word hw ha =>
      attempt_sound ring fixed s ht hwidth hroot hbad hgenealogy x hx word hw ha)
    T z hz

end L3.FreshFixed

namespace L3.FreshFixed

/-- Arithmetic for the exact ceiling used by the stopping-cost API. -/
theorem ceiling_budget (a d : Nat) (hd : 0 < d) :
    a ≤ d * Prob.ceilNat a d := by
  have he : d * (a / d) + a % d = a := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod a d
  have hr := Nat.mod_lt a hd
  by_cases hz : a % d = 0
  · simp only [Prob.ceilNat, if_pos hz, Nat.add_zero]
    omega
  · simp only [Prob.ceilNat, if_neg hz, Nat.mul_add, Nat.mul_one]
    omega

theorem ceiling_le_of_budget (a d C : Nat) (hd : 0 < d)
    (h : a ≤ d * C) :
    Prob.ceilNat a d ≤ C := by
  have he : d * (a / d) + a % d = a := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod a d
  by_cases hz : a % d = 0
  · have hm : d * (a / d) ≤ d * C := by omega
    have hq := Nat.le_of_mul_le_mul_left hm hd
    simpa only [Prob.ceilNat, if_pos hz, Nat.add_zero] using hq
  · have hq : a / d < C := by
      by_cases hc : C ≤ a / d
      · have hm := Nat.mul_le_mul_left d hc
        omega
      · omega
    simpa only [Prob.ceilNat, if_neg hz] using Nat.succ_le_of_lt hq

theorem ceiling_ratio_mono (a d b e : Nat)
    (hd : 0 < d) (he : 0 < e) (h : a * e ≤ b * d) :
    Prob.ceilNat a d ≤ Prob.ceilNat b e := by
  have hb := ceiling_budget b e he
  have hc : e * a ≤ e * (d * Prob.ceilNat b e) := by
    calc
      e * a = a * e := Nat.mul_comm _ _
      _ ≤ b * d := h
      _ ≤ (e * Prob.ceilNat b e) * d := Nat.mul_le_mul_right d hb
      _ = e * (d * Prob.ceilNat b e) := by ac_rfl
  exact ceiling_le_of_budget a d (Prob.ceilNat b e) hd
    (Nat.le_of_mul_le_mul_left hc he)

/-- Cross-multiplied comparison: it is valid with the exact R
and does not require a zero coupon deficit. -/
theorem attempt_ratio_bound (n t : Nat)
    (ht : 2 ≤ t) (hwidth : t + 3 ≤ n) :
    (attemptLength n t * n ^ attemptLength n t) *
        FreshCoupon.clearCountSix n t ≤
      (8 * n * n ^ (6 * n) * segmentPenalty t) * successLower n t := by
  have hs := segments_fraction n t (by omega) hwidth
  have hw :
      n ^ attemptLength n t ≤
        n ^ (6 * n) * (segmentPenalty t * (launchLower n t * coverageLower n t)) := by
    unfold attemptLength
    rw [Nat.pow_add]
    exact Nat.mul_le_mul_left _ hs
  have h := Nat.mul_le_mul (attemptLength_le n t ht hwidth) hw
  calc
    (attemptLength n t * n ^ attemptLength n t) *
        FreshCoupon.clearCountSix n t ≤
      ((8 * n) * (n ^ (6 * n) *
        (segmentPenalty t * (launchLower n t * coverageLower n t)))) *
          FreshCoupon.clearCountSix n t :=
      Nat.mul_le_mul_right _ h
    _ = (8 * n * n ^ (6 * n) * segmentPenalty t) * successLower n t := by
      unfold successLower
      ac_rfl

theorem attemptCeiling_le_discrete (n t : Nat)
    (ht : 2 ≤ t) (hwidth : t + 3 ≤ n) :
    attemptCeiling n t ≤
      Prob.ceilNat (8 * n * n ^ (6 * n) * segmentPenalty t)
        (FreshCoupon.clearCountSix n t) := by
  unfold attemptCeiling
  exact ceiling_ratio_mono _ _ _ _
    (successLower_pos n t hwidth)
    (FreshCoupon.clearCountSix_pos n t hwidth)
    (attempt_ratio_bound n t ht hwidth)

/-- Only this optional comparison uses the separate coupon deficit.
The exact fixed-attempt cost theorem does not use it. -/
theorem attemptCeiling_le_fixedFactor (n t : Nat)
    (ht : 2 ≤ t) (hwidth : t + 3 ≤ n)
    (hzero : FreshCoupon.sixWindowDeficit n t = 0) :
    attemptCeiling n t ≤
      Prob.ceilNat (n * fixedFactorNumerator t) (fixedFactorDenominator t) := by
  have hclear :
      n ^ (6 * n) * 19 ^ (t + 3) ≤
        20 ^ (t + 3) * freshFact (t + 3) * FreshCoupon.clearCountSix n t := by
    unfold FreshCoupon.sixWindowDeficit at hzero
    omega
  have hnum :
      (8 * n * n ^ (6 * n) * segmentPenalty t) * fixedFactorDenominator t ≤
        (n * fixedFactorNumerator t) * FreshCoupon.clearCountSix n t := by
    unfold fixedFactorDenominator
    calc
      (8 * n * n ^ (6 * n) * segmentPenalty t) * 19 ^ (t + 3) =
          (8 * n * segmentPenalty t) * (n ^ (6 * n) * 19 ^ (t + 3)) := by
        ac_rfl
      _ ≤ (8 * n * segmentPenalty t) *
          (20 ^ (t + 3) * freshFact (t + 3) * FreshCoupon.clearCountSix n t) :=
        Nat.mul_le_mul_left _ hclear
      _ = (n * fixedFactorNumerator t) * FreshCoupon.clearCountSix n t := by
        unfold fixedFactorNumerator
        ac_rfl
  exact Nat.le_trans (attemptCeiling_le_discrete n t ht hwidth)
    (ceiling_ratio_mono _ _ _ _
      (FreshCoupon.clearCountSix_pos n t hwidth)
      (show 0 < fixedFactorDenominator t from Nat.pow_pos (by omega : 0 < 19))
      hnum)

end L3.FreshFixed

/-!
Deterministic fresh-trail genealogy for the fixed-length experiment.

The ghost only needs an occupied scanner with the correct *index*, plus
empty future scanner slots and a matching proof-only origin/hop tag.
This is intentionally weaker than SampledStage: no rootless or
static-sampled data assumption is required to preserve provenance.
-/

namespace L3.FreshFixed

open FreshReference
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- A successful canonical ordered word cannot ask for more distinct
labels than the scheduler alphabet has. This supplies the width
hypothesis omitted from the abstract FixedWordGenealogy signature. -/
theorem fresh_lastAccept_width {n : Nat}
    (k : Nat) (word : List (Fin n))
    (h : FreshCoupon.lastAccept k word = 1) : k ≤ n := by
  unfold FreshCoupon.lastAccept at h
  cases hw : word.reverse with
  | nil =>
      simp only [hw, FreshCoupon.orderedAccept] at h
      by_cases hk : k = 0
      · omega
      · simp [FreshCoupon.orderedAccept, hk] at h
  | cons e rest =>
      simp only [hw, FreshCoupon.orderedAccept] at h
      by_cases he : e.val + 1 = k
      · have hv := e.isLt
        omega
      · by_cases hk : k ≤ e.val
        · have hv := e.isLt
          omega
        · simp [FreshCoupon.orderedAccept, he, hk] at h

/-- The index/trail invariant; the physical token may contain arbitrary
data bits. Its index and the strictly later empty slots are enough for
the R0b transport and the eventual R0c provenance test. -/
def TaggedIndexStage {n q : Nat}
    (s : Fin n) (j : Fin (compileAdvice q).t)
    (z : FreshGhostConfig n q) : Prop :=
  (∃ r : RawTok (compileAdvice q).t,
      (z.1 (certSite s j.val)).rawTok = some r ∧
        r.j = j.val + 1) ∧
  (∀ k : Nat, j.val < k → k ≤ (compileAdvice q).t →
      (z.1 (certSite s k)).rawTok = none) ∧
  z.2.trail (certSite s j.val) =
    some { origin := s, hops := j.val }

/-- Equation for one proof-only trail update. It reduces the let-bound
ghost transition explicitly, so subsequent rewrites never target an
opaque step/freshTrailStep let body. -/
theorem fresh_ghost_trail_endpoint_eq {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n) (z : FreshGhostConfig n q)
    (e site : Fin n) :
    (freshGhostStep ring fixed s z e).2.trail site =
      (if site = e then none
       else if site = ring.rightNeighbor e then
         freshTargetTrail ring z.1 z.2 e
       else z.2.trail site) := by
  show (if site = e then none
        else if site = ring.rightNeighbor e then
          freshTargetTrail ring z.1 z.2 e
        else z.2.trail site) = _
  rfl

/-- The resident's old tag survives any incoming interaction, including
literal R0a: freshTargetTrail gives resident priority over an arrival.
Only selecting the resident as source may retire its tag. -/
theorem fresh_resident_tag_wait {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n) (z : FreshGhostConfig n q)
    (e site : Fin n) (r : RawTok (compileAdvice q).t)
    (hs : site ≠ e)
    (hr : (z.1 site).rawTok = some r) :
    (freshGhostStep ring fixed s z e).2.trail site =
      z.2.trail site := by
  rw [fresh_ghost_trail_endpoint_eq ring fixed s z e site, if_neg hs]
  by_cases hy : site = ring.rightNeighbor e
  · rw [if_pos hy]
    simp [freshTargetTrail, ← hy, hr]
  · rw [if_neg hy]

/-- Outside-B letters preserve physical index, future emptiness and
proof-only trail together. No incoming-token collision is excluded. -/
theorem tagged_stage_wait {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n) (j : Fin (compileAdvice q).t)
    (z : FreshGhostConfig n q) (e : Fin n)
    (hout : OutsideCoverage (q := q) s e)
    (hstage : TaggedIndexStage s j z) :
    TaggedIndexStage s j (freshGhostStep ring fixed s z e) := by
  obtain ⟨r, hr, hindex⟩ := hstage.1
  have hphysical :
      (freshGhostStep ring fixed s z e).1 =
        step ring fixed z.1 e :=
    freshGhost_projection ring fixed s z e
  refine ⟨⟨r, ?_, hindex⟩, ?_, ?_⟩
  · rw [hphysical]
    exact resident_of_no_outgoing ring fixed z.1 e
      (certSite s j.val) r (Ne.symm (hout j)) hr
  · intro k hjk hkt
    have hprelt : k - 1 < (compileAdvice q).t := by omega
    have hnext :
        ring.rightNeighbor (certSite s (k - 1)) =
          certSite s k := by
      have heq : k - 1 + 1 = k := by omega
      simpa only [heq] using
        ring_neighbor_certSite ring s (k - 1)
    have hno :
        certSite s k ≠ ring.rightNeighbor e := by
      intro heq
      have he : e = certSite s (k - 1) :=
        neighbor_injective ring e (certSite s (k - 1))
          (heq.symm.trans hnext.symm)
      exact hout ⟨k - 1, hprelt⟩ he
    rw [hphysical]
    exact empty_of_no_incoming ring fixed z.1 e
      (certSite s k) hno (hstage.2.1 k hjk hkt)
  · have hw := fresh_resident_tag_wait ring fixed s z e
      (certSite s j.val) r (Ne.symm (hout j)) hr
    rw [hw]
    exact hstage.2.2

/-- A monitored nonterminal B-edge forwards the actual scanner with
index j+2 and its origin=s tag with hops=j+1. The tag tests the OLD
index and source location; resident priority cannot intervene because
the required future target is physically empty. -/
theorem tagged_stage_advance {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n) (j : Fin (compileAdvice q).t)
    (hj : j.val + 1 < (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (z : FreshGhostConfig n q)
    (hstage : TaggedIndexStage s j z) :
    TaggedIndexStage s ⟨j.val + 1, hj⟩
      (freshGhostStep ring fixed s z (certSite s j.val)) := by
  let e := certSite s j.val
  let y := certSite s (j.val + 1)
  obtain ⟨r, hr, hindex⟩ := hstage.1
  have hsrc : (z.1 e).rawTok = some r := hr
  have hsrcTag : z.2.trail e =
      some { origin := s, hops := j.val } := hstage.2.2
  have hempty : (z.1 y).rawTok = none :=
    hstage.2.1 (j.val + 1) (by omega) (by omega)
  have hneighbor : ring.rightNeighbor e = y :=
    ring_neighbor_certSite ring s j.val
  have hdistinct : y ≠ e := by
    intro heq
    have hh := site_offset_injective s (j.val + 1) j.val
      (by omega) (by omega) heq
    omega
  have hsmall : r.j < (compileAdvice q).t := by
    rw [hindex]
    exact hj
  let rNext : RawTok (compileAdvice q).t :=
    { jm1 := ⟨r.j, hsmall⟩
      z := r.z || (z.1 y).u
      p := Bool.xor r.p ((compileAdvice q).taps r.j && (z.1 y).u)
      a := r.a && (z.1 y).u
      h := r.h || (postEInfo (z.1 e) (z.1 y)).eY.l
      m := if r.j + 1 == (compileAdvice q).t then
        (!(r.h || (postEInfo (z.1 e) (z.1 y)).eY.l) &&
          ((z.1 y).beta != (r.a && (z.1 y).u)))
        else false }
  have hrow : (rawResult ring z.1 e).row = "R0b" := by
    unfold rawResult
    rw [hneighbor]
    simp [rawD1Step, hsrc, hempty, hsmall]
  have hrawY : (rawResult ring z.1 e).tokY = some rNext := by
    unfold rawResult
    rw [hneighbor]
    simp [rawD1Step, hsrc, hempty, hsmall, rNext]
  have htargetRaw :
      (step ring fixed z.1 e y).rawTok = some rNext := by
    have hne : ring.rightNeighbor e ≠ e := by
      rw [hneighbor]
      exact hdistinct
    have hp := (target_raw ring fixed z.1 e hne).1
    change (step ring fixed z.1 e (ring.rightNeighbor e)).rawTok =
      (rawResult ring z.1 e).tokY at hp
    rw [hneighbor] at hp
    exact hp.trans hrawY
  have hnewIndex : rNext.j = (j.val + 1) + 1 := by
    change r.j + 1 = (j.val + 1) + 1
    rw [hindex]
  have htargetTrail :
      freshTargetTrail ring z.1 z.2 e =
        some { origin := s, hops := j.val + 1 } := by
    simp [freshTargetTrail, hneighbor, hempty, hrow,
      hsrcTag, hsrc, hindex]
    try rfl
  have hnewTag :
      (freshGhostStep ring fixed s z e).2.trail y =
        some { origin := s, hops := j.val + 1 } := by
    rw [fresh_ghost_trail_endpoint_eq ring fixed s z e y,
      if_neg hdistinct, if_pos hneighbor.symm]
    exact htargetTrail
  have hphysical :
      (freshGhostStep ring fixed s z e).1 =
        step ring fixed z.1 e :=
    freshGhost_projection ring fixed s z e
  refine ⟨⟨rNext, ?_, hnewIndex⟩, ?_, hnewTag⟩
  · rw [hphysical]
    exact htargetRaw
  · intro k hk hkt
    change j.val + 1 < k at hk
    have hkBound : k < n := by omega
    have hjBound : j.val + 1 < n := by omega
    have hno : certSite s k ≠ ring.rightNeighbor e := by
      rw [hneighbor]
      intro heq
      have hh := site_offset_injective s k (j.val + 1)
        hkBound hjBound heq
      omega
    have hold : j.val < k := by omega
    rw [hphysical]
    exact empty_of_no_incoming ring fixed z.1 e
      (certSite s k) hno (hstage.2.1 k hold hkt)

/-- The second guarded A-mark really runs R1c on the empty responder.
The produced index-one scanner at s is *newly tagged* at s even if
arbitrary ghost tags existed at the start of this attempt. -/
theorem tagged_second_launch {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n) (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (z : FreshGhostConfig n q)
    (hscratch : LaunchScratch z.1 s true) :
    TaggedIndexStage s ⟨0, by omega⟩
      (freshGhostStep ring fixed s z (certSite s (n - 1))) := by
  let e := certSite s (n - 1)
  have hneighbor : ring.rightNeighbor e = s :=
    launch_neighbor ring s (by omega)
  have hdistinct : s ≠ e := by
    have hne := Ne.symm (ring_neighbor_distinct ring (by omega) e)
    rw [hneighbor] at hne
    exact hne
  let rSeed : RawTok (compileAdvice q).t :=
    { jm1 := ⟨0, by omega⟩
      z := (z.1 s).u
      p := (compileAdvice q).taps 0 && (z.1 s).u
      a := (z.1 s).u
      h := (postEInfo (z.1 e) (z.1 s)).eY.l
      m := false }
  have hrow : (rawResult ring z.1 e).row = "R1c" := by
    unfold rawResult
    rw [hneighbor]
    exact launch_second_row z.1 s hscratch
  have hrawY : (rawResult ring z.1 e).tokY = some rSeed := by
    have hpos : 0 < (compileAdvice q).t := by omega
    have hsrc : (z.1 e).rawTok = none := hscratch.1.1
    have htgt : (z.1 s).rawTok = none := hscratch.2.1
    have hkick : (z.1 s).rawKick = true := hscratch.2.2.1
    unfold rawResult
    rw [hneighbor]
    simp [rawD1Step, hsrc, htgt, hkick, rSeed, hpos]
  have htargetRaw :
      (step ring fixed z.1 e s).rawTok = some rSeed := by
    have hne : ring.rightNeighbor e ≠ e := by
      rw [hneighbor]
      exact hdistinct
    have hp := (target_raw ring fixed z.1 e hne).1
    change (step ring fixed z.1 e (ring.rightNeighbor e)).rawTok =
      (rawResult ring z.1 e).tokY at hp
    rw [hneighbor] at hp
    exact hp.trans hrawY
  have hnewTag :
      (freshGhostStep ring fixed s z e).2.trail s =
        some { origin := s, hops := 0 } := by
    rw [fresh_ghost_trail_endpoint_eq ring fixed s z e s,
      if_neg hdistinct, if_pos hneighbor.symm]
    simp [freshTargetTrail, hneighbor, hscratch.2.1, hrow, hrawY]
  have hforward :
      ForwardClear (step ring fixed z.1 e) s :=
    launch_forward_clear ring fixed z.1 s hn hscratch.2.2.2
  have hphysical :
      (freshGhostStep ring fixed s z e).1 =
        step ring fixed z.1 e :=
    freshGhost_projection ring fixed s z e
  simp only [TaggedIndexStage, Fin.val_mk, certSite_zero]
  refine ⟨⟨rSeed, ?_, ?_⟩, ?_, hnewTag⟩
  · rw [hphysical]
    exact htargetRaw
  · change 0 + 1 = 0 + 1
    rfl
  · intro k hk hkt
    have hpos : k - 1 < (compileAdvice q).t := by omega
    have hindex : k - 1 + 1 = k := by omega
    have hslot := (hforward
      (⟨k - 1, hpos⟩ : Fin (compileAdvice q).t)).1
    rw [hphysical]
    simpa only [hindex] using hslot

/-- Assemble protected-slot clearing and the A-mark launch
with proof-only tags. No change to the physical scheduler or state. -/
theorem tagged_launch_sequence {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n) (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n)
    (z : FreshGhostConfig n q)
    (clear before between : List (Fin n))
    (hclear : FreshCoupon.lastAccept ((compileAdvice q).t + 3)
      (clear.map (protectedLabel s)) = 1)
    (hbefore : ∀ e, e ∈ before → ¬ LaunchEdge (q := q) s e)
    (hbetween : ∀ e, e ∈ between → ¬ LaunchEdge (q := q) s e) :
    TaggedIndexStage s ⟨0, by omega⟩
      (LDSinkBoundedKernel.run (freshGhostStep ring fixed s) z
        (clear ++ (before ++ [certSite s (n - 1)] ++
          between ++ [certSite s (n - 1)]))) := by
  let e := certSite s (n - 1)
  let zClear := LDSinkBoundedKernel.run
    (freshGhostStep ring fixed s) z clear
  let zBefore := LDSinkBoundedKernel.run
    (freshGhostStep ring fixed s) zClear before
  let zArmed := freshGhostStep ring fixed s zBefore e
  let zBetween := LDSinkBoundedKernel.run
    (freshGhostStep ring fixed s) zArmed between
  have hclearSlots :
      ∀ j : Fin ((compileAdvice q).t + 2),
        SlotClear zClear.1 (certSite s (n - 1 + j.val)) := by
    intro j
    change SlotClear
      (LDSinkBoundedKernel.run (freshGhostStep ring fixed s) z clear).1
      (certSite s (n - 1 + j.val))
    rw [fixedGhostRun_projection ring fixed s z clear]
    exact recognized_list_clears ring fixed z.1 s clear hn hclear j
  have hclearScratch : LaunchScratch zClear.1 s false :=
    launchScratch_of_protected_clear zClear.1 s hn hclearSlots
  have hbeforePhysical :
      zBefore.1 = runList ring fixed zClear.1 before :=
    fixedGhostRun_projection ring fixed s zClear before
  have hbeforeScratch : LaunchScratch zBefore.1 s false := by
    rw [hbeforePhysical]
    exact launch_outside_run ring fixed zClear.1 s false ht hn
      before hclearScratch hbefore
  have harmedPhysical :
      zArmed.1 = step ring fixed zBefore.1 e :=
    freshGhost_projection ring fixed s zBefore e
  have harmedScratch : LaunchScratch zArmed.1 s true := by
    rw [harmedPhysical]
    exact launch_arm ring fixed zBefore.1 s hn hbeforeScratch
  have hbetweenPhysical :
      zBetween.1 = runList ring fixed zArmed.1 between :=
    fixedGhostRun_projection ring fixed s zArmed between
  have hbetweenScratch : LaunchScratch zBetween.1 s true := by
    rw [hbetweenPhysical]
    exact launch_outside_run ring fixed zArmed.1 s true ht hn
      between harmedScratch hbetween
  have hlast := tagged_second_launch ring fixed s ht hn
    zBetween hbetweenScratch
  have hrun :
      LDSinkBoundedKernel.run (freshGhostStep ring fixed s) z
        (clear ++ (before ++ [e] ++ between ++ [e])) =
      freshGhostStep ring fixed s zBetween e := by
    simp only [List.append_assoc, fixedRun_append,
      LDSinkBoundedKernel.run, zClear, zBefore, zArmed, zBetween]
  rw [hrun]
  exact hlast

/-- Paired induction on the actual B-coverage word. It stops
*before* the last monitored service, at the fresh tag on the
physical terminal scanner. Every delay may include a collision. -/
theorem tagged_coverage_terminal {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n) (ht : 2 ≤ (compileAdvice q).t)
    (hn : (compileAdvice q).t + 3 ≤ n) :
    ∀ (j : Fin (compileAdvice q).t)
      (word : List (Fin n)),
      CoverageWord (q := q) s j word →
      ∀ (z : FreshGhostConfig n q),
        TaggedIndexStage s j z →
        ∃ before : List (Fin n),
          word = before ++ [certSite s ((compileAdvice q).t - 1)] ∧
          (LDSinkBoundedKernel.run (freshGhostStep ring fixed s)
            z before).2.trail
              (certSite s ((compileAdvice q).t - 1)) =
            some { origin := s, hops := (compileAdvice q).t - 1 } := by
  intro j word hword
  induction hword with
  | final j hlast =>
      intro z hstage
      have hj : j.val = (compileAdvice q).t - 1 := by omega
      refine ⟨[], ?_, ?_⟩
      · simpa only [List.nil_append, hj]
      · simpa only [LDSinkBoundedKernel.run, hj] using hstage.2.2
  | advance j hj word tail ih =>
      intro z hstage
      let e := certSite s j.val
      let zNext := freshGhostStep ring fixed s z e
      have hnext : TaggedIndexStage s ⟨j.val + 1, hj⟩ zNext :=
        tagged_stage_advance ring fixed s j hj hn z hstage
      obtain ⟨before, hword, htag⟩ := ih zNext hnext
      refine ⟨e :: before, ?_, ?_⟩
      · simpa only [List.cons_append] using
          congrArg (fun w => e :: w) hword
      · simpa only [LDSinkBoundedKernel.run] using htag
  | delay j e word outside tail ih =>
      intro z hstage
      let zNext := freshGhostStep ring fixed s z e
      have hnext : TaggedIndexStage s j zNext :=
        tagged_stage_wait ring fixed s j z e outside hstage
      obtain ⟨before, hword, htag⟩ := ih zNext hnext
      refine ⟨e :: before, ?_, ?_⟩
      · simpa only [List.cons_append] using
          congrArg (fun w => e :: w) hword
      · simpa only [LDSinkBoundedKernel.run] using htag

/-- The named genealogy premise is a theorem. The successful
clearing event itself supplies width <= n, and no rootless hypothesis
is needed by the raw-index/provenance part of the reference machine. -/
theorem fixedWordGenealogy_valid {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n)
    (s : Fin n) (ht : 2 ≤ (compileAdvice q).t) :
    FixedWordGenealogy ring fixed s ht := by
  intro z clear before between coverage hFrozen hclear
    hbefore hbetween hcoverage front hwhole
  have hn : (compileAdvice q).t + 3 ≤ n :=
    fresh_lastAccept_width ((compileAdvice q).t + 3)
      (clear.map (protectedLabel s)) hclear
  let e := certSite s (n - 1)
  let terminal := certSite s ((compileAdvice q).t - 1)
  let launchWord := before ++ [e] ++ between ++ [e]
  let zLaunch := LDSinkBoundedKernel.run
    (freshGhostStep ring fixed s) z (clear ++ launchWord)
  have hstage : TaggedIndexStage s ⟨0, by omega⟩ zLaunch := by
    dsimp only [zLaunch, launchWord, e]
    exact tagged_launch_sequence ring fixed s ht hn z clear
      before between hclear hbefore hbetween
  obtain ⟨tail, htail, htag⟩ :=
    tagged_coverage_terminal ring fixed s ht hn
      ⟨0, by omega⟩ coverage hcoverage zLaunch hstage
  have hgiven :
      ((clear ++ launchWord) ++ coverage) =
        front ++ [terminal] := hwhole
  have hnormal :
      ((clear ++ launchWord) ++ coverage) =
        ((clear ++ launchWord) ++ tail) ++ [terminal] := by
    dsimp only [terminal]
    rw [htail]
    simp only [List.append_assoc]
  have hfront : front = (clear ++ launchWord) ++ tail :=
    List.append_cancel_right (hgiven.symm.trans hnormal)
  have hrun :
      LDSinkBoundedKernel.run (freshGhostStep ring fixed s) z front =
        LDSinkBoundedKernel.run (freshGhostStep ring fixed s)
          zLaunch tail := by
    rw [hfront, fixedRun_append]
  rw [hrun]
  exact htag

/-- The paper's fixed-attempt first-hit bound with no phase-budget,
Bellman, FreshPhaseSound or FixedWordGenealogy hypothesis. The only
scientific input is the original frozen reference and bad-window
hypotheses. The exact ceiling and all n^T scheduler words are unchanged. -/
theorem freshGhost_cost_fixedAttempts_paper {n q : Nat}
    (ring : DirectedRing n)
    (fixed : (protocol q).Configuration n) (s : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hwidth : (compileAdvice q).t + 3 ≤ n)
    (hroot : ∀ i : Fin n, (fixed i).l = false)
    (hbad :
      ¬ NonzeroRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ RecurrenceRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s ∨
      ¬ MarkerRelation
        (certificateWordOfAgents (compileAdvice q) fixed) s)
    (z : FreshGhostConfig n q) (hz : Frozen fixed z.1) :
    ∀ T,
      costNumerator (freshGhostStep ring fixed s) freshGhostGood z T ≤
        n ^ T * attemptCeiling n (compileAdvice q).t := by
  exact freshGhost_cost_fixedAttempts ring fixed s ht hwidth hroot hbad
    (fixedWordGenealogy_valid ring fixed s ht) z hz

end L3.FreshFixed

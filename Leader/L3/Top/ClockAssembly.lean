import Leader.L3.RequestStage

/-!
Assembly interface for Lemma P.1 (fixed-public TOP packet clock).

The producer phases are separate propositions, NOT established by this file.
The phase-cut predicates are proof-only descriptions of reachable adapted cuts:
a future implementation must furnish their receipt, ancestry, barrier and
front-protection witnesses. No coordinate is added to the physical machine.

In particular B is an auxiliary port-acceptance clock used repeatedly WITHIN
F, not an additional serial charge. V and the first-two-edge race are local
trial subphases. Their bounds do not, by themselves, imply the geometric
2*C renewal bound; that remains an explicitly named phase obligation.
-/

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-! ## P.2--P.16, exact Nat budgets -/

/-- The compared complete-block width, definitionally 2^t - 1. -/
def topClockSpan (n : Nat) : Nat :=
  (compileAdvice (ceilLogTwo n)).rho

/-- P.2: arbitrary-private target port acceptance allowance. -/
def topClockB (r : Nat) : Nat := 3 * r ^ 2 + 4 * r + 2

/-- P.3: first post-entrance genuinely sampled source-border tail. -/
def topClockF (r : Nat) : Nat :=
  (2 * r ^ 2 + 1) * topClockB r + 8 * r ^ 3

/-- P.4--P.5: retirement of the moving obligations marked at T_F. -/
def topClockR (r : Nat) : Nat := 4 * r ^ 2 + 4 * r

/-- P.7--P.10: coloured settled-component elimination, including final
front/carry work at zero active component charge. -/
def topClockU (r : Nat) : Nat :=
  r ^ 2 * (2 * r ^ 2 + 8 * r + 1) + 5 * r

/-- P.12: a pending-only preparation and aligned favourable sweep. -/
def topClockV (r : Nat) : Nat := 2 * r ^ 2 + 5 * r + 3

/-- P.13: maximum conditional charge for one real trial, including its
race and its actual success or failure continuation. -/
def topClockC (r : Nat) : Nat :=
  topClockV r + 1 + topClockU r + r

/-! A small semiring certificate for P.16: rewrite monomial products
before asking omega to check only the integer coefficients. -/

private theorem topClockSquareTimesSquare (r : Nat) :
    r ^ 2 * r ^ 2 = r ^ 4 := by
  have h := Nat.pow_add r 2 2
  change r ^ 4 = r ^ 2 * r ^ 2 at h
  exact h.symm

private theorem topClockSquareTimesR (r : Nat) :
    r ^ 2 * r = r ^ 3 := by
  have h := Nat.pow_succ r 2
  change r ^ 3 = r ^ 2 * r at h
  exact h.symm

private theorem topClockFExpanded (r : Nat) :
    topClockF r =
      6 * r ^ 4 + 16 * r ^ 3 + 7 * r ^ 2 + 4 * r + 2 := by
  have hfour : (2 * r ^ 2) * (3 * r ^ 2) = 6 * r ^ 4 := by
    calc
      (2 * r ^ 2) * (3 * r ^ 2) =
          (2 * 3) * (r ^ 2 * r ^ 2) := by ac_rfl
      _ = 6 * r ^ 4 :=
        congrArg (fun z : Nat => 6 * z) (topClockSquareTimesSquare r)
  have hthree : (2 * r ^ 2) * (4 * r) = 8 * r ^ 3 := by
    calc
      (2 * r ^ 2) * (4 * r) =
          (2 * 4) * (r ^ 2 * r) := by ac_rfl
      _ = 8 * r ^ 3 :=
        congrArg (fun z : Nat => 8 * z) (topClockSquareTimesR r)
  have htwo : (2 * r ^ 2) * 2 = 4 * r ^ 2 := by
    calc
      (2 * r ^ 2) * 2 = (2 * 2) * r ^ 2 := by ac_rfl
      _ = 4 * r ^ 2 := by rfl
  unfold topClockF topClockB
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul,
    hfour, hthree, htwo]
  omega

private theorem topClockUExpanded (r : Nat) :
    topClockU r =
      2 * r ^ 4 + 8 * r ^ 3 + r ^ 2 + 5 * r := by
  have hfour : r ^ 2 * (2 * r ^ 2) = 2 * r ^ 4 := by
    calc
      r ^ 2 * (2 * r ^ 2) =
          2 * (r ^ 2 * r ^ 2) := by ac_rfl
      _ = 2 * r ^ 4 :=
        congrArg (fun z : Nat => 2 * z) (topClockSquareTimesSquare r)
  have hthree : r ^ 2 * (8 * r) = 8 * r ^ 3 := by
    calc
      r ^ 2 * (8 * r) = 8 * (r ^ 2 * r) := by ac_rfl
      _ = 8 * r ^ 3 :=
        congrArg (fun z : Nat => 8 * z) (topClockSquareTimesR r)
  unfold topClockU
  simp only [Nat.mul_add, Nat.mul_one, hfour, hthree]

/-- P.16. No rounding or population hypothesis occurs in this identity. -/
theorem topClockPolynomialSixteen (r : Nat) :
    topClockF r + topClockR r + topClockU r + r +
        2 * (topClockV r + 1 + topClockU r + r) =
      topCoefficientH r := by
  simp only [topClockFExpanded, topClockUExpanded,
    topClockR, topClockV, topCoefficientH, Nat.mul_add]
  omega

/-- P.16, written in the actual compiler width and with the factor n. -/
theorem topClockScaledSixteen (n : Nat) :
    n * topClockF (topClockSpan n) +
        n * topClockR (topClockSpan n) +
        n * topClockU (topClockSpan n) +
        n * topClockSpan n +
        n * (2 * topClockC (topClockSpan n)) =
      topCoefficientWidthH (compileAdvice (ceilLogTwo n)).t * n := by
  calc
    n * topClockF (topClockSpan n) +
        n * topClockR (topClockSpan n) +
        n * topClockU (topClockSpan n) +
        n * topClockSpan n +
        n * (2 * topClockC (topClockSpan n)) =
      n * (topClockF (topClockSpan n) +
        topClockR (topClockSpan n) +
        topClockU (topClockSpan n) +
        topClockSpan n + 2 * topClockC (topClockSpan n)) := by
          simp only [Nat.mul_add]
    _ = n * topCoefficientH (topClockSpan n) := by
      unfold topClockC
      rw [topClockPolynomialSixteen]
    _ = topCoefficientWidthH (compileAdvice (ceilLogTwo n)).t * n := by
      unfold topClockSpan topCoefficientWidthH Compiled.rho
      exact Nat.mul_comm _ _

/-! ## Generic exact first-hit sequential composition -/

/-- A path charged until P is bounded by the charge until Q followed
by a uniformly bounded P-charge at every Q-entry. This does not
require P or Q to be closed under the physical step. The recursion
itself stops at the first hit, so premature P hits cost zero. -/
private theorem topClockCostSequential
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (P Q : S → Prop) (b : Nat)
    (hafter : ∀ y : S, Q y →
      ∀ T : Nat, costNumerator next P y T ≤ n ^ T * b) :
    ∀ (T : Nat) (x : S),
      costNumerator next P x T ≤
        costNumerator next Q x T + n ^ T * b := by
  classical
  intro T
  induction T with
  | zero =>
      intro x
      simp only [costNumerator_zero, Nat.zero_add]
      exact Nat.zero_le _
  | succ T ih =>
      intro x
      by_cases hp : P x
      · rw [costNumerator_terminal next P x hp]
        exact Nat.zero_le _
      · by_cases hq : Q x
        · rw [costNumerator_terminal next Q x hq]
          simpa only [Nat.zero_add] using (hafter x hq (T + 1))
        · rw [costNumerator_succ next P x hp,
            costNumerator_succ next Q x hq]
          have hsum :=
            ofFn_sum_le
              (fun e : Fin n => costNumerator next P (next x e) T)
              (fun e : Fin n =>
                costNumerator next Q (next x e) T + n ^ T * b)
              (fun e => ih (next x e))
          have hsumBound :
              (List.ofFn
                (fun e : Fin n =>
                  costNumerator next P (next x e) T)).sum ≤
              (List.ofFn
                (fun e : Fin n =>
                  costNumerator next Q (next x e) T)).sum +
                n * (n ^ T * b) := by
            simpa only [ofFn_sum_add, ofFn_sum_const] using hsum
          calc
            n ^ (T + 1) +
              (List.ofFn (fun e : Fin n =>
                costNumerator next P (next x e) T)).sum ≤
              n ^ (T + 1) +
                ((List.ofFn (fun e : Fin n =>
                    costNumerator next Q (next x e) T)).sum +
                  n * (n ^ T * b)) :=
                Nat.add_le_add_left hsumBound _
            _ =
              (n ^ (T + 1) +
                (List.ofFn (fun e : Fin n =>
                  costNumerator next Q (next x e) T)).sum) +
                  n ^ (T + 1) * b := by
                rw [Nat.pow_succ]
                ac_rfl

/-- Exact strong-Markov-style serial composition at a first Q hit:
E[tau_P] <= a+b whenever E[tau_Q] <= a and every Q-cut
has residual P-cost <= b. No independence of the two clocks is used. -/
theorem topClockExpectedSequential
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (P Q : S → Prop)
    (hn : 0 < n) (x : S) (a b : Nat)
    (hfirst : UniformFirstHit.ExpectedHittingTimeAtMost
      next Q x (a : Rat))
    (hsecond : ∀ y : S, Q y →
      UniformFirstHit.ExpectedHittingTimeAtMost
        next P y (b : Rat)) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      next P x ((a + b : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    next P hn x (a + b)).2
  have hfirstCost :=
    (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      next Q hn x a).1 hfirst
  have hsecondCost : ∀ y : S, Q y →
      ∀ T : Nat, costNumerator next P y T ≤ n ^ T * b := by
    intro y hy
    exact (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      next P hn y b).1 (hsecond y hy)
  intro T
  calc
    costNumerator next P x T ≤
        costNumerator next Q x T + n ^ T * b :=
      topClockCostSequential next P Q b hsecondCost T x
    _ ≤ n ^ T * a + n ^ T * b :=
      Nat.add_le_add_right (hfirstCost T) _
    _ = n ^ T * (a + b) := (Nat.mul_add _ _ _).symm

/-! ## Cut meaning: actual frozen trace, receipts and physical slots -/

/-- Every phase cut is an actual state of one fixed-public scheduler word,
not an independently invented ghost trace. -/
def topClockReached {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) : Prop :=
  Z = topFixedTraceRun ring C Z.2

/-- The actual end-of-service source tail acceptance, requiring
a post-start recorded genuine sample, matching export receipt and
pending target-border input. The output's future purity is separate. -/
def topClockGenuineTailAccepted {n : Nat}
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) : Prop :=
  ∃ (sample : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (exported : DigitExport (compileAdvice (ceilLogTwo n)) n),
    DigitRecordedSample Z.1.2 sample ∧
    DigitRecordedExport Z.1.2 exported ∧
    sample.id.lane = .comparison ∧
    sample.id.site = certSite s 0 ∧
    0 < sample.id.time ∧
    sample.tail = true ∧
    exported.time = Z.1.2.clock ∧
    exported.lane = .comparison ∧
    exported.source = certSite s (topClockSpan n - 1) ∧
    exported.destination = certSite s (topClockSpan n) ∧
    exported.operand = some (.sampled sample.id) ∧
    exported.value = sample.value ∧
    exported.tail = true ∧
    (Z.1.1 (certSite s (topClockSpan n))).qIn =
      .P sample.value true

/-- Physical part of the cut T_{S=0}, prior to final mobile drain. -/
def topClockTargetSettledEmpty {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n) : Prop :=
  ∀ j : Fin (topClockSpan n),
    ((Z.1.1 (certSite s (topClockSpan n + j.val))).qIn.isS) =
      false

/-- Physical part of pi: all target inputs E/P and all carries OFF.
The pure-source serial-suffix genealogy is additionally required in
the pending-only cut class below; these slot tests alone are NOT pi. -/
def topClockTargetPendingOnly {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n) : Prop :=
  ∀ j : Fin (topClockSpan n),
    (((Z.1.1 (certSite s (topClockSpan n + j.val))).qIn.isE =
       true) ∨
      ((Z.1.1 (certSite s (topClockSpan n + j.val))).qIn.isP =
       true)) ∧
      (Z.1.1 (certSite s (topClockSpan n + j.val))).qCarry =
        .OFF

/-- A particular old output packet is physically present at the
source exit port. The atom may be inherited: P.2 allows arbitrary
initial private target scratch and does not presume fresh provenance. -/
def topClockPortReady {n : Nat}
    (s : Fin n) (atom : Option (DigitAtom n))
    (Z : TopFixedTraceState n) : Prop :=
  ∃ value : Fin (compileAdvice (ceilLogTwo n)).topA,
    ∃ tail : Bool,
      (Z.1.1 (certSite s (topClockSpan n - 1))).qOut =
        .D value tail ∧
      ((Z.1.2.current
        (certSite s (topClockSpan n - 1))).comparison.out.atom) =
          atom

/-- A receipt on the present cut records acceptance of the nominated
atom at the source-terminal-to-target-border physical edge. -/
def topClockPortAccepted {n : Nat}
    (s : Fin n) (atom : Option (DigitAtom n))
    (Z : TopFixedTraceState n) : Prop :=
  ∃ exported : DigitExport (compileAdvice (ceilLogTwo n)) n,
    DigitRecordedExport Z.1.2 exported ∧
    exported.time = Z.1.2.clock ∧
    exported.lane = .comparison ∧
    exported.source = certSite s (topClockSpan n - 1) ∧
    exported.destination = certSite s (topClockSpan n) ∧
    exported.operand = atom

/-- The same strict terminal is included in every intermediate target,
so an earlier strict hit ends the whole accounting immediately. -/
def topClockStopOr {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (P : TopFixedTraceState n → Prop) :
    TopFixedTraceState n → Prop :=
  fun Z => topFixedStrictStop ring C s Z ∨ P Z

/-- Proof-only phase classes, parameterized by the fixed public word.
All fields are predicates on the full TopFixedTraceState, including its
chronological history and audit frames; they are NOT extra machine state.

"coloured" includes (i)--(iv), and "pending" includes purity and
consecutive-suffix ancestry, not merely a shape test. The proof
obligations below prevent an implementation from silently using
arbitrary untyped post-eta scratch as a coloured restart state. -/
structure TopClockCutClasses {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) where
  pureCohorts : TopFixedTraceState n → Prop
  movingBarrier : TopFixedTraceState n → Prop
  generatedCarryGap : TopFixedTraceState n → Prop
  frontProtection : TopFixedTraceState n → Prop
  noTerminalReseed : TopFixedTraceState n → Prop
  consecutivePendingSuffix : TopFixedTraceState n → Prop
  firstTail : TopFixedTraceState n → Prop
  coloured : TopFixedTraceState n → Prop
  settledEmpty : TopFixedTraceState n → Prop
  pendingOnly : TopFixedTraceState n → Prop
  misplacedTail : TopFixedTraceState n → Prop
  favourable : TopFixedTraceState n → Prop
  unfavourable : TopFixedTraceState n → Prop
  firstTailSpec : ∀ Z, firstTail Z →
    topClockReached ring C Z ∧
    topClockGenuineTailAccepted C s Z ∧ pureCohorts Z
  colouredSpec : ∀ Z, coloured Z →
    topClockReached ring C Z ∧ pureCohorts Z ∧
    movingBarrier Z ∧ generatedCarryGap Z ∧
    frontProtection Z ∧ noTerminalReseed Z
  settledSpec : ∀ Z, settledEmpty Z →
    topClockReached ring C Z ∧
    pureCohorts Z ∧ topClockTargetSettledEmpty s Z
  pendingSpec : ∀ Z, pendingOnly Z →
    topClockReached ring C Z ∧ pureCohorts Z ∧
    consecutivePendingSuffix Z ∧ topClockTargetPendingOnly s Z
  misplacedSpec : ∀ Z, misplacedTail Z →
    topClockReached ring C Z ∧ pureCohorts Z ∧
    consecutivePendingSuffix Z
  favourableSpec : ∀ Z, favourable Z → topClockReached ring C Z
  unfavourableSpec : ∀ Z, unfavourable Z → coloured Z

/-! ## Named stochastic phase contracts: all use the SAME topFixedTraceNext -/

/-- P.2: any nominated ready output, from any reached legal target
scratch, is accepted (or strict completion occurs) within n*B. -/
def TopClockPortPhase {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) : Prop :=
  ∀ (atom : Option (DigitAtom n)) (Z : TopFixedTraceState n),
    topClockReached ring C Z →
    topClockPortReady s atom Z →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (topFixedTraceNext ring C)
      (topClockStopOr ring C s (topClockPortAccepted s atom))
      Z ((n * topClockB (topClockSpan n) : Nat) : Rat)

/-- P.3: arbitrary private initial scratch -> a true sampled-tail
acceptance and permanently pure future source stream, or strict stop. -/
def TopClockFreshTailPhase {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (cuts : TopClockCutClasses ring C s) : Prop :=
  UniformFirstHit.ExpectedHittingTimeAtMost
    (topFixedTraceNext ring C)
    (topClockStopOr ring C s cuts.firstTail)
    ((C, digitAuditInitial (piD C)), [])
    ((n * topClockF (topClockSpan n) : Nat) : Rat)

/-- P.4--P.5: first genuine tail -> all old marked moving input/front/
carry obligations retired, with four reached coloured invariants. -/
def TopClockMarkedDebtPhase {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (cuts : TopClockCutClasses ring C s) : Prop :=
  ∀ Z : TopFixedTraceState n,
    topClockStopOr ring C s cuts.firstTail Z →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (topFixedTraceNext ring C)
      (topClockStopOr ring C s cuts.coloured)
      Z ((n * topClockR (topClockSpan n) : Nat) : Rat)

/-- P.6--P.10: every reached coloured (i)--(iv) cut, with arbitrary
surviving inherited settled input, reaches no-settled at n*U.
The marked debris itself has already retired, but its settled residue
is not falsely assumed empty. -/
def TopClockSettledWorkPhase {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (cuts : TopClockCutClasses ring C s) : Prop :=
  ∀ Z : TopFixedTraceState n,
    topClockStopOr ring C s cuts.coloured Z →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (topFixedTraceNext ring C)
      (topClockStopOr ring C s cuts.settledEmpty)
      Z ((n * topClockU (topClockSpan n) : Nat) : Rat)

/-- Last part of P.11: after the first settled-empty cut, at most
r outward mobile services yield the genuinely pure pending-only cut. -/
def TopClockFinalMobilePhase {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (cuts : TopClockCutClasses ring C s) : Prop :=
  ∀ Z : TopFixedTraceState n,
    topClockStopOr ring C s cuts.settledEmpty Z →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (topFixedTraceNext ring C)
      (topClockStopOr ring C s cuts.pendingOnly)
      Z ((n * topClockSpan n : Nat) : Rat)

/-- P.12: preparation from every reached pure consecutive pending
suffix, either to strict completion or to a true misplaced-tail race
cut, under n*V. Physical gaps between pending packets are allowed. -/
def TopClockPreparationPhase {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (cuts : TopClockCutClasses ring C s) : Prop :=
  ∀ Z : TopFixedTraceState n,
    topClockStopOr ring C s cuts.pendingOnly Z →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (topFixedTraceNext ring C)
      (topClockStopOr ring C s cuts.misplacedTail)
      Z ((n * topClockV (topClockSpan n) : Nat) : Rat)

/-- The P.12 two-distinct-edge race has mean at most n. This alone
does NOT prove the required 1/2 favourable probability. -/
def TopClockRacePhase {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (cuts : TopClockCutClasses ring C s) : Prop :=
  ∀ Z : TopFixedTraceState n,
    topClockStopOr ring C s cuts.misplacedTail Z →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (topFixedTraceNext ring C)
      (fun Y => topFixedStrictStop ring C s Y ∨
        cuts.favourable Y ∨ cuts.unfavourable Y)
      Z ((n : Nat) : Rat)

/-- P.12--P.13 favourable branch: the outward front clears the old
suffix in at most r services, then aligned completion in V. -/
def TopClockFavourablePhase {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (cuts : TopClockCutClasses ring C s) : Prop :=
  ∀ Z : TopFixedTraceState n,
    topClockStopOr ring C s cuts.favourable Z →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (topFixedTraceNext ring C)
      (topFixedStrictStop ring C s)
      Z ((n * (topClockSpan n + topClockV (topClockSpan n)) : Nat) : Rat)

/-- P.13 unfavourable branch: from the ACTUAL losing successor,
not a fabricated reset state, U+r reaches another pending-only cut. -/
def TopClockUnfavourablePhase {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (cuts : TopClockCutClasses ring C s) : Prop :=
  ∀ Z : TopFixedTraceState n,
    topClockStopOr ring C s cuts.unfavourable Z →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (topFixedTraceNext ring C)
      (topClockStopOr ring C s cuts.pendingOnly)
      Z ((n * (topClockU (topClockSpan n) + topClockSpan n) : Nat) : Rat)

/-- P.13--P.14: the genuine history-conditioned renewal consumer.
It needs the separate two-edge first-hit 1/2 probability and a
payload-preserving conditional-mean bound C for each trial. Neither
claim follows from the above unconditional expected-time phase bounds
alone. Its 2*C coefficient is exact, with no deterministic trial cap. -/
def TopClockRenewalPhase {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (cuts : TopClockCutClasses ring C s) : Prop :=
  ∀ Z : TopFixedTraceState n,
    topClockStopOr ring C s cuts.pendingOnly Z →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (topFixedTraceNext ring C)
      (topFixedStrictStop ring C s)
      Z ((n * (2 * topClockC (topClockSpan n)) : Nat) : Rat)

/-- All P.1 phase producers at one fixed public pair.
The local B and V contracts are retained and must be proved, even
though their prices are already included in F and 2*C. -/
structure TopClockPhaseBundle {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) where
  cuts : TopClockCutClasses ring C s
  port : TopClockPortPhase ring C s
  fresh : TopClockFreshTailPhase ring C s cuts
  marked : TopClockMarkedDebtPhase ring C s cuts
  settled : TopClockSettledWorkPhase ring C s cuts
  mobile : TopClockFinalMobilePhase ring C s cuts
  prepare : TopClockPreparationPhase ring C s cuts
  race : TopClockRacePhase ring C s cuts
  favourable : TopClockFavourablePhase ring C s cuts
  unfavourable : TopClockUnfavourablePhase ring C s cuts
  renew : TopClockRenewalPhase ring C s cuts

/-- Exactly the remaining P.1 obligations at every eligible fixed
entrance C, hence at every legal Cartesian private scratch assignment.
The real entrance guards are the same as TopFixedClock. -/
def TopClockAllPhaseProps {n : Nat} (ring : DirectedRing n) : Prop :=
  5 ≤ n ∧
  ∀ (C : HeadlineConfiguration n) (s : Fin n),
    headlineGrantReady ring C →
    (∀ i : Fin n, (C i).l = false) →
    (∀ i : Fin n, (C i).req = false) →
    HeadlineDigit.BadCompletePair C s →
    Nonempty (TopClockPhaseBundle ring C s)

/-! ## P.15--P.16: sequential assembly and the actual target -/

/-- Main assembly. The four adapted handoffs are literally the same
cut predicates on both sides:
    start -> fresh -> coloured -> settled-empty -> pending-only -> strict.
The final pending-only -> strict bound is the geometric 2*C producer,
not two deterministic trials and not another F/R restart.
No phase assumes independence between successive scheduler edges. -/
theorem topFixedClock_of_phases {n : Nat}
    (ring : DirectedRing n)
    (hphases : TopClockAllPhaseProps ring) :
    TopFixedClock ring := by
  refine ⟨hphases.1, ?_⟩
  intro C s hg hl hr hbad
  obtain ⟨pkg⟩ := hphases.2 C s hg hl hr hbad
  have hfive : 5 ≤ n := hphases.1
  have hn : 0 < n := by omega
  have hFR :=
    topClockExpectedSequential
      (topFixedTraceNext ring C)
      (topClockStopOr ring C s pkg.cuts.coloured)
      (topClockStopOr ring C s pkg.cuts.firstTail)
      hn ((C, digitAuditInitial (piD C)), [])
      (n * topClockF (topClockSpan n))
      (n * topClockR (topClockSpan n))
      pkg.fresh pkg.marked
  have hFRU :=
    topClockExpectedSequential
      (topFixedTraceNext ring C)
      (topClockStopOr ring C s pkg.cuts.settledEmpty)
      (topClockStopOr ring C s pkg.cuts.coloured)
      hn ((C, digitAuditInitial (piD C)), [])
      (n * topClockF (topClockSpan n) +
        n * topClockR (topClockSpan n))
      (n * topClockU (topClockSpan n))
      hFR pkg.settled
  have hFRUM :=
    topClockExpectedSequential
      (topFixedTraceNext ring C)
      (topClockStopOr ring C s pkg.cuts.pendingOnly)
      (topClockStopOr ring C s pkg.cuts.settledEmpty)
      hn ((C, digitAuditInitial (piD C)), [])
      (n * topClockF (topClockSpan n) +
        n * topClockR (topClockSpan n) +
        n * topClockU (topClockSpan n))
      (n * topClockSpan n)
      hFRU pkg.mobile
  have hfull :=
    topClockExpectedSequential
      (topFixedTraceNext ring C)
      (topFixedStrictStop ring C s)
      (topClockStopOr ring C s pkg.cuts.pendingOnly)
      hn ((C, digitAuditInitial (piD C)), [])
      (n * topClockF (topClockSpan n) +
        n * topClockR (topClockSpan n) +
        n * topClockU (topClockSpan n) +
        n * topClockSpan n)
      (n * (2 * topClockC (topClockSpan n)))
      hFRUM pkg.renew
  rw [topClockScaledSixteen n] at hfull
  exact hfull

end L3

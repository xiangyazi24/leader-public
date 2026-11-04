import Leader.L3.Headline.Reduce
import Leader.L3.Purification
import Leader.L3.Grant.Drain
import Leader.L3.Bank.Counter
import Leader.L3.FreshScan
import Leader.L3.ProbRenewal
import Leader.L3.SealedPrep
import Leader.L3.SealedClose
import Leader.L3.CouponClear
import Leader.L3.TripleDeletion
import Leader.L3.SerClockCost
import Leader.L3.ClosureFull
import Leader.L3.NativeSector
import Leader.L3.CandidateClosure
import Leader.L3.EWord

/-!
The five still-open timing stages in the linear-lease
headline. This module does not modify Target, Headline, or
HeadlineAssembly. All stages use the actual physical IID Fin n
scheduler and the actual compiled Cartesian alphabet.

Paper source: research/paper/l3/appendices/renewal.tex,
Proof of thm:main (lines 1004-1194) reused by
thm:linear-lease (lines 1804-1823).
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-! ## Reusable target and zero-cost first-hit consequences -/

/-- An initial state already satisfying P has zero hitting cost.
    The bound B is arbitrary and nonnegative by its Nat type. -/
private theorem headlineStagesExpectedAtTarget
    {S : Type} {n : Nat} (next : S → Fin n → S)
    (P : S → Prop) (x : S) (hP : P x)
    (hn : 0 < n) (B : Nat) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      next P x (B : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    next P hn x B).2
  intro T
  cases T with
  | zero =>
    simp only [costNumerator_zero]
    exact Nat.zero_le _
  | succ T =>
    rw [costNumerator_terminal next P x hP (T + 1)]
    exact Nat.zero_le _

/-- Enlarging the terminal class cannot increase an expected
    hitting time. Uses the existing exact numerator comparison
    from ProbStages, not a separate stochastic approximation. -/
private theorem headlineStagesExpectedTargetMono
    {S : Type} {n : Nat} (next : S → Fin n → S)
    (P Q : S → Prop) (hPQ : ∀ x, P x → Q x)
    (hn : 0 < n) (x : S) (B : Nat)
    (h : UniformFirstHit.ExpectedHittingTimeAtMost
      next P x (B : Rat)) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      next Q x (B : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    next Q hn x B).2
  intro T
  exact Nat.le_trans
    (Prob.costNumerator_target_mono next P Q hPQ x T)
    ((UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      next P hn x B).1 h T)

/-!
STAGE P: Native purification (renewal.tex:1006-1014).

Exact coverage:
  Purification.purification_cost, purification_expected
      in Leader/L3/Purification.lean:858-909;
  real_step_preserves_P, Purification.lean:29-43;
  NativeBirth.native_step_eq, NativeBirth.lean:733-834;
  NativeBirth.birth_preserves_P, NativeBirth.lean:329-337.

The target of purification_expected is P on the real native
projection, while StageNativePurification uses
headlinePurified OR headlineGeneratedTarget. Since Protected
is definitionally PPlus, native P implies headlinePurified
even when no leader is present. This stage is proved below;
there is NO missing Stage P premise.
-/

/-- A real native-peaceful configuration is precisely the
    protected-or-leaderless purified class used by the paper. -/
theorem headlineStagesPurifiedOfPeaceful {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (h : P ring (nativeProjection C)) :
    headlinePurified ring C := by
  refine ⟨h, ?_⟩
  intro hleader
  change PPlus ring (nativeProjection C)
  refine ⟨?_, h⟩
  obtain ⟨i, hi⟩ := hleader
  refine ⟨i, ?_⟩
  change (C i).l = true
  exact hi

/-- Any purified state remains purified after one real edge,
    including a selected FIRE birth. -/
theorem headlineStagesPurifiedStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (h : headlinePurified ring C) :
    headlinePurified ring (headlinePhysicalNext ring C e) := by
  exact headlineStagesPurifiedOfPeaceful ring
    (headlinePhysicalNext ring C e)
    (real_step_preserves_P (by omega : 3 ≤ n)
      ring C e h.1)

/-- STAGE P IS DISCHARGED by the already proved
    real-protocol purification theorem and target monotonicity. -/
theorem stageNativePurification_proved {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) :
    StageNativePurification ring := by
  intro C
  apply headlineStagesExpectedTargetMono
    (headlinePhysicalNext ring)
    (fun D => P ring (nativeProjection D))
    (fun D => headlinePurified ring D ∨ headlineGeneratedTarget ring D)
    (fun D hp => Or.inl (headlineStagesPurifiedOfPeaceful ring D hp))
    (by omega : 0 < n)
    C (2 * n ^ 2)
  exact purification_expected hn ring C

/-!
STAGE B: First protected birth (renewal.tex:1015-1045).

Exact available contributions:
  NativeBirth.native_step_eq, NativeBirth.lean:733-834:
      the full real selected service is native E plus at most
      one eligible canonical birth;
  NativeBirth.lastLeader_not_deleted, NativeBirth.lean:839-863:
      a protected leader cannot be extinguished;
  NativeBirth.birth_preserves_P, NativeBirth.lean:329-337;
  Purification.real_step_preserves_P, Purification.lean:29-43.
  GrantDrain.grantDrainStep_preserves_PPlus,
      GrantDrain.lean:223-234, applies to a different stopped
      no-new-grant model; it is not a real first-birth clock.

The paper says that *both live OLD token types* have a physical
n^2 rendezvous clock, despite arbitrary scratch. The visible
source branch of headlineRequestReady assumes only existence of
one grant and one request on a peaceful ring. It does not encode
their no-loss transport lineage. The missing all-Cartesian
real-service theorem is named StageBirthTokenRendezvous below.
The other branch (an already protected leader) is zero-cost.
-/

/-- Exact missing first-birth producer, in the actual global
    Fin n scheduler and from arbitrary leaderless peaceful
    Cartesian scratch with at least one request and grant.
    Needed from NativeBirth / request-and-grant transport. -/
def StageBirthTokenRendezvous {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ C : HeadlineConfiguration n,
    headlinePurified ring C →
    (∀ i : Fin n, (C i).l = false) →
    (∃ i : Fin n, (C i).grant = true) →
    (∃ j : Fin n, (C j).req = true) →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring)
      (headlineRooted ring) C ((n ^ 2 : Nat) : Rat)

/-- A protected rooted state survives one physical service
    even if an unrelated canonical birth fires. -/
theorem headlineStagesRootedStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (h : headlineRooted ring C) :
    headlineRooted ring (headlinePhysicalNext ring C e) := by
  have hP : P ring (nativeProjection C) := h.1.2
  have hafter : P ring
      (nativeProjection (headlinePhysicalNext ring C e)) :=
    real_step_preserves_P (by omega : 3 ≤ n)
      ring C e hP
  have hleader : ∃ v : Fin n,
      (nativeProjection (headlinePhysicalNext ring C e) v).l =
        true :=
    lastLeader_not_deleted (by omega : 3 ≤ n)
      ring C e h.1
  refine ⟨⟨hleader, hafter⟩, ?_⟩
  obtain ⟨i, hi⟩ := hleader
  refine ⟨i, ?_⟩
  change
    (nativeProjection (headlinePhysicalNext ring C e) i).l =
      true
  exact hi

/-- If the earlier modules produce the precise missing token
    rendezvous clock, the full StageFirstProtectedBirth follows:
    the protected-leader case is already terminal and the
    leaderless case is the missing real-service producer. -/
theorem stageFirstProtectedBirth_of_rendezvous {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbirth : StageBirthTokenRendezvous ring) :
    StageFirstProtectedBirth ring := by
  intro C hready
  rcases hready with hprotected | htokens
  · obtain ⟨i, hi, hP⟩ := hprotected
    apply headlineStagesExpectedAtTarget
      (headlinePhysicalNext ring)
      (fun D => headlineRooted ring D ∨ headlineGeneratedTarget ring D)
      C (Or.inl ⟨hP, ⟨i, hi⟩⟩)
      (by omega : 0 < n) (n ^ 2)
  · obtain ⟨hpurified, hgrant, hrequest⟩ := htokens
    by_cases hleader : ∃ i : Fin n, (C i).l = true
    · apply headlineStagesExpectedAtTarget
        (headlinePhysicalNext ring)
        (fun D => headlineRooted ring D ∨ headlineGeneratedTarget ring D)
        C (Or.inl ⟨hpurified.2 hleader, hleader⟩)
        (by omega : 0 < n) (n ^ 2)
    · have hnone : ∀ i : Fin n, (C i).l = false := by
        intro i
        cases hi : (C i).l with
        | false =>
          rfl
        | true =>
          exact False.elim (hleader ⟨i, hi⟩)
      apply headlineStagesExpectedTargetMono
        (headlinePhysicalNext ring)
        (headlineRooted ring)
        (fun D => headlineRooted ring D ∨ headlineGeneratedTarget ring D)
        (fun D hd => Or.inl hd)
        (by omega : 0 < n) C (n ^ 2)
      exact hbirth C hpurified hnone hgrant hrequest

/-!
STAGE G: Leaderless first grant (renewal.tex:1019-1029,
F.9 at 405-420, F.36 at 1688-1698).

Green component evidence, not the requested full conclusion:
  Counter.resetClockBankStoppedExpected,
      Counter.lean:6615-6626, requires ResetLaunchPhysical
      and a BANK rather than actual first-grant target;
  CouponClear.protected_coupon_first_cover_cost_exact,
      CouponClear.lean:1015-1033, is an abstract mask clock;
  FreshFixed.freshGhost_cost_fixedAttempts_paper,
      FreshScan.lean:8674-8692, requires frozen reference
      state, rootlessness and a bad-recurrence witness.
  ProbRenewal.expectedHittingTimeAtMost_renewal_le,
      ProbRenewal.lean:506-523, needs a RetrySimulation.

No theorem above proves arbitrary leaderless first-GRANT
from a peaceful physical Cartesian cut without a grant. The
precise residual case is StageGrantLeaderlessClock below;
an already protected leader or existing grant costs zero.
-/

/-- Missing permit-clock producer. Its domain excludes only
    the two zero-time cases which StageFirstGrant already skips.
    The target is the actual grant-ready-or-generated event. -/
def StageGrantLeaderlessClock {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ C : HeadlineConfiguration n,
    headlinePurified ring C →
    (∀ i : Fin n, (C i).l = false) →
    (∀ i : Fin n, (C i).grant = false) →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring)
      (fun D => headlineGrantReady ring D ∨ headlineGeneratedTarget ring D)
      C ((headlinePermitRate n * n ^ 2 : Nat) : Rat)

/-- StageFirstGrant is exactly reduced to the missing
    leaderless-no-grant producer plus already-terminal cases. -/
theorem stageFirstGrant_of_leaderless_clock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hgrantClock : StageGrantLeaderlessClock ring) :
    StageFirstGrant ring := by
  intro C hpurified
  by_cases hleader : ∃ i : Fin n, (C i).l = true
  · have hprotected : Protected ring (nativeProjection C) :=
      hpurified.2 hleader
    obtain ⟨i, hi⟩ := hleader
    apply headlineStagesExpectedAtTarget
      (headlinePhysicalNext ring)
      (fun D => headlineGrantReady ring D ∨ headlineGeneratedTarget ring D)
      C (Or.inl (Or.inl ⟨i, hi, hprotected⟩))
      (by omega : 0 < n) (headlinePermitRate n * n ^ 2)
  · by_cases hgrant : ∃ i : Fin n, (C i).grant = true
    · apply headlineStagesExpectedAtTarget
        (headlinePhysicalNext ring)
        (fun D => headlineGrantReady ring D ∨ headlineGeneratedTarget ring D)
        C (Or.inl (Or.inr ⟨hpurified, hgrant⟩))
        (by omega : 0 < n) (headlinePermitRate n * n ^ 2)
    · have hnoLeader : ∀ i : Fin n, (C i).l = false := by
        intro i
        cases hi : (C i).l with
        | false =>
          rfl
        | true =>
          exact False.elim (hleader ⟨i, hi⟩)
      have hnoGrant : ∀ i : Fin n, (C i).grant = false := by
        intro i
        cases hi : (C i).grant with
        | false =>
          rfl
        | true =>
          exact False.elim (hgrant ⟨i, hi⟩)
      exact hgrantClock C hpurified hnoLeader hnoGrant

/-!
STAGE R: Request/checker clock (renewal.tex:1030-1032,
1040-1046, F.10 at 422-446).

Green component evidence, not the requested full conclusion:
  CouponClear.tolerant_scan_physical_stopping_cost,
      CouponClear.lean:2921, starts in a separate scanner
      stop process, not arbitrary physical grant-ready cuts;
  FreshFixed.freshGhost_cost_fixedAttempts_paper,
      FreshScan.lean:8674, bounds a frozen certificate
      attempt, not the old request bit;
  ClosureFull.targetSetClosed,
      ClosureFull.lean:127, is target closure after
      generation, not a first-REQUEST producer.

The StageRequestChecker target requires a simultaneous real
GRANT+REQ presence at its post-service cut. Showing request
production while all grant lineages vanish would be insufficient.
StageRequestMissingClock gives the precise all-Cartesian
remaining case; already-rooted or already-requested cuts have
zero hitting cost.
-/

/-- Missing request clock after the grant-ready cut, in the
    case of no physical leader and no existing OLD request. -/
def StageRequestMissingClock {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ C : HeadlineConfiguration n,
    headlineGrantReady ring C →
    (∀ i : Fin n, (C i).l = false) →
    (∀ i : Fin n, (C i).req = false) →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring)
      (fun D => headlineRequestReady ring D ∨
        headlineGeneratedTarget ring D)
      C (((headlineCheckerRate n + 1) * n ^ 2 : Nat) : Rat)

/-- Reduce the checker stage to the sole missing leaderless,
    no-request clock. A surviving grant must be paid in this
    clock because the target needs both token types together. -/
theorem stageRequestChecker_of_missing_clock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hrequestClock : StageRequestMissingClock ring) :
    StageRequestChecker ring := by
  intro C hgrantReady
  by_cases hleader : ∃ i : Fin n, (C i).l = true
  · have hprotected :
        ∃ i : Fin n,
          (C i).l = true ∧
            Protected ring (nativeProjection C) := by
      rcases hgrantReady with hp | htokens
      · exact hp
      · obtain ⟨hpurified, _⟩ := htokens
        have hprotected : Protected ring (nativeProjection C) :=
          hpurified.2 hleader
        obtain ⟨i, hi⟩ := hleader
        exact ⟨i, hi, hprotected⟩
    apply headlineStagesExpectedAtTarget
      (headlinePhysicalNext ring)
      (fun D => headlineRequestReady ring D ∨
        headlineGeneratedTarget ring D)
      C (Or.inl (Or.inl hprotected))
      (by omega : 0 < n)
      ((headlineCheckerRate n + 1) * n ^ 2)
  · by_cases hrequest : ∃ i : Fin n, (C i).req = true
    · have hready : headlineRequestReady ring C := by
        rcases hgrantReady with hp | htokens
        · exact Or.inl hp
        · exact Or.inr ⟨htokens.1, htokens.2, hrequest⟩
      apply headlineStagesExpectedAtTarget
        (headlinePhysicalNext ring)
        (fun D => headlineRequestReady ring D ∨
          headlineGeneratedTarget ring D)
        C (Or.inl hready)
        (by omega : 0 < n)
        ((headlineCheckerRate n + 1) * n ^ 2)
    · have hnoLeader : ∀ i : Fin n, (C i).l = false := by
        intro i
        cases hi : (C i).l with
        | false =>
          rfl
        | true =>
          exact False.elim (hleader ⟨i, hi⟩)
      have hnoRequest : ∀ i : Fin n, (C i).req = false := by
        intro i
        cases hi : (C i).req with
        | false =>
          rfl
        | true =>
          exact False.elim (hrequest ⟨i, hi⟩)
      exact hrequestClock C hgrantReady hnoLeader hnoRequest

/-!
STAGE N: Rooted renewal (renewal.tex:1058-1194,
F.1-F.4 at 195-302, F.34-F.39 at 1646-1794).

Green component evidence, not the requested full conclusion:
  TripleDeletion.tagged_q_expected_drift_bound,
      TripleDeletion.lean:3300-3317, applies to a
      controlled native singleton-contraction trial;
  SealedPrep.sealed_prep_expected,
      SealedPrep.lean:4617, needs its actual sealed start;
  FreshFixed.freshGhost_cost_fixedAttempts_paper,
      FreshScan.lean:8674, is a frozen-reference clock;
  SerClockCost.clockSerializerSOneExpectedFromG,
      SerClockCost.lean:273-289, needs a no-root-loss
      closure predicate and is an S1-only stopping clock;
  ProbRenewal.expectedHittingTimeAtMost_renewal_le,
      ProbRenewal.lean:506-523, requires a physical
      RetrySimulation, bounded attempt costs, and a
      bounded retry mass with strictly positive slack.

None of these statements by itself supplies the causal
reference-to-real fresh-origin renewal F.3 starting from
arbitrary protected Cartesian state. The exact remaining
finite-horizon certificate is StageRootedRenewalCost below.
-/

/-- Missing physical fresh-origin coupling and renewal,
    expressed exactly in the costNumerator API. The rate
    already includes all sigma_B/G/1/p reference subcuts. -/
def StageRootedRenewalCost {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ C : HeadlineConfiguration n,
    headlineRooted ring C →
    ∀ T : Nat,
      costNumerator (headlinePhysicalNext ring)
        (headlineGeneratedTarget ring) C T ≤
        n ^ T * (headlineRenewalRate n * n ^ 2)

/-- A finite-horizon F.3 certificate entails exactly
    StageRootedRenewal, including almost-sure entrance. -/
theorem stageRootedRenewal_of_cost {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hcost : StageRootedRenewalCost ring) :
    StageRootedRenewal ring := by
  intro C hroot
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (headlinePhysicalNext ring)
    (headlineGeneratedTarget ring)
    (by omega : 0 < n)
    C (headlineRenewalRate n * n ^ 2)).2
  exact hcost C hroot

/-!
STATUS AND EXACT OPEN PRODUCERS

PROVED ABOVE:
* StageNativePurification: stageNativePurification_proved.
* Native-P closure on all real edges:
  headlineStagesPurifiedStep (Purification.real_step_preserves_P).
* Rooted-P closure on all real edges:
  headlineStagesRootedStep
  (NativeBirth.lastLeader_not_deleted and
   Purification.real_step_preserves_P).
* All zero-duration inherited-leader / already-granted /
  already-requested subcases of the birth, grant and checker
  stages, by the finite-horizon cost terminal equation.

STILL OPEN (separate named propositions; NONE assumed true):
* StageBirthTokenRendezvous: NativeBirth and literal
  request/grant transport, renewal.tex:1032-1040.
* StageGrantLeaderlessClock: Counter / CouponClear /
  FreshScan plus physical first-grant comparison,
  renewal.tex:1019-1029.
* StageRequestMissingClock: DCC request producer and
  preservation of an OLD grant at the completion cut,
  renewal.tex:1030-1046.
* StageRootedRenewalCost: reference/real coupling,
  inherited-vs-fresh origin counting and RetrySimulation,
  ProbRenewal plus FreshScan / TripleDeletion / SealedPrep
  / SealedClose / EWord / GrantDrain,
  renewal.tex:1058-1194 and F.1-F.4.

The conditional reductions above are NOT claims that
the missing physical producers are already proved.
There is no new proof of an unconditional L3Headline.
-/

/-- `L3Headline` for `n ≥ 5` from the four remaining physical producers.
Purification is `stageNativePurification_proved`; closure and safety of the
generated target are `ClosureFull.targetSetClosed` / `targetSetIsSafe`
(through `l3Headline_of_time_stages`). -/
theorem l3Headline_of_producers {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbirth : StageBirthTokenRendezvous ring)
    (hgrantClock : StageGrantLeaderlessClock ring)
    (hrequestClock : StageRequestMissingClock ring)
    (hcost : StageRootedRenewalCost ring) :
    L3Headline ring :=
  l3Headline_of_time_stages ring hn
    (stageNativePurification_proved ring hn)
    (stageFirstGrant_of_leaderless_clock ring hn hgrantClock)
    (stageRequestChecker_of_missing_clock ring hn hrequestClock)
    (stageFirstProtectedBirth_of_rendezvous ring hn hbirth)
    (stageRootedRenewal_of_cost ring hn hcost)

end L3

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
The literal OLD-request/OLD-grant rendezvous rows.

renewal.tex:1032-1040 is the proposed n^2 first protected
birth clock. The original HeadlineStages prefix has already
proved StageFirstProtectedBirth from StageBirthTokenRendezvous.

Exact row order in Base.lean:322-331,358-437:
- FIRE F0: source OLD request plus source OLD grant;
- FIRE F1: responder OLD request plus responder OLD grant;
- FIRE F2: source OLD request plus responder OLD grant;
- T0: only a selected FIRE consumes OLD tokens;
- T1: final native leaders sink tokens;
- T2: DCC produces a responder request; BANK/SMALL produces
  a source grant, neither of which removes an OLD token;
- HOLD: coincident nonfiring OLD pairs do not separate;
- REQ: source x to responder y (clockwise);
- GRANT: responder y to source x (counterclockwise).

The post-E source is an empty native follower when both
endpoints are leaderless, independently of old bullet bytes.
Consequently F0 and F2 cannot be blocked by an old source
bullet. The no-FIRE/no-leader token-row conservation below
is LOCAL: transporting it through the actual full pair
transition and proving all-edge minimum-gap monotonicity
remain the first unproved global obligations.

No claim that StageBirthTokenRendezvous is proved is made.
-/

/-- Literal native E on a leaderless pair: no leader is
    created by E, and its source has no bullet. -/
theorem headlineRendezvousLeaderlessPostE
    (x y : CertNative)
    (hx : x.l = false) (hy : y.l = false) :
    (certLiteralEPair x y).1.l = false ∧
    (certLiteralEPair x y).2.l = false ∧
    (certLiteralEPair x y).1.b = (0 : Fin 3) := by
  by_cases hb : 0 < x.b.val
  · simp [certLiteralEPair, hx, hy, hb, certFinThree]
  · have hz : x.b.val = 0 := by omega
    simp [certLiteralEPair, hx, hy, hz, certFinThree]

/-- F0: a co-located OLD request/grant at a leaderless
    source necessarily selects FIRE. No initial bullet
    shape or certificate field is restricted. -/
theorem headlineRendezvousCoincidentFires {c : Compiled}
    (x y : Agent c)
    (hx : x.l = false) (hy : y.l = false)
    (hreq : x.req = true) (hgrant : x.grant = true) :
    oldFire x y ≠ none := by
  have hpost := headlineRendezvousLeaderlessPostE
    x.certNative y.certNative
    (by simpa only [Agent.certNative] using hx)
    (by simpa only [Agent.certNative] using hy)
  simp [oldFire, fireSelect, hreq, hgrant,
    hpost.1, hpost.2.1, hpost.2.2]

/-- F0/F1/F2: an OLD request at the source and an OLD
    grant at its clockwise responder select FIRE, even
    when the responder has a bullet or a second request. -/
theorem headlineRendezvousCrossFires {c : Compiled}
    (x y : Agent c)
    (hx : x.l = false) (hy : y.l = false)
    (hreq : x.req = true) (hgrant : y.grant = true) :
    oldFire x y ≠ none := by
  have hpost := headlineRendezvousLeaderlessPostE
    x.certNative y.certNative
    (by simpa only [Agent.certNative] using hx)
    (by simpa only [Agent.certNative] using hy)
  cases hgrantX : x.grant <;>
    cases hrequestY : y.req <;>
    by_cases hreadyY :
      (certLiteralEPair x.certNative y.certNative).2.b.val = 0 <;>
    simp [oldFire, fireSelect, hreq, hgrant, hgrantX,
      hrequestY, hreadyY, hpost.1, hpost.2.1,
      hpost.2.2]

/-- Literal T0-T2/HOLD/REQ/GRANT row fact. Under no FIRE
    and no final leader at either endpoint, each nonempty
    OLD token kind remains nonempty across the pair:
    requests may coalesce but travel x->y; grants may
    coalesce but travel y->x. DCC/BANK production cannot
    invalidate either implication. The result is about
    tokenStep, not yet a theorem about protocol.step. -/
theorem headlineRendezvousLocalNoFireRetainsTokens
    {c : Compiled}
    (x y : Agent c) (finalX finalY : CertNative)
    (dccRequest bankSuccessX : Bool)
    (hX : finalX.l = false) (hY : finalY.l = false) :
    ((x.req = true ∨ y.req = true) →
      (tokenStep x y finalX finalY none
        dccRequest bankSuccessX).1.req = true ∨
      (tokenStep x y finalX finalY none
        dccRequest bankSuccessX).2.1.req = true) ∧
    ((x.grant = true ∨ y.grant = true) →
      (tokenStep x y finalX finalY none
        dccRequest bankSuccessX).1.grant = true ∨
      (tokenStep x y finalX finalY none
        dccRequest bankSuccessX).2.1.grant = true) := by
  cases hreqX : x.req <;>
    cases hgrantX : x.grant <;>
    cases hreqY : y.req <;>
    cases hgrantY : y.grant <;>
    cases dccRequest <;>
    cases bankSuccessX <;>
    simp [tokenStep, hX, hY, hreqX, hgrantX,
      hreqY, hgrantY] <;>
    (repeat' split) <;> simp


/-- Native E itself never creates a leader from a leaderless
    physical native cut. This is the T1 sink exclusion before
    any FIRE service: both post-E leader bits are false. -/
theorem headlineRendezvousNativeERootless {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (e : Fin n) (hrootless : ∀ i : Fin n, (N i).l = false) :
    ∀ i : Fin n, (nativeE ring N e i).l = false := by
  have hpost := headlineRendezvousLeaderlessPostE
    (N e) (N (ring.rightNeighbor e))
    (hrootless e) (hrootless (ring.rightNeighbor e))
  intro i
  by_cases he : i = e
  · subst i
    simpa [nativeE] using hpost.1
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simpa [nativeE, he] using hpost.2.1
    · simpa [nativeE, he, hj] using hrootless i

/-- An actual no-FIRE physical service cannot introduce a
    native leader from a leaderless cut. The native projection
    commutation is Closure.nativeProjectionBirthFree. -/
theorem headlineRendezvousNoFireRemainsRootless {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (e : Fin n) (hn : 2 ≤ n)
    (hrootless : ∀ i : Fin n, (C i).l = false)
    (hfire : oldFire (C e)
      (C (ring.rightNeighbor e)) = none) :
    ∀ i : Fin n,
      ((headlinePhysicalNext ring C e) i).l = false := by
  have hproj := Closure.nativeProjectionBirthFree
    (q := ceilLogTwo n) hn ring C e hfire
  have hNative : ∀ i : Fin n,
      (nativeProjection C i).l = false := by
    intro i
    exact hrootless i
  have hE := headlineRendezvousNativeERootless
    ring (nativeProjection C) e hNative
  intro i
  have h2 := hE i
  rw [← hproj] at h2
  exact h2

/-- Proof-observer distance, in directed clockwise coordinates.
    When both token types exist, choose the least clockwise
    request-to-grant gap across all OLD pairs. When a type
    is absent, use n as an explicit sentinel; the missing
    physical no-loss invariant must exclude that sentinel
    on every pre-birth reachable cut. -/
def headlineRendezvousMinGap {n : Nat}
    (C : HeadlineConfiguration n) : Nat :=
  (List.finRange n).foldl (fun acc r =>
    (List.finRange n).foldl (fun acc' g =>
      if (C r).req = true ∧ (C g).grant = true then
        min acc' ((g.val + n - r.val) % n)
      else acc') acc) n

/-- Candidate physical rank: zero at a protected birth,
    otherwise 1 plus the least clockwise gap, capped at n.
    The extra unit is the final F0/F2 service.
    Strict and weak one-edge inequalities for this rank
    are NOT asserted without a full real-step row proof. -/
noncomputable def headlineRendezvousRank {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) : Nat := by
  classical
  exact if headlineRooted ring C then 0
    else min n (headlineRendezvousMinGap C + 1)

/-- The rank has the required n-ticket cap
    independently of arbitrary private certificate fields. -/
theorem headlineRendezvousRankCap {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) :
    headlineRendezvousRank ring C ≤ n := by
  classical
  unfold headlineRendezvousRank
  split
  · exact Nat.zero_le _
  · exact Nat.min_le_left _ _

/-!
FIRST UNFINISHED ITEM: full-real-step token survival and
minimum-gap drift, renewal.tex:1032-1040.

The local tokenStep no-FIRE/no-leader row is separated
above from the actual protocol.step; the native rootless
condition on a real no-FIRE edge is proved, but the
full token coordinate transport still remains open, whose DCC and BANK
owners produce new tokens, whose E owner moves bullets,
and whose FIRE selector reads OLD tokens and POST-E
native eligibility. To complete StageBirthTokenRendezvous:
(1) lift the no-FIRE/no-leader token-row conservation
    into all-site OLD request/grant witnesses of the
    actual full protocol step until first rooted birth;
(2) establish that every genuine F0/F1/F2 birth reached
    from a peaceful leaderless cut is headlineRooted,
    using real_step_preserves_P, native_step_eq and
    canonicalBirth_has_leader / birth_preserves_P;
(3) prove that the least directed request->grant gap
    never increases under a non-birth real service,
    and that a nominated request-outgoing service
    strictly decreases headlineRendezvousRank;
(4) apply Prob.costNumerator_le_of_nominated_edge
    with n tickets, then
    UniformFirstHit.expectedHittingTimeAtMost_iff_cost.

The pure T1 leader sink is NOT an example of premature
loss in this leaderless scope: reaching a final leader
already ends this stage. No rootless no-FIRE token-loss
row has been established, and no counterexample to the
n^2 producer is claimed.
-/

end L3


/-!
Bounded-density grant entrance only.
No theorem below claims the full first-grant stage.

First the already-proved real-role density clock is transferred
to the actual headline scheduler and its larger early-stop target.
The first unproved next interface is then recorded as a Prop,
not an axiom or assumed theorem.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- The 192 n^2 role-defect entrance is already a theorem for
the REAL physical step. No reference or BANK-only chain is used. -/
theorem headlineStagesGrantDefectDensityCost {n : Nat}
    (ring : DirectedRing n) (hn : 16 ≤ n)
    (C : HeadlineConfiguration n) (T : Nat) :
    costNumerator (headlinePhysicalNext ring)
      (fun D : HeadlineConfiguration n =>
        defects ring D * defects ring D ≤ 4 * n) C T ≤
      n ^ T * (192 * n ^ 2) := by
  exact density_cost hn ring C T

/-- At the same actual cut, stop earlier for a physical grant-ready
state or generated target. This keeps all inherited scratch and
does not condition on the absence of either earlier event. -/
theorem headlineStagesGrantDensityEntrance {n : Nat}
    (ring : DirectedRing n) (hn : 16 ≤ n)
    (C : HeadlineConfiguration n) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring)
      (fun D : HeadlineConfiguration n =>
        (defects ring D * defects ring D ≤ 4 * n) ∨
        headlineGrantReady ring D ∨
        headlineGeneratedTarget ring D)
      C ((192 * n ^ 2 : Nat) : Rat) := by
  apply headlineStagesExpectedTargetMono
    (headlinePhysicalNext ring)
    (fun D : HeadlineConfiguration n =>
      defects ring D * defects ring D ≤ 4 * n)
    (fun D : HeadlineConfiguration n =>
      (defects ring D * defects ring D ≤ 4 * n) ∨
      headlineGrantReady ring D ∨
      headlineGeneratedTarget ring D)
    (fun _ hd => Or.inl hd)
    (by omega : 0 < n) C (192 * n ^ 2)
  exact density_expected hn ring C

/-- Physical full-support goodness and the clockwise rear buffer.
The bad-edge condition is evaluated at the ACTUAL completed cut.
A good complete interval alone does not assert that a future
defect cannot enter during its local counter attempt. -/
def HeadlineGrantBufferedCounter {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (radius : Nat) (root : Fin n) : Prop :=
  Counter.Complete ring C root ∧
  (∀ e : Fin n,
    Counter.Support (ceilLogTwo n) ring root e →
      badRoleEdge (compileAdvice (ceilLogTwo n)).b ring
        (fun i : Fin n => (C i).pack) e = 0) ∧
  (∀ e : Fin n,
    badRoleEdge (compileAdvice (ceilLogTwo n)).b ring
      (fun i : Fin n => (C i).pack) e = 1 →
    ∀ d : Nat, 1 ≤ d → d ≤ 2 * radius →
      Counter.site ring e d ≠ root)

/-- FIRST UNSOLVED BRIDGE, not a hypothesis used by any theorem.
This is the C.9-C.10 deterministic spatial-selection obligation:
after the density stop, select enough ACTUAL complete
full-support-good roots with a two-radius rear buffer and pairwise
disjoint inclusive counter supports.

The squared inequalities specify radius = floor(sqrt(n)/256)
without importing an integer-square-root API. The first size
inequality is the paper's sqrt(n) >= 4096*(b+2).
The last inequality is the strict 489/1000 density of selected
supports in C.10. It is deliberately quantified over arbitrary
PACK words and makes no favorable future-scheduler assumption.

The proposition is only NAMED. Its proof, followed by cold RESET
entry C.3, defect-censored local renewal C.2, successful trial C.6,
and all-support first-grant composition, remains to be supplied.
-/
def StageGrantSpatialSupportBridge {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ (C : HeadlineConfiguration n) (radius : Nat),
    (4096 * ((compileAdvice (ceilLogTwo n)).b + 2)) ^ 2 ≤ n →
    (256 * radius) ^ 2 ≤ n →
    n < (256 * (radius + 1)) ^ 2 →
    defects ring C * defects ring C ≤ 4 * n →
    ∃ roots : List (Fin n),
      roots.Nodup ∧
      (∀ root : Fin n, root ∈ roots →
        HeadlineGrantBufferedCounter ring C radius root) ∧
      (∀ root other : Fin n,
        root ∈ roots → other ∈ roots → root ≠ other →
        ∀ e : Fin n,
          ¬ (Counter.Support (ceilLogTwo n) ring root e ∧
             Counter.Support (ceilLogTwo n) ring other e)) ∧
      489 * n <
        1000 * roots.length *
          ((compileAdvice (ceilLogTwo n)).b + 2)

end L3

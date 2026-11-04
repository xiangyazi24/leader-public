import Leader.L3.Bank.TrialCompare

/-!
C.6--C.8 local BANK trial-duration route audit.

The original alphabet is Fin n (all physical scheduler edges).
A trial stops at the first WON or LOST observer state. LOST
includes the following authenticated zero reset; RECOVERY is
not a terminal outcome.

The three budget Props below are deliberately NOT theorems.
Their source obligations are spatial-counter.tex, C.6,
lines 358--368. The third requires transferring C.2 from the
authenticated reset-renewal carrier to reachable local RECOVERY.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Stage 0: an armed decision race; stage 1: live worker
and comparator traffic; stage 2: reset recovery.
A terminal state is not charged, irrespective of its tag. -/
def bankTrialDurationClass {q : Nat}
    (z : BankTrialLocalState q) : Nat :=
  match z.phase with
  | .live _ =>
      if (z.bank.fields ⟨0, by omega⟩).1 = .ARMED then 0 else 1
  | .recovery => 2
  | .won => 2
  | .lost => 2

private theorem bankTrialDurationClassLe {q : Nat}
    (z : BankTrialLocalState q) :
    bankTrialDurationClass z ≤ 2 := by
  cases z with
  | mk bank phase =>
      cases phase with
      | live begun =>
          change (if (bank.fields ⟨0, by omega⟩).1 = .ARMED
            then 0 else 1) ≤ 2
          split <;> omega
      | recovery => exact Nat.le_refl 2
      | won => exact Nat.le_refl 2
      | lost => exact Nat.le_refl 2

private theorem bankTrialDurationClassOne {q : Nat}
    (z : BankTrialLocalState q) :
    (if bankTrialDurationClass z = 0 then 1 else 0) +
      ((if bankTrialDurationClass z = 1 then 1 else 0) +
       (if bankTrialDurationClass z = 2 then 1 else 0)) = 1 := by
  have hle := bankTrialDurationClassLe z
  by_cases hz : bankTrialDurationClass z = 0
  · simp [hz]
  · by_cases ho : bankTrialDurationClass z = 1
    · have ht : bankTrialDurationClass z ≠ 2 := by omega
      simp [hz, ho, ht]
    · have ht : bankTrialDurationClass z = 2 := by omega
      simp [hz, ho, ht]

/-- Number of preterminal letters with this OLD observer class,
on a single ORIGINAL scheduler word. No extra worker clock. -/
noncomputable def bankTrialDurationStageWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (tag : Nat) :
    BankTrialLocalState q → List (Fin n) → Nat
  | _, [] => 0
  | z, e :: tail =>
      if bankTrialLocalTerminal z then 0
      else (if bankTrialDurationClass z = tag then 1 else 0) +
        bankTrialDurationStageWord ring root tag
          (bankTrialLocalNext ring root z e) tail

/-- Every preterminal original-clock letter belongs to exactly
one of the three classes; the equality includes unfinished words. -/
theorem bankTrialDurationWordPartition {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q) (w : List (Fin n)) :
    costWord (bankTrialLocalNext ring root)
        bankTrialLocalTerminal z w =
      bankTrialDurationStageWord ring root 0 z w +
        (bankTrialDurationStageWord ring root 1 z w +
         bankTrialDurationStageWord ring root 2 z w) := by
  classical
  induction w generalizing z with
  | nil => rfl
  | cons e tail ih =>
      by_cases ht : bankTrialLocalTerminal z
      · simp [costWord, K2FiniteSafeEliminationExpected.rawCost,
          bankTrialDurationStageWord, ht]
      · have hc :
          costWord (bankTrialLocalNext ring root)
              bankTrialLocalTerminal z (e :: tail) =
            1 + costWord (bankTrialLocalNext ring root)
              bankTrialLocalTerminal
              (bankTrialLocalNext ring root z e) tail := by
            simp only [costWord, K2FiniteSafeEliminationExpected.rawCost,
              if_neg ht]
        rw [hc]
        simp only [bankTrialDurationStageWord, if_neg ht]
        rw [ih (bankTrialLocalNext ring root z e)]
        have hw := bankTrialDurationClassOne z
        omega

/-- Exact unnormalized expected charge on all n^T words. -/
noncomputable def bankTrialDurationStageMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (tag : Nat)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) : Nat :=
  Prob.scheduleSum n T
    (bankTrialDurationStageWord ring root tag
      (bankTrialLocalStart S))

private theorem bankTrialDurationSumAdd (n T : Nat)
    (f g : List (Fin n) → Nat) :
    Prob.scheduleSum n T (fun w => f w + g w) =
      Prob.scheduleSum n T f + Prob.scheduleSum n T g := by
  change FixedSpanRenewalPayload.wordSum n T (fun w => f w + g w) =
    FixedSpanRenewalPayload.wordSum n T f +
      FixedSpanRenewalPayload.wordSum n T g
  rw [← FixedSpanRenewalPayload.rawWord_sum n T
        (fun w => f w + g w),
      ← FixedSpanRenewalPayload.rawWord_sum n T f,
      ← FixedSpanRenewalPayload.rawWord_sum n T g,
      ofFn_sum_add]

/-- MISSING, paper C.6 lines 358--363: all ARMED decision-race
epochs together cost at most n (the geometric-head argument).
Fairness of a single pair of ports alone does not prove this
finite-horizon stopped charge inequality. -/
def BankTrialDurationRaceBudget {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    BankTrialLocalClean q S →
    ∀ T : Nat,
      bankTrialDurationStageMass ring root 0 S T ≤ n ^ T * n

/-- MISSING, paper C.6 lines 363--365: expected combined
increment/comparison cost, including aborted workers, is
(2L+1)n, L=2b+2. This is the complete live-worker charge
over all geometric heads, not a single worker excursion. -/
def BankTrialDurationWorkerBudget {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    BankTrialLocalClean q S →
    ∀ T : Nat,
      bankTrialDurationStageMass ring root 1 S T ≤
        n ^ T * ((2 * (2 * (compileAdvice q).b + 2) + 1) * n)

/-- MISSING TRANSFER, paper C.2 lines 235--243 and
C.6 lines 365--367: recovery from the actual reachable
authenticated local cut has cost (2L+2)n.
The Counter.resetClockBankResetRenewalCost works on
ResetClockBankRenewalState, NOT on BankTrialLocalState.
The proposed bound is for all local words from CLEAN seeds
and therefore does not quantify over forged reset scratch. -/
def BankTrialDurationRecoveryBudget {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    BankTrialLocalClean q S →
    ∀ T : Nat,
      bankTrialDurationStageMass ring root 2 S T ≤
        n ^ T * ((2 * (2 * (compileAdvice q).b + 2) + 2) * n)

/-- C.6 on the exact BankTrialLocalState first-hit clock,
conditionally derived from three SEPARATELY named missing costs.
The proof uses one n-edge tape and no outcome/duration independence. -/
theorem bankTrialDurationC6OfBudgets {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hrace : BankTrialDurationRaceBudget (q := q) ring root)
    (hworker : BankTrialDurationWorkerBudget (q := q) ring root)
    (hreset : BankTrialDurationRecoveryBudget (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) (T : Nat) :
    costNumerator (bankTrialLocalNext ring root)
      bankTrialLocalTerminal (bankTrialLocalStart S) T ≤
        n ^ T * ((8 * (compileAdvice q).b + 12) * n) := by
  have hsum :
      costNumerator (bankTrialLocalNext ring root)
          bankTrialLocalTerminal (bankTrialLocalStart S) T =
        bankTrialDurationStageMass ring root 0 S T +
          (bankTrialDurationStageMass ring root 1 S T +
           bankTrialDurationStageMass ring root 2 S T) := by
    change Prob.scheduleSum n T
        (costWord (bankTrialLocalNext ring root)
          bankTrialLocalTerminal (bankTrialLocalStart S)) =
      Prob.scheduleSum n T
        (bankTrialDurationStageWord ring root 0
          (bankTrialLocalStart S)) +
        (Prob.scheduleSum n T
          (bankTrialDurationStageWord ring root 1
            (bankTrialLocalStart S)) +
         Prob.scheduleSum n T
          (bankTrialDurationStageWord ring root 2
            (bankTrialLocalStart S)))
    rw [← bankTrialDurationSumAdd n T
      (bankTrialDurationStageWord ring root 1
        (bankTrialLocalStart S))
      (bankTrialDurationStageWord ring root 2
        (bankTrialLocalStart S))]
    rw [← bankTrialDurationSumAdd n T
      (bankTrialDurationStageWord ring root 0
        (bankTrialLocalStart S))
      (fun w =>
        bankTrialDurationStageWord ring root 1
          (bankTrialLocalStart S) w +
        bankTrialDurationStageWord ring root 2
          (bankTrialLocalStart S) w)]
    apply congrArg (Prob.scheduleSum n T)
    funext w
    exact bankTrialDurationWordPartition ring root
      (bankTrialLocalStart S) w
  have harith :
      n +
        ((2 * (2 * (compileAdvice q).b + 2) + 1) * n +
         (2 * (2 * (compileAdvice q).b + 2) + 2) * n) =
      (8 * (compileAdvice q).b + 12) * n := by
    have hc :
        1 + ((2 * (2 * (compileAdvice q).b + 2) + 1) +
             (2 * (2 * (compileAdvice q).b + 2) + 2)) =
          8 * (compileAdvice q).b + 12 := by omega
    calc
      _ =
        (1 + ((2 * (2 * (compileAdvice q).b + 2) + 1) +
          (2 * (2 * (compileAdvice q).b + 2) + 2))) * n := by
            symm
            rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
      _ = (8 * (compileAdvice q).b + 12) * n := by rw [hc]
  calc
    costNumerator (bankTrialLocalNext ring root)
        bankTrialLocalTerminal (bankTrialLocalStart S) T =
      bankTrialDurationStageMass ring root 0 S T +
        (bankTrialDurationStageMass ring root 1 S T +
         bankTrialDurationStageMass ring root 2 S T) := hsum
    _ ≤ n ^ T * n +
        (n ^ T * ((2 * (2 * (compileAdvice q).b + 2) + 1) * n) +
         n ^ T * ((2 * (2 * (compileAdvice q).b + 2) + 2) * n)) :=
      Nat.add_le_add (hrace S hclean T)
        (Nat.add_le_add (hworker S hclean T)
          (hreset S hclean T))
    _ = n ^ T * ((8 * (compileAdvice q).b + 12) * n) := by
      calc
        _ = n ^ T *
          (n +
            ((2 * (2 * (compileAdvice q).b + 2) + 1) * n +
             (2 * (2 * (compileAdvice q).b + 2) + 2) * n)) := by
              simpa only [Nat.mul_add]
        _ = n ^ T * ((8 * (compileAdvice q).b + 12) * n) := by
              rw [harith]

/-- An abstract FINISHED two-outcome stopped-time inequality.
Masses are integer numerators on a common finite probability
space. There is no assumption that duration and outcome are
independent. The partition premise must NOT be used for a local
observer at an arbitrary finite T while some paths are active. -/
theorem bankTrialDurationConditionalFailureHalf
    (totalMass successMass failureMass
      totalCost failureCost B : Nat)
    (hpartition : successMass + failureMass = totalMass)
    (hhalf : 2 * successMass ≤ totalMass)
    (hsub : failureCost ≤ totalCost)
    (huncond : totalCost ≤ totalMass * B) :
    failureCost ≤ failureMass * (2 * B) := by
  have hmass : totalMass ≤ 2 * failureMass := by omega
  calc
    failureCost ≤ totalCost := hsub
    _ ≤ totalMass * B := huncond
    _ ≤ (2 * failureMass) * B :=
      Nat.mul_le_mul_right B hmass
    _ = failureMass * (2 * B) := by ac_rfl

/-- C.7 algebra: 2^K p <= 1 and K>=1 imply p<=1/2;
the failure-conditioned bound doubles C.6. -/
theorem bankTrialDurationC7Abstract
    (b n K totalMass successMass failureMass
      totalCost failureCost : Nat)
    (hK : 1 ≤ K)
    (hpartition : successMass + failureMass = totalMass)
    (hprob : 2 ^ K * successMass ≤ totalMass)
    (hsub : failureCost ≤ totalCost)
    (hC6 : totalCost ≤ totalMass * ((8 * b + 12) * n)) :
    failureCost ≤ failureMass * ((16 * b + 24) * n) := by
  have hpower : 2 ≤ 2 ^ K := by
    cases K with
    | zero => omega
    | succ k =>
        rw [Nat.pow_succ]
        have hp : 0 < 2 ^ k := Nat.pow_pos (by omega)
        omega
  have hhalf : 2 * successMass ≤ totalMass :=
    Nat.le_trans (Nat.mul_le_mul_right successMass hpower) hprob
  have hc := bankTrialDurationConditionalFailureHalf
    totalMass successMass failureMass totalCost failureCost
    ((8 * b + 12) * n) hpartition hhalf hsub hC6
  calc
    failureCost ≤ failureMass * (2 * ((8 * b + 12) * n)) := hc
    _ = failureMass * ((16 * b + 24) * n) := by
      have he : 2 * (8 * b + 12) = 16 * b + 24 := by omega
      rw [← Nat.mul_assoc 2 (8 * b + 12) n, he]

/-- Completed failure and still-active mass at horizon T. -/
noncomputable def bankTrialDurationFailureMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) : Nat :=
  Prob.scheduleSum n T (fun w =>
    if (bankTrialLocalRun ring root w
      (bankTrialLocalStart S)).phase = .lost then 1 else 0)

noncomputable def bankTrialDurationActiveMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) : Nat :=
  Prob.scheduleSum n T (fun w =>
    if bankTrialLocalTerminal
      (bankTrialLocalRun ring root w (bankTrialLocalStart S))
    then 0 else 1)

noncomputable def bankTrialDurationFailureCostMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) : Nat :=
  Prob.scheduleSum n T (fun w =>
    if (bankTrialLocalRun ring root w
      (bankTrialLocalStart S)).phase = .lost then
      costWord (bankTrialLocalNext ring root)
        bankTrialLocalTerminal (bankTrialLocalStart S) w
    else 0)

/-- An explicit active residual is indispensable at finite T. -/
private theorem bankTrialDurationOutcomeOne {q : Nat}
    (z : BankTrialLocalState q) :
    (if z.phase = .won then 1 else 0) +
      ((if z.phase = .lost then 1 else 0) +
       (if bankTrialLocalTerminal z then 0 else 1)) = 1 := by
  cases z with
  | mk bank phase =>
      cases phase <;> simp [bankTrialLocalTerminal]

theorem bankTrialDurationMassPartition {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) :
    bankTrialProbabilityWinMass ring root S T +
      (bankTrialDurationFailureMass ring root S T +
       bankTrialDurationActiveMass ring root S T) = n ^ T := by
  classical
  unfold bankTrialProbabilityWinMass
    bankTrialDurationFailureMass bankTrialDurationActiveMass
  rw [← bankTrialDurationSumAdd n T
    (fun w => if (bankTrialLocalRun ring root w
      (bankTrialLocalStart S)).phase = .lost then 1 else 0)
    (fun w => if bankTrialLocalTerminal
      (bankTrialLocalRun ring root w (bankTrialLocalStart S))
      then 0 else 1)]
  rw [← bankTrialDurationSumAdd n T
    (fun w => if (bankTrialLocalRun ring root w
      (bankTrialLocalStart S)).phase = .won then 1 else 0)
    (fun w =>
      (if (bankTrialLocalRun ring root w
        (bankTrialLocalStart S)).phase = .lost then 1 else 0) +
      (if bankTrialLocalTerminal
        (bankTrialLocalRun ring root w (bankTrialLocalStart S))
        then 0 else 1))]
  have hpoint :
      Prob.scheduleSum n T (fun w =>
        (if (bankTrialLocalRun ring root w
          (bankTrialLocalStart S)).phase = .won then 1 else 0) +
        ((if (bankTrialLocalRun ring root w
          (bankTrialLocalStart S)).phase = .lost then 1 else 0) +
         (if bankTrialLocalTerminal
           (bankTrialLocalRun ring root w (bankTrialLocalStart S))
           then 0 else 1))) =
      Prob.scheduleSum n T (fun _ => 1) := by
    apply congrArg (Prob.scheduleSum n T)
    funext w
    exact bankTrialDurationOutcomeOne
      (bankTrialLocalRun ring root w (bankTrialLocalStart S))
  rw [hpoint]
  simpa only [Nat.mul_one] using
    (bankTrialProbabilityScheduleSumConst n T 1)

/-- Finite-prefix C.7 with ACTIVE SLACK, not an incorrect claim
that all runs have finished by T. Requires the still-unproved
upper probability target and three C.6 accounting budgets. -/
theorem bankTrialDurationC7FiniteOfBudgets {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hrace : BankTrialDurationRaceBudget (q := q) ring root)
    (hworker : BankTrialDurationWorkerBudget (q := q) ring root)
    (hreset : BankTrialDurationRecoveryBudget (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hupper : BankTrialProbabilityUpperTarget ring root S)
    (hsp : (compileAdvice q).useSmall = false)
    (hn : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hK : 1 ≤ (compileAdvice q).K)
    (T : Nat) :
    bankTrialDurationFailureCostMass ring root S T ≤
      (bankTrialDurationFailureMass ring root S T +
       bankTrialDurationActiveMass ring root S T) *
        ((16 * (compileAdvice q).b + 24) * n) := by
  have hsub :
      bankTrialDurationFailureCostMass ring root S T ≤
        costNumerator (bankTrialLocalNext ring root)
          bankTrialLocalTerminal (bankTrialLocalStart S) T := by
    unfold bankTrialDurationFailureCostMass
    change Prob.scheduleSum n T (fun w =>
      if (bankTrialLocalRun ring root w
        (bankTrialLocalStart S)).phase = .lost then
        costWord (bankTrialLocalNext ring root)
          bankTrialLocalTerminal (bankTrialLocalStart S) w
      else 0) ≤
        Prob.scheduleSum n T
          (costWord (bankTrialLocalNext ring root)
            bankTrialLocalTerminal (bankTrialLocalStart S))
    apply bankTrialProbabilityScheduleSumMono n T
    intro w
    split
    · exact Nat.le_refl _
    · exact Nat.zero_le _
  exact bankTrialDurationC7Abstract
    (compileAdvice q).b n (compileAdvice q).K
    (n ^ T) (bankTrialProbabilityWinMass ring root S T)
    (bankTrialDurationFailureMass ring root S T +
      bankTrialDurationActiveMass ring root S T)
    (costNumerator (bankTrialLocalNext ring root)
      bankTrialLocalTerminal (bankTrialLocalStart S) T)
    (bankTrialDurationFailureCostMass ring root S T)
    hK (bankTrialDurationMassPartition ring root S T)
    (hupper hsp hn hclean T) hsub
    (bankTrialDurationC6OfBudgets (q := q) ring root
      hrace hworker hreset S hclean T)

/-- Cost of the genuinely completed WON paths, not of the
unconditional trial or of arbitrarily classified active words. -/
noncomputable def bankTrialDurationSuccessCostMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) : Nat :=
  Prob.scheduleSum n T (fun w =>
    if (bankTrialLocalRun ring root w
      (bankTrialLocalStart S)).phase = .won then
      costWord (bankTrialLocalNext ring root)
        bankTrialLocalTerminal (bankTrialLocalStart S) w
    else 0)

/-- MISSING C.8, paper lines 376--388.
This exact finite-prefix, ACTIVE-SLACK specification is the
remaining outcome-dependent worker-clock obligation.
Its derivation requires an all-K-head worker path, the adapted
watchdog survival probability, and a correct conditional charge.
It is NOT a theorem; C.6 does not imply it. -/
def BankTrialDurationSuccessConditionalTarget {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    BankTrialLocalClean q S →
    ∀ T : Nat,
      bankTrialDurationSuccessCostMass ring root S T ≤
        (bankTrialProbabilityWinMass ring root S T +
          bankTrialDurationActiveMass ring root S T) *
          ((8 * (compileAdvice q).b + 12) *
            ((compileAdvice q).K + 1) * n)

/-- MISSING passage from finite-word active slack to conditional
expectations at actual terminal time. Paper C.6--C.8,
lines 358--391. It must establish almost-sure termination;
the present module does not assert any limiting theorem. -/
def BankTrialDurationAlmostSureExit {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    BankTrialLocalClean q S →
    ∀ B : Nat, ∃ T : Nat,
      B * bankTrialDurationActiveMass ring root S T ≤ n ^ T

end L3


/-!
Class-0 occupation drift on the original local BANK
trial observer, not on a replacement scheduler. An armed head may
re-arm after a worker; "two races" is an EXPECTATION, not a
two-race deterministic countdown.

The n-credit LIVE potential proves C.6's race budget for
distinct root ports (n >= 2). The original budget Prop also
quantifies over n=1; that degenerate port case is separated.

All source bytes above are unchanged.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- This is a prospective occupation-credit potential, not the
number of remaining possible races: a trial may re-arm repeatedly. -/
def bankTrialDurationRacePotential (n : Nat) {q : Nat}
    (z : BankTrialLocalState q) : Nat :=
  match z.phase with
  | .live _ => n
  | .recovery => 0
  | .won => 0
  | .lost => 0

theorem bankTrialDurationRacePotentialCap (n : Nat) {q : Nat}
    (z : BankTrialLocalState q) :
    bankTrialDurationRacePotential n z ≤ n := by
  unfold bankTrialDurationRacePotential
  split <;> omega

/-- A zero incoming child compensates one unit of cost in the
complete finite physical-edge sum. -/
private theorem bankTrialDurationSumBoundWithZero :
    ∀ (n : Nat) (f : Fin n → Nat)
      (chosen : Fin n) (c : Nat),
      (∀ e : Fin n, f e ≤ c) →
      f chosen = 0 →
      c + (List.ofFn f).sum ≤ n * c := by
  intro n
  induction n with
  | zero =>
      intro f chosen c _ _
      exact Fin.elim0 chosen
  | succ n ih =>
      intro f chosen c hbound hzero
      rw [List.ofFn_succ, List.sum_cons]
      cases chosen using Fin.cases with
      | zero =>
          have htail :
              (List.ofFn (fun i : Fin n => f i.succ)).sum ≤ n * c := by
            have hsum := ofFn_sum_le
              (fun i : Fin n => f i.succ)
              (fun _ : Fin n => c)
              (fun i => hbound i.succ)
            rw [ofFn_sum_const] at hsum
            exact hsum
          rw [hzero, Nat.zero_add]
          calc
            c + (List.ofFn (fun i : Fin n => f i.succ)).sum ≤
                c + n * c := Nat.add_le_add_left htail c
            _ = Nat.succ n * c := by
              rw [Nat.succ_mul]
              ac_rfl
      | succ i =>
          have htail := ih (fun j : Fin n => f j.succ)
            i c (fun j => hbound j.succ) hzero
          have hfirst := hbound (0 : Fin (n + 1))
          calc
            c + (f 0 + (List.ofFn
                (fun j : Fin n => f j.succ)).sum) =
              f 0 + (c + (List.ofFn
                (fun j : Fin n => f j.succ)).sum) := by omega
            _ ≤ c + n * c := Nat.add_le_add hfirst htail
            _ = Nat.succ n * c := by
              rw [Nat.succ_mul]
              ac_rfl

/-- Wrap-safe, distinct root ports on a ring with at least
two sites. The proof uses the literal cyclic-neighbor map. -/
theorem bankTrialDurationIncomingPort {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (root : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor root) = root ∧
      ring.leftNeighbor root ≠ root := by
  have hright : ring.rightNeighbor (ring.leftNeighbor root) =
      root := by
    apply Fin.ext
    change (((root.val + n - 1) % n + 1) % n) = root.val
    rw [Nat.mod_add_mod]
    have he : root.val + n - 1 + 1 = root.val + n := by omega
    rw [he, Nat.add_mod]
    simp [Nat.mod_eq_of_lt root.isLt]
  refine ⟨hright, ?_⟩
  intro he
  have hh := congrArg ring.rightNeighbor he
  rw [hright] at hh
  exact (Counter.resetRootPortDistinct ring root hn) hh.symm

/-- Literal recovery output is again RECOVERY, WON, or LOST,
never LIVE. This remains valid under exceptional success. -/
theorem bankTrialDurationRecoveryRacePotentialZero {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    bankTrialDurationRacePotential n
      (bankTrialLocalNext ring root
        (⟨B, .recovery⟩ : BankTrialLocalState q) e) = 0 := by
  classical
  simp [bankTrialLocalNext, bankTrialDurationRacePotential]
    <;> split
    <;> (first
      | rfl
      | (rename_i heq
         split at heq <;> (try split at heq) <;> cases heq))

/-- For ARMED, incoming root changes a false-latch LIVE state
to RECOVERY; an already true latch wins. Neither branch is LIVE. -/
theorem bankTrialDurationArmedIncomingRacePotentialZero {n q : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (root : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (harmed : (B.fields ⟨0, by omega⟩).1 = .ARMED) :
    bankTrialDurationRacePotential n
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (ring.leftNeighbor root)) = 0 := by
  obtain ⟨hin, hne⟩ := bankTrialDurationIncomingPort ring hn root
  cases hsuccess : B.success with
  | false =>
      have hnext :=
        bankTrialProbabilityIncomingArmedEntersRecovery
          ring root (ring.leftNeighbor root)
          B begun hsuccess harmed hne hin
      rw [hnext]
      rfl
  | true =>
      have hlatched :=
        GrantBankReference.bankLocalReferenceLatchedStepClamped
          ring root (ring.leftNeighbor root) B hsuccess
      have hnext :
          bankTrialLocalNext ring root
              (⟨B, .live begun⟩ : BankTrialLocalState q)
              (ring.leftNeighbor root) =
            ⟨B, .won⟩ := by
        simp [bankTrialLocalNext, hlatched, hsuccess]
      rw [hnext]
      rfl

/-- Weighted one-step Bellman inequality for the actual
OLD-class-0 indicator. The LIVE credit need never decrease
on a successful head, but the incoming tail contributes zero. -/
theorem bankTrialDurationRacePotentialDrift {n q : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (root : Fin n) (z : BankTrialLocalState q)
    (hnot : ¬ bankTrialLocalTerminal z) :
    n * (if bankTrialDurationClass z = 0 then 1 else 0) +
      (List.ofFn (fun e : Fin n =>
        bankTrialDurationRacePotential n
          (bankTrialLocalNext ring root z e))).sum ≤
        n * bankTrialDurationRacePotential n z := by
  cases z with
  | mk B phase =>
      cases phase with
      | live begun =>
          have hparent :
              bankTrialDurationRacePotential n
                (⟨B, .live begun⟩ : BankTrialLocalState q) = n := rfl
          rw [hparent]
          by_cases harmed : (B.fields ⟨0, by omega⟩).1 = .ARMED
          · have hclass :
                bankTrialDurationClass
                  (⟨B, .live begun⟩ : BankTrialLocalState q) = 0 := by
                show (if (B.fields ⟨0, by omega⟩).1 = .ARMED then 0 else 1) = 0
                exact if_pos harmed
            rw [hclass]
            simp only [if_pos rfl, ↓reduceIte, Nat.mul_one]
            exact bankTrialDurationSumBoundWithZero n
              (fun e : Fin n =>
                bankTrialDurationRacePotential n
                  (bankTrialLocalNext ring root
                    (⟨B, .live begun⟩ : BankTrialLocalState q) e))
              (ring.leftNeighbor root) n
              (fun e =>
                bankTrialDurationRacePotentialCap n
                  (bankTrialLocalNext ring root
                    (⟨B, .live begun⟩ : BankTrialLocalState q) e))
              (bankTrialDurationArmedIncomingRacePotentialZero
                ring hn root B begun harmed)
          · have hclass :
                bankTrialDurationClass
                  (⟨B, .live begun⟩ : BankTrialLocalState q) ≠ 0 := by
                show ¬ (if (B.fields ⟨0, by omega⟩).1 = .ARMED then 0 else 1) = 0
                rw [if_neg harmed]
                exact Nat.one_ne_zero
            simp only [if_neg hclass, Nat.mul_zero, Nat.zero_add]
            have hsum := ofFn_sum_le
              (fun e : Fin n =>
                bankTrialDurationRacePotential n
                  (bankTrialLocalNext ring root
                    (⟨B, .live begun⟩ : BankTrialLocalState q) e))
              (fun _ : Fin n => n)
              (fun e =>
                bankTrialDurationRacePotentialCap n
                  (bankTrialLocalNext ring root
                    (⟨B, .live begun⟩ : BankTrialLocalState q) e))
            rw [ofFn_sum_const] at hsum
            exact hsum
      | recovery =>
          have hsum := ofFn_sum_eq
            (fun e : Fin n =>
              bankTrialDurationRacePotential n
                (bankTrialLocalNext ring root
                  (⟨B, .recovery⟩ : BankTrialLocalState q) e))
            (fun _ : Fin n => 0)
            (fun e =>
              bankTrialDurationRecoveryRacePotentialZero
                ring root e B)
          rw [hsum, ofFn_sum_const]
          change n * 0 + n * 0 ≤ n * 0
          omega
      | won =>
          exact False.elim (hnot (Or.inl rfl))
      | lost =>
          exact False.elim (hnot (Or.inr rfl))

/-- Generic finite-horizon charged-word lemma on the EXISTING
original Fin n scheduler and the original phase observer.
G can restrict the drift to the actual reachable class. -/
private theorem bankTrialDurationStageCostOfDrift {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (tag : Nat)
    (G : BankTrialLocalState q → Prop)
    (potential : BankTrialLocalState q → Nat)
    (hclosed : ∀ z, G z → ∀ e : Fin n,
      G (bankTrialLocalNext ring root z e))
    (hdrift : ∀ z, G z → ¬ bankTrialLocalTerminal z →
      n * (if bankTrialDurationClass z = tag then 1 else 0) +
        (List.ofFn (fun e : Fin n =>
          potential (bankTrialLocalNext ring root z e))).sum ≤
            n * potential z) :
    ∀ (T : Nat) (z : BankTrialLocalState q), G z →
      Prob.scheduleSum n T
        (bankTrialDurationStageWord ring root tag z) ≤
      n ^ T * potential z := by
  classical
  intro T
  induction T with
  | zero =>
      intro z hz
      rw [bankTrialProbabilityScheduleSumZero]
      exact Nat.zero_le _
  | succ T ih =>
      intro z hz
      by_cases ht : bankTrialLocalTerminal z
      · rw [bankTrialProbabilityScheduleSumFirst]
        have heq :=
          ofFn_sum_eq
            (fun e : Fin n =>
              Prob.scheduleSum n T
                (fun w => bankTrialDurationStageWord
                  ring root tag z (e :: w)))
            (fun _ : Fin n => 0)
            (fun e => by
              have hfun :
                  (fun w : List (Fin n) =>
                    bankTrialDurationStageWord
                      ring root tag z (e :: w)) =
                    (fun _ : List (Fin n) => 0) := by
                funext w
                simp only [bankTrialDurationStageWord, if_pos ht]
              rw [hfun, bankTrialProbabilityScheduleSumConst]
              omega)
        rw [heq, ofFn_sum_const]
        exact Nat.zero_le _
      · rw [bankTrialProbabilityScheduleSumFirst]
        have hstep : ∀ e : Fin n,
            Prob.scheduleSum n T
              (fun w => bankTrialDurationStageWord
                ring root tag z (e :: w)) =
            n ^ T * (if bankTrialDurationClass z = tag then 1 else 0) +
              Prob.scheduleSum n T
                (bankTrialDurationStageWord ring root tag
                  (bankTrialLocalNext ring root z e)) := by
          intro e
          have hfun :
              (fun w : List (Fin n) =>
                bankTrialDurationStageWord
                  ring root tag z (e :: w)) =
              (fun w : List (Fin n) =>
                (if bankTrialDurationClass z = tag then 1 else 0) +
                bankTrialDurationStageWord
                  ring root tag
                  (bankTrialLocalNext ring root z e) w) := by
            funext w
            simp only [bankTrialDurationStageWord, if_neg ht]
          rw [hfun, bankTrialDurationSumAdd,
            bankTrialProbabilityScheduleSumConst]
        have hsum := ofFn_sum_le
          (fun e : Fin n =>
            Prob.scheduleSum n T
              (fun w => bankTrialDurationStageWord
                ring root tag z (e :: w)))
          (fun e : Fin n =>
            n ^ T * (if bankTrialDurationClass z = tag then 1 else 0) +
              n ^ T * potential (bankTrialLocalNext ring root z e))
          (fun e => by
            rw [hstep e]
            exact Nat.add_le_add_left
              (ih (bankTrialLocalNext ring root z e)
                (hclosed z hz e)) _)
        calc
          (List.ofFn (fun e : Fin n =>
              Prob.scheduleSum n T
                (fun w => bankTrialDurationStageWord
                  ring root tag z (e :: w)))).sum ≤
            (List.ofFn (fun e : Fin n =>
              n ^ T * (if bankTrialDurationClass z = tag then 1 else 0) +
                n ^ T * potential
                  (bankTrialLocalNext ring root z e))).sum := hsum
          _ = n ^ T *
              (n * (if bankTrialDurationClass z = tag then 1 else 0) +
                (List.ofFn (fun e : Fin n =>
                  potential (bankTrialLocalNext ring root z e))).sum) := by
              rw [ofFn_sum_add, ofFn_sum_const, ofFn_sum_mul_left]
              rw [Nat.mul_add]
              ac_rfl
          _ ≤ n ^ T * (n * potential z) :=
            Nat.mul_le_mul_left _ (hdrift z hz ht)
          _ = n ^ (T + 1) * potential z := by
            rw [Nat.pow_succ]
            ac_rfl

/-- Main race result on physical rings with distinct ports.
This is the ORIGINAL stage mass, not a separate race-edge clock. -/
theorem bankTrialDurationRaceBudgetDistinctPorts {n q : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (root : Fin n) :
    BankTrialDurationRaceBudget (q := q) ring root := by
  intro S hclean T
  have hcost := bankTrialDurationStageCostOfDrift
    ring root 0
    (fun _ : BankTrialLocalState q => True)
    (bankTrialDurationRacePotential n)
    (by intro z _ e; exact True.intro)
    (by intro z _ hnot
        exact bankTrialDurationRacePotentialDrift ring hn root z hnot)
    T (bankTrialLocalStart S) True.intro
  change bankTrialDurationStageMass ring root 0 S T ≤
    n ^ T * bankTrialDurationRacePotential n
      (bankTrialLocalStart S) at hcost
  have hstart :
      bankTrialDurationRacePotential n (bankTrialLocalStart S) = n := rfl
  rw [hstart] at hcost
  exact hcost

/-- The original RaceBudget has no 2<=n premise. For n=1,
the outgoing/incoming orientation is a single physical edge;
the distinct-port proof cannot be applied to that degenerate
case without a separate exact single-port row argument. -/
def BankTrialDurationSinglePortRace {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  n = 1 →
  ∀ (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    BankTrialLocalClean q S →
    ∀ T : Nat,
      bankTrialDurationStageMass ring root 0 S T ≤ n ^ T * n

theorem bankTrialDurationRaceBudgetOfSinglePort {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hone : BankTrialDurationSinglePortRace (q := q) ring root) :
    BankTrialDurationRaceBudget (q := q) ring root := by
  by_cases hn : 2 ≤ n
  · exact bankTrialDurationRaceBudgetDistinctPorts ring hn root
  · have hOne : n = 1 := by
      have hpos := ring.hn
      omega
    exact hone hOne

/-- Reachability on one actual chronological local scheduler word. -/
def BankTrialDurationReachable {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (z : BankTrialLocalState q) : Prop :=
  ∃ w : List (Fin n),
    bankTrialLocalRun ring root w (bankTrialLocalStart S) = z

theorem bankTrialDurationReachableNext {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (z : BankTrialLocalState q)
    (hz : BankTrialDurationReachable ring root S z)
    (e : Fin n) :
    BankTrialDurationReachable ring root S
      (bankTrialLocalNext ring root z e) := by
  obtain ⟨w, hw⟩ := hz
  refine ⟨w ++ [e], ?_⟩
  rw [bankTrialLocalRunAppend, hw]
  rfl

/-- The remaining ACTUAL worker-row progress gap, rather than
a missing restatement of the desired worker-cost bound.
C.6 lines 373--376 require a rank that counts aborted carries,
comparison launches and the expected head-continuation credit. -/
def BankTrialDurationWorkerPotentialCertificate {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  ∃ potential : BankTrialLocalState q → Nat,
    potential (bankTrialLocalStart S) ≤
      ((2 * (2 * (compileAdvice q).b + 2) + 1) * n) ∧
    ∀ z : BankTrialLocalState q,
      BankTrialDurationReachable ring root S z →
      ¬ bankTrialLocalTerminal z →
      n * (if bankTrialDurationClass z = 1 then 1 else 0) +
        (List.ofFn (fun e : Fin n =>
          potential (bankTrialLocalNext ring root z e))).sum ≤
          n * potential z

/-- Conditional worker theorem with the same schedule and the
same costWord semantics. No unproved source fact is assumed silently. -/
theorem bankTrialDurationWorkerBudgetOfPotential {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsource : ∀ S : GrantBankReference.BankLocalReference
      (compileAdvice q).b,
      BankTrialLocalClean q S →
      BankTrialDurationWorkerPotentialCertificate ring root S) :
    BankTrialDurationWorkerBudget (q := q) ring root := by
  intro S hclean T
  obtain ⟨potential, hcap, hdrift⟩ := hsource S hclean
  have hstart : BankTrialDurationReachable ring root S
      (bankTrialLocalStart S) := ⟨[], rfl⟩
  have hcost := bankTrialDurationStageCostOfDrift
    ring root 1
    (BankTrialDurationReachable ring root S)
    potential
    (fun z hz e =>
      bankTrialDurationReachableNext ring root S z hz e)
    (fun z hz hnot => hdrift z hz hnot)
    T (bankTrialLocalStart S) hstart
  change bankTrialDurationStageMass ring root 1 S T ≤
    n ^ T * potential (bankTrialLocalStart S) at hcost
  exact Nat.le_trans hcost (Nat.mul_le_mul_left (n ^ T) hcap)

end L3


/-!
Amortized HEAD accounting on the original BANK
observer and its genuine Fin n scheduler.

Paper spatial-counter.tex C.6 lines 354--361, in particular
"The fair race gives E H <= 1" and the (2L+1)n cost per head.

A worker can return to ARMED and cause another head. Thus a
naive per-excursion countdown in a local LIVE state does not
bound the total number of heads on every *individual* word.
The expected head count, however, follows exactly from the
already class-0 race budget. There is no additional
independent scheduler: one head is the selected outgoing root
letter in a preterminal old ARMED state.

The ONE open owner-row proposition at the end expresses the
remaining necessary physical progress: replenish the worker
rank by (2L+1)n on a head, charge one unit for each class-1
letter, and never create unsupported rank on other edges.
Its one-step inequality must be established from BANK's
increment, comparison, launch, abort and return owner rows.
No expected-head independence or unconditional worker theorem
is asserted.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Actual outgoing head indicator at the OLD observer state
and the selected ORIGINAL physical scheduler letter. -/
def bankTrialDurationHeadEdge {n q : Nat}
    (root : Fin n) (z : BankTrialLocalState q)
    (e : Fin n) : Nat :=
  if bankTrialDurationClass z = 0 then
    if e = root then 1 else 0
  else 0

/-- Count real selected outgoing ARMED heads until the same
local WON/LOST first-hit stop; an unfinished word is allowed. -/
noncomputable def bankTrialDurationHeadWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    BankTrialLocalState q → List (Fin n) → Nat
  | _, [] => 0
  | z, e :: rest =>
      if bankTrialLocalTerminal z then 0
      else bankTrialDurationHeadEdge root z e +
        bankTrialDurationHeadWord ring root
          (bankTrialLocalNext ring root z e) rest

/-- Integer mass of all heads on the original n^T tapes. -/
noncomputable def bankTrialDurationHeadMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q) (T : Nat) : Nat :=
  Prob.scheduleSum n T (bankTrialDurationHeadWord ring root z)

/-- Core Fin-list single-spike sum, with no Finset. -/
private theorem bankTrialDurationHeadSpikeSum (n : Nat) :
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
              if i.succ = (0 : Fin (n + 1)) then v else 0)).sum = 0 := by
          have hh := ofFn_sum_eq
            (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then v else 0)
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

/-- For a fixed OLD ARMED state, exactly one of the n physical
letters is the outgoing head opportunity. -/
theorem bankTrialDurationHeadEdgeSum {n q : Nat}
    (root : Fin n) (z : BankTrialLocalState q) :
    (List.ofFn (fun e : Fin n =>
      bankTrialDurationHeadEdge root z e)).sum =
        (if bankTrialDurationClass z = 0 then 1 else 0) := by
  by_cases hclass : bankTrialDurationClass z = 0
  · simp only [bankTrialDurationHeadEdge, if_pos hclass]
    exact bankTrialDurationHeadSpikeSum n root 1
  · simp only [bankTrialDurationHeadEdge, if_neg hclass]
    rw [ofFn_sum_const, Nat.mul_zero]

private theorem bankTrialDurationStageSumTerminal {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (tag : Nat)
    (z : BankTrialLocalState q)
    (ht : bankTrialLocalTerminal z) (T : Nat) :
    Prob.scheduleSum n T
      (bankTrialDurationStageWord ring root tag z) = 0 := by
  have hfun :
      (bankTrialDurationStageWord ring root tag z) =
        (fun _ : List (Fin n) => 0) := by
    funext word
    cases word with
    | nil => rfl
    | cons e rest =>
        simp only [bankTrialDurationStageWord, if_pos ht]
  rw [hfun, bankTrialProbabilityScheduleSumConst]
  exact Nat.mul_zero _

private theorem bankTrialDurationHeadSumTerminal {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q)
    (ht : bankTrialLocalTerminal z) (T : Nat) :
    bankTrialDurationHeadMass ring root z T = 0 := by
  have hfun :
      bankTrialDurationHeadWord ring root z =
        (fun _ : List (Fin n) => 0) := by
    funext word
    cases word with
    | nil => rfl
    | cons e rest =>
        simp only [bankTrialDurationHeadWord, if_pos ht]
  unfold bankTrialDurationHeadMass
  rw [hfun, bankTrialProbabilityScheduleSumConst]
  exact Nat.mul_zero _

/-- The exact first-letter recursion for every state-class
occupation on the same finite original scheduler. -/
private theorem bankTrialDurationStageSumSucc {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (tag : Nat)
    (z : BankTrialLocalState q) (T : Nat)
    (hnot : ¬ bankTrialLocalTerminal z) :
    Prob.scheduleSum n (T + 1)
      (bankTrialDurationStageWord ring root tag z) =
    n ^ (T + 1) *
        (if bankTrialDurationClass z = tag then 1 else 0) +
      (List.ofFn (fun e : Fin n =>
        Prob.scheduleSum n T
          (bankTrialDurationStageWord ring root tag
            (bankTrialLocalNext ring root z e)))).sum := by
  rw [bankTrialProbabilityScheduleSumFirst]
  have hstep : ∀ e : Fin n,
      Prob.scheduleSum n T (fun w =>
        bankTrialDurationStageWord ring root tag z (e :: w)) =
      n ^ T * (if bankTrialDurationClass z = tag then 1 else 0) +
        Prob.scheduleSum n T
          (bankTrialDurationStageWord ring root tag
            (bankTrialLocalNext ring root z e)) := by
    intro e
    have hfun :
        (fun w : List (Fin n) =>
          bankTrialDurationStageWord ring root tag z (e :: w)) =
        (fun w : List (Fin n) =>
          (if bankTrialDurationClass z = tag then 1 else 0) +
          bankTrialDurationStageWord ring root tag
            (bankTrialLocalNext ring root z e) w) := by
      funext w
      simp only [bankTrialDurationStageWord, if_neg hnot]
    rw [hfun, bankTrialDurationSumAdd,
      bankTrialProbabilityScheduleSumConst]
  have hsum := ofFn_sum_eq
    (fun e : Fin n =>
      Prob.scheduleSum n T (fun w =>
        bankTrialDurationStageWord ring root tag z (e :: w)))
    (fun e : Fin n =>
      n ^ T * (if bankTrialDurationClass z = tag then 1 else 0) +
      Prob.scheduleSum n T
        (bankTrialDurationStageWord ring root tag
          (bankTrialLocalNext ring root z e)))
    hstep
  rw [hsum, ofFn_sum_add, ofFn_sum_const, Nat.pow_succ]
  ac_rfl

/-- For outgoing heads the first letter is the actual single
root port, so the immediate head mass is n^T times the
single-edge sum rather than n^(T+1). -/
private theorem bankTrialDurationHeadSumSucc {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q) (T : Nat)
    (hnot : ¬ bankTrialLocalTerminal z) :
    bankTrialDurationHeadMass ring root z (T + 1) =
    n ^ T * (if bankTrialDurationClass z = 0 then 1 else 0) +
      (List.ofFn (fun e : Fin n =>
        bankTrialDurationHeadMass ring root
          (bankTrialLocalNext ring root z e) T)).sum := by
  unfold bankTrialDurationHeadMass
  rw [bankTrialProbabilityScheduleSumFirst]
  have hstep : ∀ e : Fin n,
      Prob.scheduleSum n T (fun w =>
        bankTrialDurationHeadWord ring root z (e :: w)) =
      n ^ T * bankTrialDurationHeadEdge root z e +
        Prob.scheduleSum n T
          (bankTrialDurationHeadWord ring root
            (bankTrialLocalNext ring root z e)) := by
    intro e
    have hfun :
        (fun w : List (Fin n) =>
          bankTrialDurationHeadWord ring root z (e :: w)) =
        (fun w : List (Fin n) =>
          bankTrialDurationHeadEdge root z e +
            bankTrialDurationHeadWord ring root
              (bankTrialLocalNext ring root z e) w) := by
      funext w
      simp only [bankTrialDurationHeadWord, if_neg hnot]
    rw [hfun, bankTrialDurationSumAdd,
      bankTrialProbabilityScheduleSumConst]
  have hsum := ofFn_sum_eq
    (fun e : Fin n =>
      Prob.scheduleSum n T (fun w =>
        bankTrialDurationHeadWord ring root z (e :: w)))
    (fun e : Fin n =>
      n ^ T * bankTrialDurationHeadEdge root z e +
        Prob.scheduleSum n T
          (bankTrialDurationHeadWord ring root
            (bankTrialLocalNext ring root z e)))
    hstep
  rw [hsum, ofFn_sum_add, ofFn_sum_mul_left,
    bankTrialDurationHeadEdgeSum]

/-- Exact finite-horizon compensation identity: each armed
OLD-state time-step sees each of the n ports once across the
complete uniform schedule sum, and exactly one is the head.
No independence of the worker duration is assumed. -/
theorem bankTrialDurationRaceMassEqualsNHeads {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ T : Nat, ∀ z : BankTrialLocalState q,
      Prob.scheduleSum n T
        (bankTrialDurationStageWord ring root 0 z) =
          n * bankTrialDurationHeadMass ring root z T := by
  intro T
  induction T with
  | zero =>
      intro z
      unfold bankTrialDurationHeadMass
      rw [bankTrialProbabilityScheduleSumZero,
        bankTrialProbabilityScheduleSumZero]
      rfl
  | succ T ih =>
      intro z
      by_cases ht : bankTrialLocalTerminal z
      · rw [bankTrialDurationStageSumTerminal
          ring root 0 z ht (T + 1),
          bankTrialDurationHeadSumTerminal
            ring root z ht (T + 1)]
        rfl
      · rw [bankTrialDurationStageSumSucc
          ring root 0 z T ht,
          bankTrialDurationHeadSumSucc ring root z T ht]
        have hchildren := ofFn_sum_eq
          (fun e : Fin n =>
            Prob.scheduleSum n T
              (bankTrialDurationStageWord ring root 0
                (bankTrialLocalNext ring root z e)))
          (fun e : Fin n =>
            n * bankTrialDurationHeadMass ring root
              (bankTrialLocalNext ring root z e) T)
          (fun e => ih (bankTrialLocalNext ring root z e))
        rw [hchildren, ofFn_sum_mul_left, Nat.pow_succ,
          Nat.mul_add]
        ac_rfl

/-- Paper C.6 line 356, E[H] <= 1, now an exact finite-horizon
theorem. The mass identity and class-0 race drift give
the result for all CLEAN seeds and n >= 2. -/
theorem bankTrialDurationExpectedHeadsAtMostOne {n q : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) (T : Nat) :
    bankTrialDurationHeadMass ring root
      (bankTrialLocalStart S) T ≤ n ^ T := by
  have heq := bankTrialDurationRaceMassEqualsNHeads
    ring root T (bankTrialLocalStart S)
  have hrace := bankTrialDurationRaceBudgetDistinctPorts
    ring hn root S hclean T
  change Prob.scheduleSum n T
      (bankTrialDurationStageWord ring root 0
        (bankTrialLocalStart S)) ≤ n ^ T * n at hrace
  rw [heq, Nat.mul_comm (n ^ T) n] at hrace
  by_cases hle :
      bankTrialDurationHeadMass ring root
        (bankTrialLocalStart S) T ≤ n ^ T
  · exact hle
  · have hlt : n ^ T <
        bankTrialDurationHeadMass ring root
          (bankTrialLocalStart S) T := Nat.lt_of_not_ge hle
    have hmul := Nat.mul_lt_mul_of_pos_left hlt
      (by omega : 0 < n)
    omega

/-- ONE remaining physical worker-row obligation. It is NOT a
proof of WorkerBudget and does not hide a changed scheduler.
The potential is a bounded remaining-worker rank, zero at
CLEAN start; one HEAD permits a refill of C=(2L+1)n.
Every original class-1 letter is charged one unit through the
n-scaled one-step inequality, and non-head steps receive no
refill. The actual increment/comparison/abort/collision rows
must establish this certificate, including repeated heads.
Paper spatial-counter.tex C.6 lines 358--361. -/
def BankTrialDurationWorkerHeadAmortizedRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ S : GrantBankReference.BankLocalReference
      (compileAdvice q).b,
    BankTrialLocalClean q S →
      ∃ potential : BankTrialLocalState q → Nat,
        potential (bankTrialLocalStart S) = 0 ∧
        (∀ z : BankTrialLocalState q,
          BankTrialDurationReachable ring root S z →
          potential z ≤
            ((2 * (2 * (compileAdvice q).b + 2) + 1) * n)) ∧
        ∀ z : BankTrialLocalState q,
          BankTrialDurationReachable ring root S z →
          ¬ bankTrialLocalTerminal z →
          n * (if bankTrialDurationClass z = 1 then 1 else 0) +
            (List.ofFn (fun e : Fin n =>
              potential (bankTrialLocalNext ring root z e))).sum ≤
          n * potential z +
            ((2 * (2 * (compileAdvice q).b + 2) + 1) * n) *
              (if bankTrialDurationClass z = 0 then 1 else 0)

/-- Amortized stage-mass induction with an explicit HEAD
recharge. This extends the StageCostOfDrift lemma rather
than replacing its original-clock semantics by a worker clock. -/
private theorem bankTrialDurationWorkerMassOfHeadDrift {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (potential : BankTrialLocalState q → Nat)
    (hdrift : ∀ z : BankTrialLocalState q,
      BankTrialDurationReachable ring root S z →
      ¬ bankTrialLocalTerminal z →
      n * (if bankTrialDurationClass z = 1 then 1 else 0) +
        (List.ofFn (fun e : Fin n =>
          potential (bankTrialLocalNext ring root z e))).sum ≤
      n * potential z +
        ((2 * (2 * (compileAdvice q).b + 2) + 1) * n) *
          (if bankTrialDurationClass z = 0 then 1 else 0)) :
    ∀ (T : Nat) (z : BankTrialLocalState q),
      BankTrialDurationReachable ring root S z →
      Prob.scheduleSum n T
        (bankTrialDurationStageWord ring root 1 z) ≤
        n ^ T * potential z +
          ((2 * (2 * (compileAdvice q).b + 2) + 1) * n) *
            bankTrialDurationHeadMass ring root z T := by
  classical
  intro T
  induction T with
  | zero =>
      intro z _
      rw [bankTrialProbabilityScheduleSumZero]
      unfold bankTrialDurationHeadMass
      rw [bankTrialProbabilityScheduleSumZero]
      simp only [bankTrialDurationStageWord,
        bankTrialDurationHeadWord, Nat.pow_zero,
        Nat.one_mul, Nat.mul_zero, Nat.add_zero]
      exact Nat.zero_le _
  | succ T ih =>
      intro z hz
      by_cases ht : bankTrialLocalTerminal z
      · rw [bankTrialDurationStageSumTerminal
          ring root 1 z ht (T + 1),
          bankTrialDurationHeadSumTerminal
            ring root z ht (T + 1)]
        exact Nat.zero_le _
      · rw [bankTrialDurationStageSumSucc
          ring root 1 z T ht,
          bankTrialDurationHeadSumSucc ring root z T ht]
        have hchildren := ofFn_sum_le
          (fun e : Fin n =>
            Prob.scheduleSum n T
              (bankTrialDurationStageWord ring root 1
                (bankTrialLocalNext ring root z e)))
          (fun e : Fin n =>
            n ^ T * potential (bankTrialLocalNext ring root z e) +
              ((2 * (2 * (compileAdvice q).b + 2) + 1) * n) *
                bankTrialDurationHeadMass ring root
                  (bankTrialLocalNext ring root z e) T)
          (fun e => ih (bankTrialLocalNext ring root z e)
            (bankTrialDurationReachableNext ring root S z hz e))
        calc
          n ^ (T + 1) *
              (if bankTrialDurationClass z = 1 then 1 else 0) +
              (List.ofFn (fun e : Fin n =>
                Prob.scheduleSum n T
                  (bankTrialDurationStageWord ring root 1
                    (bankTrialLocalNext ring root z e)))).sum ≤
            n ^ (T + 1) *
              (if bankTrialDurationClass z = 1 then 1 else 0) +
              (List.ofFn (fun e : Fin n =>
                n ^ T * potential (bankTrialLocalNext ring root z e) +
                  ((2 * (2 * (compileAdvice q).b + 2) + 1) * n) *
                    bankTrialDurationHeadMass ring root
                      (bankTrialLocalNext ring root z e) T)).sum :=
            Nat.add_le_add_left hchildren _
          _ = n ^ T * (n *
                (if bankTrialDurationClass z = 1 then 1 else 0) +
                (List.ofFn (fun e : Fin n =>
                  potential (bankTrialLocalNext ring root z e))).sum) +
              ((2 * (2 * (compileAdvice q).b + 2) + 1) * n) *
                (List.ofFn (fun e : Fin n =>
                  bankTrialDurationHeadMass ring root
                    (bankTrialLocalNext ring root z e) T)).sum := by
            rw [ofFn_sum_add, ofFn_sum_mul_left,
              ofFn_sum_mul_left, Nat.pow_succ, Nat.mul_add]
            simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
              Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          _ ≤ n ^ T * (n * potential z +
                ((2 * (2 * (compileAdvice q).b + 2) + 1) * n) *
                  (if bankTrialDurationClass z = 0 then 1 else 0)) +
              ((2 * (2 * (compileAdvice q).b + 2) + 1) * n) *
                (List.ofFn (fun e : Fin n =>
                  bankTrialDurationHeadMass ring root
                    (bankTrialLocalNext ring root z e) T)).sum :=
            Nat.add_le_add_right
              (Nat.mul_le_mul_left (n ^ T) (hdrift z hz ht)) _
          _ = n ^ (T + 1) * potential z +
              ((2 * (2 * (compileAdvice q).b + 2) + 1) * n) *
                (n ^ T *
                  (if bankTrialDurationClass z = 0 then 1 else 0) +
                  (List.ofFn (fun e : Fin n =>
                    bankTrialDurationHeadMass ring root
                      (bankTrialLocalNext ring root z e) T)).sum) := by
            rw [Nat.pow_succ, Nat.mul_add, Nat.mul_add]
            simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
              Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Under ONE explicit physical per-head progress obligation,
E[H] <= 1 gives the ORIGINAL class-1 C.6 WorkerBudget
on the true n-edge schedule (distinct ports n >= 2). -/
theorem bankTrialDurationWorkerBudgetDistinctPortsOfHeadRows
    {n q : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n) (root : Fin n)
    (hrows : BankTrialDurationWorkerHeadAmortizedRows
      (q := q) ring root) :
    BankTrialDurationWorkerBudget (q := q) ring root := by
  intro S hclean T
  obtain ⟨potential, hstart, _hcap, hdrift⟩ :=
    hrows S hclean
  have hreach : BankTrialDurationReachable ring root S
      (bankTrialLocalStart S) := ⟨[], rfl⟩
  have hcost := bankTrialDurationWorkerMassOfHeadDrift
    ring root S potential hdrift T (bankTrialLocalStart S) hreach
  change bankTrialDurationStageMass ring root 1 S T ≤
      n ^ T * potential (bankTrialLocalStart S) +
        ((2 * (2 * (compileAdvice q).b + 2) + 1) * n) *
          bankTrialDurationHeadMass ring root
            (bankTrialLocalStart S) T at hcost
  rw [hstart, Nat.mul_zero, Nat.zero_add] at hcost
  have hheads := bankTrialDurationExpectedHeadsAtMostOne
    ring hn root S hclean T
  calc
    bankTrialDurationStageMass ring root 1 S T ≤
      ((2 * (2 * (compileAdvice q).b + 2) + 1) * n) *
        bankTrialDurationHeadMass ring root
          (bankTrialLocalStart S) T := hcost
    _ ≤ ((2 * (2 * (compileAdvice q).b + 2) + 1) * n) *
        n ^ T :=
      Nat.mul_le_mul_left _ hheads
    _ = n ^ T *
        ((2 * (2 * (compileAdvice q).b + 2) + 1) * n) := by
      ac_rfl

end L3


/-!
Explicit worker service-rank potential and the remaining
CLEAN-reachable physical row obligation.

The source at BankTrialProbability.lean:3251 documents short-ring
aliasing. Its patch token/field frame lemmas only constrain
the selected two-slot patch, and do not by themselves establish
all-n clean-reachable worker uniqueness or progress. We therefore
prove a bounded concrete rank, its initial zero, service-distance
arithmetic, the generic nominated-edge sum, the unconditional
recovery branch, and a precise conditional original-clock Bellman
producer. The one still-open source row Prop is explicitly named.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- C = 2L+1, where L = 2b+2. -/
def bankTrialDurationWorkerLimit (q : Nat) : Nat :=
  2 * (2 * (compileAdvice q).b + 2) + 1

/-- Conservative remaining nominated worker services at digit
j, between 1 and b. The IR value also pays for its subsequent
AL return and the following CR/CL comparison. -/
def bankTrialDurationWorkerTokenRank
    (b j : Nat) : BTok → Nat
  | .E => 0
  | .RR => 2 * b + 2 - j
  | .RL => j
  | .IR => 4 * b + 5 - j
  | .AL => 2 * b + 3 + j
  | .CR0 => 2 * b + 2 - j
  | .CR1 => 2 * b + 2 - j
  | .CL0 => j
  | .CL1 => j

/-- Max over all original protected digit fields. Using a
maximum requires source-level unique-worker authentication
before a selected edge is known to lower this quantity. -/
def bankTrialDurationWorkerTokenMaximum {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Nat :=
  (List.ofFn (fun j : Fin (compileAdvice q).b =>
    bankTrialDurationWorkerTokenRank (compileAdvice q).b
      (j.val + 1) (bankTrialLiveWaveToken B j))).foldl Nat.max 0

/-- If a wait state has no worker, its root lease is still
a real clock. The fallback is used only without any token.
High-lease no-worker states cannot be handled by clipping
alone; the missing CLEAN-reachability row must exclude them
or exhibit an additional true progress edge. -/
def bankTrialDurationWorkerLeaseFallback {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Nat :=
  if ((bankTrialLiveWaveRootMode B = .IWAIT ∨
       bankTrialLiveWaveRootMode B = .CWAIT ∨
       bankTrialLiveWaveRootMode B = .RWAIT) ∧
      bankTrialDurationWorkerTokenMaximum B = 0) then
    (B.fields ⟨0, by omega⟩).2.2.2
  else 0

/-- A genuine state-only rank on the OLD clamped local observer.
ARMED has no worker debt, CSTART has one comparison launch,
and other LIVE modes use the token/lease rank. The cap C
holds even before uniqueness is established. -/
def bankTrialDurationWorkerRemaining {q : Nat}
    (z : BankTrialLocalState q) : Nat :=
  match z.phase with
  | .live _ =>
      Nat.min (bankTrialDurationWorkerLimit q)
        (if bankTrialLiveWaveRootMode z.bank = .ARMED then 0
         else if bankTrialLiveWaveRootMode z.bank = .CSTART then
           2 * (compileAdvice q).b + 2
         else
           Nat.max (bankTrialDurationWorkerTokenMaximum z.bank)
             (bankTrialDurationWorkerLeaseFallback z.bank))
  | .recovery => 0
  | .won => 0
  | .lost => 0

def bankTrialDurationWorkerRankPotential (n : Nat) {q : Nat}
    (z : BankTrialLocalState q) : Nat :=
  n * bankTrialDurationWorkerRemaining z

theorem bankTrialDurationWorkerRemainingCap {q : Nat}
    (z : BankTrialLocalState q) :
    bankTrialDurationWorkerRemaining z ≤
      bankTrialDurationWorkerLimit q := by
  cases z with
  | mk B phase =>
      cases phase with
      | live begun =>
          exact Nat.min_le_left _ _
      | recovery => exact Nat.zero_le _
      | won => exact Nat.zero_le _
      | lost => exact Nat.zero_le _

theorem bankTrialDurationWorkerRankPotentialCap (n : Nat)
    {q : Nat} (z : BankTrialLocalState q) :
    bankTrialDurationWorkerRankPotential n z ≤
      bankTrialDurationWorkerLimit q * n := by
  unfold bankTrialDurationWorkerRankPotential
  calc
    n * bankTrialDurationWorkerRemaining z ≤
        n * bankTrialDurationWorkerLimit q :=
      Nat.mul_le_mul_left n (bankTrialDurationWorkerRemainingCap z)
    _ = bankTrialDurationWorkerLimit q * n := Nat.mul_comm _ _

theorem bankTrialDurationWorkerRemainingArmed {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hm : bankTrialLiveWaveRootMode B = .ARMED) :
    bankTrialDurationWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) = 0 := by
  unfold bankTrialDurationWorkerRemaining
  simp only [if_pos hm, Nat.min_zero]

theorem bankTrialDurationWorkerRemainingClean {q : Nat}
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    bankTrialDurationWorkerRemaining (bankTrialLocalStart S) = 0 := by
  exact bankTrialDurationWorkerRemainingArmed S false hclean.2.1

theorem bankTrialDurationWorkerPotentialClean (n : Nat)
    {q : Nat}
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    bankTrialDurationWorkerRankPotential n (bankTrialLocalStart S) = 0 := by
  unfold bankTrialDurationWorkerRankPotential
  rw [bankTrialDurationWorkerRemainingClean S hclean]
  exact Nat.mul_zero n

/-- Strict numerical rank changes of normal physical worker
movements; these do not themselves establish which edge is
selected or that only one worker is present. -/
theorem bankTrialDurationWorkerForwardRank
    (b j : Nat) (hj : j + 1 ≤ b) :
    bankTrialDurationWorkerTokenRank b j .IR =
      bankTrialDurationWorkerTokenRank b (j + 1) .IR + 1 ∧
    bankTrialDurationWorkerTokenRank b j .RR =
      bankTrialDurationWorkerTokenRank b (j + 1) .RR + 1 ∧
    bankTrialDurationWorkerTokenRank b j .CR0 =
      bankTrialDurationWorkerTokenRank b (j + 1) .CR0 + 1 ∧
    bankTrialDurationWorkerTokenRank b j .CR1 =
      bankTrialDurationWorkerTokenRank b (j + 1) .CR1 + 1 := by
  simp only [bankTrialDurationWorkerTokenRank]
  omega

theorem bankTrialDurationWorkerReturnRank
    (b j : Nat) (hj : 1 ≤ j) :
    bankTrialDurationWorkerTokenRank b (j - 1) .AL + 1 ≤
      bankTrialDurationWorkerTokenRank b j .AL ∧
    bankTrialDurationWorkerTokenRank b (j - 1) .CL0 + 1 ≤
      bankTrialDurationWorkerTokenRank b j .CL0 ∧
    bankTrialDurationWorkerTokenRank b (j - 1) .CL1 + 1 ≤
      bankTrialDurationWorkerTokenRank b j .CL1 ∧
    bankTrialDurationWorkerTokenRank b (j - 1) .RL + 1 ≤
      bankTrialDurationWorkerTokenRank b j .RL := by
  simp only [bankTrialDurationWorkerTokenRank]
  omega

theorem bankTrialDurationWorkerCarryTurnRank
    (b j : Nat) (hj : j + 1 ≤ b) :
    bankTrialDurationWorkerTokenRank b (j + 1) .AL + 1 ≤
      bankTrialDurationWorkerTokenRank b j .IR := by
  simp only [bankTrialDurationWorkerTokenRank]
  omega

theorem bankTrialDurationWorkerTopTurnRank
    (b : Nat) (hb : 1 ≤ b) :
    bankTrialDurationWorkerTokenRank b (b - 1) .CL0 + 1 ≤
      bankTrialDurationWorkerTokenRank b b .CR0 ∧
    bankTrialDurationWorkerTokenRank b (b - 1) .CL1 + 1 ≤
      bankTrialDurationWorkerTokenRank b b .CR1 ∧
    bankTrialDurationWorkerTokenRank b (b - 1) .RL + 1 ≤
      bankTrialDurationWorkerTokenRank b b .RR ∧
    bankTrialDurationWorkerTokenRank b 1 .CR0 + 1 ≤
      2 * b + 2 ∧
    bankTrialDurationWorkerTokenRank b 1 .CR1 + 1 ≤
      2 * b + 2 ∧
    2 * b + 2 + 1 ≤
      bankTrialDurationWorkerTokenRank b 1 .AL := by
  simp only [bankTrialDurationWorkerTokenRank]
  omega

theorem bankTrialDurationWorkerRemainingTerminal {q : Nat}
    (z : BankTrialLocalState q)
    (ht : bankTrialLocalTerminal z) :
    bankTrialDurationWorkerRemaining z = 0 := by
  cases z with
  | mk B phase =>
      cases phase with
      | live begun =>
          rcases ht with h | h
          · cases h
          · cases h
      | recovery =>
          rcases ht with h | h
          · cases h
          · cases h
      | won => rfl
      | lost => rfl

/-- Recovery always remains RECOVERY, WON, or LOST; unlike LIVE
it can never acquire new class-1 occupation debt. -/
theorem bankTrialDurationWorkerRemainingRecoveryNextZero {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    bankTrialDurationWorkerRemaining
      (bankTrialLocalNext ring root
        (⟨B, .recovery⟩ : BankTrialLocalState q) e) = 0 := by
  classical
  unfold bankTrialLocalNext
  dsimp only
  split <;> (try split) <;> rfl

theorem bankTrialDurationWorkerRemainingOtherZero {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q)
    (hnot : ¬ bankTrialLocalTerminal z)
    (hclass : bankTrialDurationClass z = 2) :
    bankTrialDurationWorkerRemaining z = 0 ∧
    ∀ e : Fin n,
      bankTrialDurationWorkerRemaining
        (bankTrialLocalNext ring root z e) = 0 := by
  cases z with
  | mk B phase =>
      cases phase with
      | live begun =>
          change (if (B.fields ⟨0, by omega⟩).1 = .ARMED
            then 0 else 1) = 2 at hclass
          split at hclass <;> omega
      | recovery =>
          exact ⟨rfl,
            fun e => bankTrialDurationWorkerRemainingRecoveryNextZero
              ring root e B⟩
      | won => exact False.elim (hnot (Or.inl rfl))
      | lost => exact False.elim (hnot (Or.inr rfl))

theorem bankTrialDurationWorkerRemainingClassZero {q : Nat}
    (z : BankTrialLocalState q)
    (hclass : bankTrialDurationClass z = 0) :
    bankTrialDurationWorkerRemaining z = 0 := by
  cases z with
  | mk B phase =>
      cases phase with
      | live begun =>
          by_cases hm : bankTrialLiveWaveRootMode B = .ARMED
          · exact bankTrialDurationWorkerRemainingArmed B begun hm
          · have heq :
                (if bankTrialLiveWaveRootMode B = .ARMED
                  then 0 else 1) = 0 := hclass
            rw [if_neg hm] at heq
            omega
      | recovery =>
          change (2 : Nat) = 0 at hclass
          omega
      | won =>
          change (2 : Nat) = 0 at hclass
          omega
      | lost =>
          change (2 : Nat) = 0 at hclass
          omega

/-- The elementary finite-n edge accounting: nonincrease
everywhere plus a strict nominated edge pays one unit. -/
private theorem bankTrialDurationWorkerNominatedSum
    {n : Nat} (rank : Fin n → Nat) (current : Nat)
    (hmono : ∀ e, rank e ≤ current)
    (hdrop : ∃ e, rank e + 1 ≤ current) :
    1 + (List.ofFn rank).sum ≤ n * current := by
  rcases hdrop with ⟨chosen, hchosen⟩
  have hpoint :
      ∀ e : Fin n,
        rank e + (if e = chosen then 1 else 0) ≤ current := by
    intro e
    by_cases he : e = chosen
    · subst e
      rw [if_pos rfl]
      exact hchosen
    · simpa only [if_neg he, Nat.add_zero] using hmono e
  have hsum := ofFn_sum_le
    (fun e : Fin n => rank e +
      (if e = chosen then 1 else 0))
    (fun _ : Fin n => current)
    hpoint
  rw [ofFn_sum_add,
    bankTrialDurationHeadSpikeSum n chosen 1,
    ofFn_sum_const] at hsum
  omega

/-- The FIRST MISSING physical owner-row certificate.
At ARMED only the outgoing HEAD may refill worker rank.
At a LIVE class-1 state every original scheduler edge
must weakly decrease the rank, and one nominated actual edge
must strictly decrease it. This includes workerless waits
and short-ring aliasing, not just independent two-slot patches.

The interior patch frame lemmas (BankTrialProbability
3974--4017) do not prove this all-n statement. The source's
four interior certificate components at 4159--4207 are still
open. A high-lease workerless IWAIT/CWAIT snapshot may violate
the clipped-rank progress; it must be proved unreachable
from CLEAN or handled by a stronger rank/exit argument. -/
def BankTrialDurationWorkerRankEdgeRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ S : GrantBankReference.BankLocalReference
      (compileAdvice q).b,
    BankTrialLocalClean q S →
    ∀ z : BankTrialLocalState q,
      BankTrialDurationReachable ring root S z →
      ¬ bankTrialLocalTerminal z →
      (bankTrialDurationClass z = 0 →
        ∀ e : Fin n, e ≠ root →
          bankTrialDurationWorkerRemaining
            (bankTrialLocalNext ring root z e) = 0) ∧
      (bankTrialDurationClass z = 1 →
        (∀ e : Fin n,
          bankTrialDurationWorkerRemaining
            (bankTrialLocalNext ring root z e) ≤
              bankTrialDurationWorkerRemaining z) ∧
        ∃ chosen : Fin n,
          bankTrialDurationWorkerRemaining
            (bankTrialLocalNext ring root z chosen) + 1 ≤
              bankTrialDurationWorkerRemaining z)

/-- Conditional but complete rank-level drift: class 0 has
at most one possible refill, class 1 pays via a nominated edge,
and class 2 is discharged by the actual recovery observer. -/
theorem bankTrialDurationWorkerRankDriftOfEdges {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hrows : BankTrialDurationWorkerRankEdgeRows (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (z : BankTrialLocalState q)
    (hreach : BankTrialDurationReachable ring root S z)
    (hnot : ¬ bankTrialLocalTerminal z) :
    (if bankTrialDurationClass z = 1 then 1 else 0) +
      (List.ofFn (fun e : Fin n =>
        bankTrialDurationWorkerRemaining
          (bankTrialLocalNext ring root z e))).sum ≤
    n * bankTrialDurationWorkerRemaining z +
      bankTrialDurationWorkerLimit q *
        (if bankTrialDurationClass z = 0 then 1 else 0) := by
  have hcases := hrows S hclean z hreach hnot
  by_cases hzero : bankTrialDurationClass z = 0
  · have hone : bankTrialDurationClass z ≠ 1 := by omega
    have hbefore := bankTrialDurationWorkerRemainingClassZero z hzero
    have hzeroOthers := hcases.1 hzero
    have hsum :
        (List.ofFn (fun e : Fin n =>
          bankTrialDurationWorkerRemaining
            (bankTrialLocalNext ring root z e))).sum =
        bankTrialDurationWorkerRemaining
          (bankTrialLocalNext ring root z root) := by
      have heq := ofFn_sum_eq
        (fun e : Fin n =>
          bankTrialDurationWorkerRemaining
            (bankTrialLocalNext ring root z e))
        (fun e : Fin n =>
          if e = root then
            bankTrialDurationWorkerRemaining
              (bankTrialLocalNext ring root z root)
          else 0)
        (fun e => by
          by_cases he : e = root
          · subst e
            rw [if_pos rfl]
          · rw [if_neg he, hzeroOthers e he])
      rw [heq]
      exact bankTrialDurationHeadSpikeSum n root _
    calc
      (if bankTrialDurationClass z = 1 then 1 else 0) +
          (List.ofFn (fun e : Fin n =>
            bankTrialDurationWorkerRemaining
              (bankTrialLocalNext ring root z e))).sum =
        bankTrialDurationWorkerRemaining
          (bankTrialLocalNext ring root z root) := by
            rw [if_neg hone, Nat.zero_add, hsum]
      _ ≤ bankTrialDurationWorkerLimit q :=
        bankTrialDurationWorkerRemainingCap
          (bankTrialLocalNext ring root z root)
      _ = n * bankTrialDurationWorkerRemaining z +
          bankTrialDurationWorkerLimit q *
            (if bankTrialDurationClass z = 0 then 1 else 0) := by
            rw [hbefore, if_pos hzero]
            simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one]
  · by_cases hone : bankTrialDurationClass z = 1
    · have hmono := (hcases.2 hone).1
      have hdrop := (hcases.2 hone).2
      have hpay := bankTrialDurationWorkerNominatedSum
        (fun e : Fin n =>
          bankTrialDurationWorkerRemaining
            (bankTrialLocalNext ring root z e))
        (bankTrialDurationWorkerRemaining z)
        hmono hdrop
      calc
        (if bankTrialDurationClass z = 1 then 1 else 0) +
            (List.ofFn (fun e : Fin n =>
              bankTrialDurationWorkerRemaining
                (bankTrialLocalNext ring root z e))).sum =
          1 + (List.ofFn (fun e : Fin n =>
              bankTrialDurationWorkerRemaining
                (bankTrialLocalNext ring root z e))).sum := by
              rw [if_pos hone]
        _ ≤ n * bankTrialDurationWorkerRemaining z := hpay
        _ = n * bankTrialDurationWorkerRemaining z +
            bankTrialDurationWorkerLimit q *
              (if bankTrialDurationClass z = 0 then 1 else 0) := by
              rw [if_neg hzero]
              simp only [Nat.mul_zero, Nat.add_zero]
    · have htwo : bankTrialDurationClass z = 2 := by
        have hle := bankTrialDurationClassLe z
        omega
      obtain ⟨hcurrent, hnext⟩ :=
        bankTrialDurationWorkerRemainingOtherZero ring root z
          hnot htwo
      have hsum :
          (List.ofFn (fun e : Fin n =>
            bankTrialDurationWorkerRemaining
              (bankTrialLocalNext ring root z e))).sum = 0 := by
        have heq := ofFn_sum_eq
          (fun e : Fin n =>
            bankTrialDurationWorkerRemaining
              (bankTrialLocalNext ring root z e))
          (fun _ : Fin n => 0)
          hnext
        rw [heq, ofFn_sum_const]
        exact Nat.mul_zero n
      rw [if_neg hone, if_neg hzero, hsum, hcurrent]
      simp only [Nat.zero_add, Nat.mul_zero, Nat.add_zero]
      exact Nat.le_refl _

theorem bankTrialDurationWorkerPotentialDriftOfEdges {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hrows : BankTrialDurationWorkerRankEdgeRows (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (z : BankTrialLocalState q)
    (hreach : BankTrialDurationReachable ring root S z)
    (hnot : ¬ bankTrialLocalTerminal z) :
    n * (if bankTrialDurationClass z = 1 then 1 else 0) +
      (List.ofFn (fun e : Fin n =>
        bankTrialDurationWorkerRankPotential n
          (bankTrialLocalNext ring root z e))).sum ≤
    n * bankTrialDurationWorkerRankPotential n z +
      (bankTrialDurationWorkerLimit q * n) *
        (if bankTrialDurationClass z = 0 then 1 else 0) := by
  have hraw :=
    bankTrialDurationWorkerRankDriftOfEdges
      ring root hrows S hclean z hreach hnot
  have hscaled := Nat.mul_le_mul_left n hraw
  unfold bankTrialDurationWorkerRankPotential
  calc
    n * (if bankTrialDurationClass z = 1 then 1 else 0) +
        (List.ofFn (fun e : Fin n =>
          n * bankTrialDurationWorkerRemaining
            (bankTrialLocalNext ring root z e))).sum =
      n * ((if bankTrialDurationClass z = 1 then 1 else 0) +
        (List.ofFn (fun e : Fin n =>
          bankTrialDurationWorkerRemaining
            (bankTrialLocalNext ring root z e))).sum) := by
          rw [ofFn_sum_mul_left, Nat.mul_add]
    _ ≤ n * (n * bankTrialDurationWorkerRemaining z +
          bankTrialDurationWorkerLimit q *
            (if bankTrialDurationClass z = 0 then 1 else 0)) := hscaled
    _ = n * (n * bankTrialDurationWorkerRemaining z) +
          (bankTrialDurationWorkerLimit q * n) *
            (if bankTrialDurationClass z = 0 then 1 else 0) := by
          simp only [Nat.mul_add]
          ac_rfl

/-- This produces exactly the earlier requested Prop IF the
single remaining true-process source row certificate is proved.
The existence of the potential, its initial zero, and uniform
cap are unconditional facts above. -/
theorem bankTrialDurationWorkerHeadAmortizedRowsOfRankEdges
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hrows : BankTrialDurationWorkerRankEdgeRows (q := q) ring root) :
    BankTrialDurationWorkerHeadAmortizedRows (q := q) ring root := by
  intro S hclean
  refine ⟨bankTrialDurationWorkerRankPotential n,
    ?_, ?_, ?_⟩
  · exact bankTrialDurationWorkerPotentialClean n S hclean
  · intro z _
    change bankTrialDurationWorkerRankPotential n z ≤
      bankTrialDurationWorkerLimit q * n
    exact bankTrialDurationWorkerRankPotentialCap n z
  · intro z hz hnot
    change n * (if bankTrialDurationClass z = 1 then 1 else 0) +
        (List.ofFn (fun e : Fin n =>
          bankTrialDurationWorkerRankPotential n
            (bankTrialLocalNext ring root z e))).sum ≤
      n * bankTrialDurationWorkerRankPotential n z +
        (bankTrialDurationWorkerLimit q * n) *
          (if bankTrialDurationClass z = 0 then 1 else 0)
    exact bankTrialDurationWorkerPotentialDriftOfEdges
      ring root hrows S hclean z hz hnot

theorem bankTrialDurationWorkerBudgetOfRankEdges {n q : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (hrows : BankTrialDurationWorkerRankEdgeRows (q := q) ring root) :
    BankTrialDurationWorkerBudget (q := q) ring root := by
  exact bankTrialDurationWorkerBudgetDistinctPortsOfHeadRows
    ring hn root
    (bankTrialDurationWorkerHeadAmortizedRowsOfRankEdges
      ring root hrows)

end L3



/-!
Source-owned worker-row rank calculations and lease-orphan
accounting audit.

IMPORTANT: the live-wave stage certificate has a uniqueness
clause, but does not assert existence of a worker. Its chronological
transfer is conditional on the four window row classes. Likewise,
the numeric carry/threshold ledger and comparator-credit obligations
remain open in BankTrialProbability. Do NOT infer a CLEAN-reachable
no-orphan theorem from the palette alone.

The following corrected interface assigns an orphan LIVE IWAIT/CWAIT
to reset/recovery time (class 2), rather than pretending that a
clipped worker rank can pay a large lease. This is an accounting
definition, NOT a proof of the original (2L+2)n recovery budget.
The genuine interior IR/AL and CR/CL pair rows below are proved
independently of a global reachable-state theorem.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- An old IR really is destroyed by the physical top boundary.
This is the source of the orphan-wait audit, not a new reset. -/
theorem bankTrialDurationTopBoundaryEraseIR
    (x : BankCell) (ht : x.tok = .IR) :
    (GrantBankReference.topBoundaryBankMap x).tok = .E := by
  simp [GrantBankReference.topBoundaryBankMap, ht]

/-- A nonterminal incoming-root service is not an immediate
escape from IWAIT/CWAIT when its old lease exceeds one. -/
theorem bankTrialDurationIncomingWaitNoExit
    (x : BankCell)
    (hm : x.mode = .IWAIT ∨ x.mode = .CWAIT)
    (hl : 1 < x.lease) :
    (GrantBankReference.incomingRootBankMap x).mode = x.mode ∧
    (GrantBankReference.incomingRootBankMap x).lease =
      x.lease - 1 := by
  rcases hm with hi | hc
  · simp [GrantBankReference.incomingRootBankMap,
      hi, hl, isWaitMode]
  · simp [GrantBankReference.incomingRootBankMap,
      hc, hl, isWaitMode]

/-- The literal outgoing-root pair also spends rather than exits
a workerless IWAIT/CWAIT; no return-token arm can fire. -/
theorem bankTrialDurationOutgoingWaitNoReturn
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 < b)
    (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false)
    (hm : x.mode = .IWAIT ∨ x.mode = .CWAIT)
    (he : y.tok = .E)
    (hl : 1 < x.lease) :
    (bankPair x y 1 b theta).1.mode = x.mode ∧
    (bankPair x y 1 b theta).1.lease = x.lease - 1 := by
  have hn : b ≠ 1 := by omega
  rcases hm with hi | hc
  · simp [bankPair, hx, hy, hg, hi, he, hl,
      hb, hn, isRetTok, isWaitMode,
      Id.run_pure, Id.run_bind]
  · simp [bankPair, hx, hy, hg, hc, he, hl,
      hb, hn, isRetTok, isWaitMode,
      Id.run_pure, Id.run_bind]

/-- A clipped lease has no strict one-step decrease while the
old lease is at least one above the clipping threshold. -/
theorem bankTrialDurationWorkerLeasePlateau
    (q lease : Nat)
    (hl : bankTrialDurationWorkerLimit q + 1 ≤ lease) :
    Nat.min (bankTrialDurationWorkerLimit q) lease =
      Nat.min (bankTrialDurationWorkerLimit q) (lease - 1) := by
  have hleft : bankTrialDurationWorkerLimit q ≤ lease := by omega
  have hright :
      bankTrialDurationWorkerLimit q ≤ lease - 1 := by omega
  exact (Nat.min_eq_left hleft).trans (Nat.min_eq_left hright).symm

/-- The budget-safe classification must distinguish an orphan
LIVE wait from a LIVE wave carrying an actual worker. Class 2
is the reset/recovery charge; its numerical bound needs a
NEW pre-RESET lease argument if orphans can really occur. -/
def bankTrialDurationLeaseAwareClass {q : Nat}
    (z : BankTrialLocalState q) : Nat :=
  match z.phase with
  | .live _ =>
      if bankTrialLiveWaveRootMode z.bank = .ARMED then 0
      else if
          (bankTrialLiveWaveRootMode z.bank = .IWAIT ∨
           bankTrialLiveWaveRootMode z.bank = .CWAIT) ∧
          bankTrialDurationWorkerTokenMaximum z.bank = 0
      then 2 else 1
  | .recovery => 2
  | .won => 2
  | .lost => 2

/-- Worker-time potential does not pay for a pre-RESET orphan
wait. That clock is assigned to the recovery account. -/
def bankTrialDurationLeaseAwareWorkerRemaining {q : Nat}
    (z : BankTrialLocalState q) : Nat :=
  if bankTrialDurationLeaseAwareClass z = 2 then 0
  else bankTrialDurationWorkerRemaining z

theorem bankTrialDurationLeaseAwareOrphanClass {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (he : bankTrialDurationWorkerTokenMaximum B = 0) :
    bankTrialDurationLeaseAwareClass
      (⟨B, .live begun⟩ : BankTrialLocalState q) = 2 := by
  have hn : bankTrialLiveWaveRootMode B ≠ .ARMED := by
    intro ha
    rcases hm with hi | hc
    · rw [ha] at hi
      cases hi
    · rw [ha] at hc
      cases hc
  change (if bankTrialLiveWaveRootMode B = .ARMED then 0
    else if
      ((bankTrialLiveWaveRootMode B = .IWAIT ∨
        bankTrialLiveWaveRootMode B = .CWAIT) ∧
       bankTrialDurationWorkerTokenMaximum B = 0)
      then 2 else 1) = 2
  rw [if_neg hn, if_pos (And.intro hm he)]

theorem bankTrialDurationLeaseAwareOrphanRemainingZero {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (he : bankTrialDurationWorkerTokenMaximum B = 0) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) = 0 := by
  unfold bankTrialDurationLeaseAwareWorkerRemaining
  rw [bankTrialDurationLeaseAwareOrphanClass B begun hm he]
  rfl

/-- Corrected ORIGINAL-clock row obligation. Class 2 now also
includes workerless LIVE waits and must have its own recovery
occupation bound. The declaration is intentionally a Prop:
neither the no-orphan invariant nor the stronger C.2 transfer
is available as a theorem. -/
def BankTrialDurationLeaseAwareWorkerRankEdgeRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ S : GrantBankReference.BankLocalReference
      (compileAdvice q).b,
    BankTrialLocalClean q S →
    ∀ z : BankTrialLocalState q,
      BankTrialDurationReachable ring root S z →
      ¬ bankTrialLocalTerminal z →
      (bankTrialDurationLeaseAwareClass z = 0 →
        ∀ e : Fin n, e ≠ root →
          bankTrialDurationLeaseAwareWorkerRemaining
            (bankTrialLocalNext ring root z e) = 0) ∧
      (bankTrialDurationLeaseAwareClass z = 1 →
        (∀ e : Fin n,
          bankTrialDurationLeaseAwareWorkerRemaining
            (bankTrialLocalNext ring root z e) ≤
              bankTrialDurationLeaseAwareWorkerRemaining z) ∧
        ∃ chosen : Fin n,
          bankTrialDurationLeaseAwareWorkerRemaining
            (bankTrialLocalNext ring root z chosen) + 1 ≤
              bankTrialDurationLeaseAwareWorkerRemaining z) ∧
      (bankTrialDurationLeaseAwareClass z = 2 →
        ∀ e : Fin n,
          bankTrialDurationLeaseAwareWorkerRemaining
            (bankTrialLocalNext ring root z e) = 0)

/-- G11 gives exactly these three IWAIT token alternatives,
not the existence of a nonempty token. -/
theorem bankTrialDurationIWaitTokenCases {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT)
    (j : Fin (compileAdvice q).b) :
    bankTrialLiveWaveToken B j = .E ∨
      bankTrialLiveWaveToken B j = .IR ∨
      bankTrialLiveWaveToken B j = .AL :=
  hc.iwaitTokens j hm

/-- G11's CWAIT palette, split on the actual worker token. -/
theorem bankTrialDurationCWaitTokenCases {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .CWAIT)
    (j : Fin (compileAdvice q).b) :
    bankTrialLiveWaveToken B j = .E ∨
      bankTrialLiveWaveToken B j = .CR0 ∨
      bankTrialLiveWaveToken B j = .CR1 ∨
      bankTrialLiveWaveToken B j = .CL0 ∨
      bankTrialLiveWaveToken B j = .CL1 := by
  rcases hc.cwaitTokens j hm with he | hcomp
  · exact Or.inl he
  · rcases hcomp with ht | ht | ht | ht
    · exact Or.inr (Or.inl ht)
    · exact Or.inr (Or.inr (Or.inl ht))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ht)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ht)))

/-- IR travels to a successor carrying IR or AL and pays one
service of the token rank. This uses the exact owner row. -/
theorem bankTrialDurationIRInteriorOwnerRank
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hir : x.tok = .IR) (he : y.tok = .E) :
    (bankPair x y y.role b theta).1.tok = .E ∧
    (bankPair x y y.role b theta).2.tok =
      (if y.bit then .IR else .AL) ∧
    bankTrialDurationWorkerTokenRank b y.role
        (bankPair x y y.role b theta).2.tok + 1 ≤
      bankTrialDurationWorkerTokenRank b x.role .IR := by
  have hr := bankTrialInteriorIRForward
    b theta x y hx hlt hy hir he
  refine ⟨hr.1, hr.2.1, ?_⟩
  rw [hr.2.1, hy]
  cases hbit : y.bit <;>
    simp [hbit, bankTrialDurationWorkerTokenRank] <;> omega

/-- AL returns one digit toward the root, preserves both bits,
and pays at least one unit of its owner rank. -/
theorem bankTrialDurationALInteriorOwnerRank
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (he : x.tok = .E) (hal : y.tok = .AL) :
    (bankPair x y y.role b theta).1.tok = .AL ∧
    (bankPair x y y.role b theta).2.tok = .E ∧
    bankTrialDurationWorkerTokenRank b x.role
        (bankPair x y y.role b theta).1.tok + 1 ≤
      bankTrialDurationWorkerTokenRank b y.role .AL := by
  have hr := bankTrialInteriorALReturn
    b theta x y hx hlt hy he hal
  refine ⟨hr.1, hr.2.2.1, ?_⟩
  rw [hr.1]
  simp only [bankTrialDurationWorkerTokenRank]
  omega

/-- A forward comparison is CR0 or CR1, with identical rank
in either branch. G11's raw CR1 row supplies the equality test. -/
theorem bankTrialDurationCRInteriorOwnerRank
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hcr : x.tok = .CR0 ∨ x.tok = .CR1)
    (he : y.tok = .E) :
    (bankPair x y y.role b theta).1.tok = .E ∧
    ((bankPair x y y.role b theta).2.tok = .CR0 ∨
      (bankPair x y y.role b theta).2.tok = .CR1) ∧
    bankTrialDurationWorkerTokenRank b y.role
        (bankPair x y y.role b theta).2.tok + 1 ≤
      bankTrialDurationWorkerTokenRank b x.role .CR0 := by
  rcases hcr with hzero | hone
  · have hr := bankTrialInteriorCRZeroForward
      b theta x y hx hlt hy hzero he
    refine ⟨hr.1, Or.inl hr.2.2.1, ?_⟩
    rw [hr.2.2.1]
    simp only [bankTrialDurationWorkerTokenRank]
    omega
  · have hr := bankTrialLiveRawCRForward
      b theta x y hx hlt hy hone he
    refine ⟨hr.1, ?_, ?_⟩
    · rw [hr.2.1]
      cases hb : (y.bit == theta (y.role - 1)) <;>
        simp [hb]
    · rw [hr.2.1]
      cases hb : (y.bit == theta (y.role - 1)) <;>
        simp [hb, bankTrialDurationWorkerTokenRank] <;> omega

/-- A CL0/CL1 answer returns one digit and pays one unit of
the identical numeric rank. No bit-write case is introduced. -/
theorem bankTrialDurationCLInteriorOwnerRank
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (he : x.tok = .E)
    (hcl : y.tok = .CL0 ∨ y.tok = .CL1) :
    ((bankPair x y y.role b theta).1.tok = .CL0 ∨
      (bankPair x y y.role b theta).1.tok = .CL1) ∧
    (bankPair x y y.role b theta).2.tok = .E ∧
    bankTrialDurationWorkerTokenRank b x.role
        (bankPair x y y.role b theta).1.tok + 1 ≤
      bankTrialDurationWorkerTokenRank b y.role .CL0 := by
  rcases hcl with hzero | hone
  · have hr := bankTrialInteriorCLZeroReturn
      b theta x y hx hlt hy he hzero
    refine ⟨Or.inl hr.1, hr.2.2.1, ?_⟩
    rw [hr.1]
    simp only [bankTrialDurationWorkerTokenRank]
    omega
  · have hr := bankTrialLiveRawCLReturn
      b theta x y hx hlt hy he hone
    refine ⟨Or.inr hr.1, hr.2.1, ?_⟩
    rw [hr.1]
    simp only [bankTrialDurationWorkerTokenRank]
    omega

/-- The field/token frame protects the rank of every
digit outside the selected two-slot interior owner. -/
theorem bankTrialDurationInteriorOutsideRankFrame {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j k : Fin (compileAdvice q).b)
    (hj : 0 < j.val)
    (hs : k.val + 1 ≠ j.val)
    (ht : k.val + 1 ≠ j.val + 1) :
    bankTrialLiveWaveRootMode
        (bankTrialWindowInteriorPatch B j) =
      bankTrialLiveWaveRootMode B ∧
    bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (k.val + 1)
        (bankTrialLiveWaveToken
          (bankTrialWindowInteriorPatch B j) k) =
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (k.val + 1) (bankTrialLiveWaveToken B k) := by
  constructor
  · exact bankTrialInteriorPatchRootMode B j hj
  · exact congrArg
      (fun t : BTok =>
        bankTrialDurationWorkerTokenRank (compileAdvice q).b
          (k.val + 1) t)
      (bankTrialInteriorPatchTokenFrame B j k hs ht)

/-- Four corrected owner-level rank rows, not an assertion that
every reachable ORIGINAL scheduler edge has a nominated drop.
The latter still requires no-orphan/counting and nonalias facts. -/
theorem bankTrialDurationWorkerInteriorOwnerRanks
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1) :
    (x.tok = .IR → y.tok = .E →
      bankTrialDurationWorkerTokenRank b y.role
        (bankPair x y y.role b theta).2.tok + 1 ≤
      bankTrialDurationWorkerTokenRank b x.role .IR) ∧
    (x.tok = .E → y.tok = .AL →
      bankTrialDurationWorkerTokenRank b x.role
        (bankPair x y y.role b theta).1.tok + 1 ≤
      bankTrialDurationWorkerTokenRank b y.role .AL) ∧
    ((x.tok = .CR0 ∨ x.tok = .CR1) → y.tok = .E →
      bankTrialDurationWorkerTokenRank b y.role
        (bankPair x y y.role b theta).2.tok + 1 ≤
      bankTrialDurationWorkerTokenRank b x.role .CR0) ∧
    (x.tok = .E → (y.tok = .CL0 ∨ y.tok = .CL1) →
      bankTrialDurationWorkerTokenRank b x.role
        (bankPair x y y.role b theta).1.tok + 1 ≤
      bankTrialDurationWorkerTokenRank b y.role .CL0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hir he
    exact (bankTrialDurationIRInteriorOwnerRank
      b theta x y hx hlt hy hir he).2.2
  · intro he hal
    exact (bankTrialDurationALInteriorOwnerRank
      b theta x y hx hlt hy he hal).2.2
  · intro hcr he
    exact (bankTrialDurationCRInteriorOwnerRank
      b theta x y hx hlt hy hcr he).2.2
  · intro he hcl
    exact (bankTrialDurationCLInteriorOwnerRank
      b theta x y hx hlt hy he hcl).2.2

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A zero original worker rank is also zero after lease-aware
classification, independently of the current observer phase. -/
private theorem bankTrialDurationLeaseAwareOfRawZero {q : Nat}
    (z : BankTrialLocalState q)
    (hz : bankTrialDurationWorkerRemaining z = 0) :
    bankTrialDurationLeaseAwareWorkerRemaining z = 0 := by
  unfold bankTrialDurationLeaseAwareWorkerRemaining
  split
  · rfl
  · exact hz

/-- In any observer phase, an ARMED root has zero lease-aware
worker rank. No reachability, spatial nonalias or no-wrap is used. -/
theorem bankTrialDurationLeaseAwareArmedRankZero {q : Nat}
    (z : BankTrialLocalState q)
    (hm : bankTrialLiveWaveRootMode z.bank = .ARMED) :
    bankTrialDurationLeaseAwareWorkerRemaining z = 0 := by
  cases z with
  | mk B phase =>
      cases phase with
      | live begun =>
          exact bankTrialDurationLeaseAwareOfRawZero
            (⟨B, .live begun⟩ : BankTrialLocalState q)
            (bankTrialDurationWorkerRemainingArmed B begun hm)
      | recovery => rfl
      | won => rfl
      | lost => rfl

/-- The entire class-zero nonroot clause on the actual
CLEAN-reachable observer. An incoming-root nonroot edge enters
RECOVERY; all other nonroot edges frame the old ARMED root.
This proof does not require window nonalias or a carry no-wrap
invariant. -/
theorem bankTrialDurationLeaseAwareClassZeroNonroot {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (z : BankTrialLocalState q)
    (hreach : BankTrialDurationReachable ring root S z)
    (hclass : bankTrialDurationLeaseAwareClass z = 0)
    (e : Fin n) (hne : e ≠ root) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (bankTrialLocalNext ring root z e) = 0 := by
  cases z with
  | mk B phase =>
      cases phase with
      | live begun =>
          have hm : bankTrialLiveWaveRootMode B = .ARMED := by
            by_cases ha : bankTrialLiveWaveRootMode B = .ARMED
            · exact ha
            · change
                (if bankTrialLiveWaveRootMode B = .ARMED then 0
                 else if
                   ((bankTrialLiveWaveRootMode B = .IWAIT ∨
                     bankTrialLiveWaveRootMode B = .CWAIT) ∧
                    bankTrialDurationWorkerTokenMaximum B = 0)
                 then 2 else 1) = 0 at hclass
              rw [if_neg ha] at hclass
              split at hclass <;> omega
          obtain ⟨word, hword⟩ := hreach
          have hf : B.success = false :=
            bankTrialProbabilityCleanLiveUnlatched
              ring root S hclean word B begun hword
          by_cases hin : ring.rightNeighbor e = root
          · rw [bankTrialProbabilityIncomingArmedEntersRecovery
              ring root e B begun hf hm hne hin]
            rfl
          · have hframe := bankTrialLocalRootNonincidentFrame
              ring root e B hf hne hin
            have hnextMode :
                bankTrialLiveWaveRootMode
                  (bankTrialLocalNext ring root
                    (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank =
                  .ARMED := by
              change
                ((bankTrialLocalNext ring root
                  (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank.fields
                  ⟨0, by omega⟩).1 = .ARMED
              rw [bankTrialLocalNextLiveBank]
              rw [hframe]
              exact hm
            exact bankTrialDurationLeaseAwareArmedRankZero
              (bankTrialLocalNext ring root
                (⟨B, .live begun⟩ : BankTrialLocalState q) e)
              hnextMode
      | recovery =>
          change (2 : Nat) = 0 at hclass
          omega
      | won =>
          change (2 : Nat) = 0 at hclass
          omega
      | lost =>
          change (2 : Nat) = 0 at hclass
          omega

/-- All RECOVERY successors have zero lease-aware worker rank.
This is a complete part of the class-two row, including WON/LOST
successors and every physical scheduler edge. -/
theorem bankTrialDurationLeaseAwareRecoveryEdgeZero {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (bankTrialLocalNext ring root
        (⟨B, .recovery⟩ : BankTrialLocalState q) e) = 0 := by
  exact bankTrialDurationLeaseAwareOfRawZero
    (bankTrialLocalNext ring root
      (⟨B, .recovery⟩ : BankTrialLocalState q) e)
    (bankTrialDurationWorkerRemainingRecoveryNextZero
      ring root e B)

/-- Terminal successors are zero as well; this lemma is useful
outside the preterminal row specification. -/
theorem bankTrialDurationLeaseAwareTerminalEdgeZero {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialLocalState q)
    (ht : bankTrialLocalTerminal z) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (bankTrialLocalNext ring root z e) = 0 := by
  rw [bankTrialLocalTerminalAbsorbs ring root e z ht]
  exact bankTrialDurationLeaseAwareOfRawZero z
    (bankTrialDurationWorkerRemainingTerminal z ht)

/-- A nonterminal lease-aware class-two state is either already
RECOVERY or an actual LIVE IWAIT/CWAIT with no worker token.
This isolates the only class-two transition family still open. -/
theorem bankTrialDurationLeaseAwareClassTwoCases {q : Nat}
    (z : BankTrialLocalState q)
    (hnot : ¬ bankTrialLocalTerminal z)
    (hclass : bankTrialDurationLeaseAwareClass z = 2) :
    (∃ B : GrantBankReference.BankLocalReference
        (compileAdvice q).b,
        z = ⟨B, .recovery⟩) ∨
    (∃ (B : GrantBankReference.BankLocalReference
        (compileAdvice q).b) (begun : Bool),
        z = ⟨B, .live begun⟩ ∧
        (bankTrialLiveWaveRootMode B = .IWAIT ∨
         bankTrialLiveWaveRootMode B = .CWAIT) ∧
        bankTrialDurationWorkerTokenMaximum B = 0) := by
  cases z with
  | mk B phase =>
      cases phase with
      | live begun =>
          have hn : bankTrialLiveWaveRootMode B ≠ .ARMED := by
            intro ha
            change
              (if bankTrialLiveWaveRootMode B = .ARMED then 0
               else if
                 ((bankTrialLiveWaveRootMode B = .IWAIT ∨
                   bankTrialLiveWaveRootMode B = .CWAIT) ∧
                  bankTrialDurationWorkerTokenMaximum B = 0)
               then 2 else 1) = 2 at hclass
            rw [if_pos ha] at hclass
            omega
          have horphan :
              (bankTrialLiveWaveRootMode B = .IWAIT ∨
                bankTrialLiveWaveRootMode B = .CWAIT) ∧
              bankTrialDurationWorkerTokenMaximum B = 0 := by
            change
              (if bankTrialLiveWaveRootMode B = .ARMED then 0
               else if
                 ((bankTrialLiveWaveRootMode B = .IWAIT ∨
                   bankTrialLiveWaveRootMode B = .CWAIT) ∧
                  bankTrialDurationWorkerTokenMaximum B = 0)
               then 2 else 1) = 2 at hclass
            rw [if_neg hn] at hclass
            by_cases ho :
                (bankTrialLiveWaveRootMode B = .IWAIT ∨
                  bankTrialLiveWaveRootMode B = .CWAIT) ∧
                bankTrialDurationWorkerTokenMaximum B = 0
            · exact ho
            · rw [if_neg ho] at hclass
              omega
          exact Or.inr ⟨B, begun, rfl, horphan.1, horphan.2⟩
      | recovery =>
          exact Or.inl ⟨B, rfl⟩
      | won =>
          exact False.elim (hnot (Or.inl rfl))
      | lost =>
          exact False.elim (hnot (Or.inr rfl))

/-- A selected IR forward edge strictly decreases the touched
token service rank, on the true clamped BANK reference. -/
theorem bankTrialDurationSelectedIRTokenRank {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .IR)
    (hdst : (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .E) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val, by omega⟩).2.2.1 = .E ∧
    bankTrialDurationWorkerTokenRank (compileAdvice q).b (j.val + 1)
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val)).fields
          ⟨j.val + 1, by omega⟩).2.2.1 + 1 ≤
      bankTrialDurationWorkerTokenRank (compileAdvice q).b j.val .IR := by
  have hr := bankTrialDurationIRInteriorOwnerRank
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by omega⟩)
    (by change 1 ≤ j.val; omega) j.isLt (by rfl)
    hsrc hdst
  constructor
  · rw [bankTrialWindowInteriorSource ring root B hf j]
    rw [(bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).1)).2]
    exact hr.1
  · rw [bankTrialWindowInteriorResponder ring root hw B hf j]
    rw [(bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).2)).2]
    exact hr.2.2

/-- A selected AL reverse edge strictly decreases the touched
token service rank, with a framed empty destination. -/
theorem bankTrialDurationSelectedALTokenRank {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .E)
    (hdst : (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .AL) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val + 1, by omega⟩).2.2.1 = .E ∧
    bankTrialDurationWorkerTokenRank (compileAdvice q).b j.val
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val)).fields
          ⟨j.val, by omega⟩).2.2.1 + 1 ≤
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (j.val + 1) .AL := by
  have hr := bankTrialDurationALInteriorOwnerRank
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by omega⟩)
    (by change 1 ≤ j.val; omega) j.isLt (by rfl)
    hsrc hdst
  constructor
  · rw [bankTrialWindowInteriorResponder ring root hw B hf j]
    rw [(bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).2)).2]
    exact hr.2.1
  · rw [bankTrialWindowInteriorSource ring root B hf j]
    rw [(bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).1)).2]
    exact hr.2.2

/-- The selected CR0/CR1 forward service pays one unit on
the true clamped reference, including the comparison-bit test. -/
theorem bankTrialDurationSelectedCRTokenRank {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .CR0 ∨
      (B.fields ⟨j.val, by omega⟩).2.2.1 = .CR1)
    (hdst : (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .E) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val, by omega⟩).2.2.1 = .E ∧
    bankTrialDurationWorkerTokenRank (compileAdvice q).b (j.val + 1)
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val)).fields
          ⟨j.val + 1, by omega⟩).2.2.1 + 1 ≤
      bankTrialDurationWorkerTokenRank (compileAdvice q).b j.val .CR0 := by
  have hr := bankTrialDurationCRInteriorOwnerRank
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by omega⟩)
    (by change 1 ≤ j.val; omega) j.isLt (by rfl)
    hsrc hdst
  constructor
  · rw [bankTrialWindowInteriorSource ring root B hf j]
    rw [(bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).1)).2]
    exact hr.1
  · rw [bankTrialWindowInteriorResponder ring root hw B hf j]
    rw [(bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).2)).2]
    exact hr.2.2

/-- The selected CL0/CL1 reverse service pays one unit on
the true clamped reference, with an empty destination. -/
theorem bankTrialDurationSelectedCLTokenRank {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .E)
    (hdst : (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .CL0 ∨
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .CL1) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val + 1, by omega⟩).2.2.1 = .E ∧
    bankTrialDurationWorkerTokenRank (compileAdvice q).b j.val
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val)).fields
          ⟨j.val, by omega⟩).2.2.1 + 1 ≤
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (j.val + 1) .CL0 := by
  have hr := bankTrialDurationCLInteriorOwnerRank
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by omega⟩)
    (by change 1 ≤ j.val; omega) j.isLt (by rfl)
    hsrc hdst
  constructor
  · rw [bankTrialWindowInteriorResponder ring root hw B hf j]
    rw [(bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).2)).2]
    exact hr.2.1
  · rw [bankTrialWindowInteriorSource ring root B hf j]
    rw [(bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).1)).2]
    exact hr.2.2

/-- All other digit token ranks frame on the SAME selected
original scheduler edge, not merely in a detached two-cell patch. -/
theorem bankTrialDurationSelectedInteriorOutsideRank {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (k : Fin (compileAdvice q).b)
    (hkleft : k.val + 1 ≠ j.val)
    (hkright : k.val + 1 ≠ j.val + 1) :
    bankTrialDurationWorkerTokenRank (compileAdvice q).b
      (k.val + 1)
      (bankTrialLiveWaveToken
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) k) =
    bankTrialDurationWorkerTokenRank (compileAdvice q).b
      (k.val + 1) (bankTrialLiveWaveToken B k) := by
  change bankTrialDurationWorkerTokenRank (compileAdvice q).b
      (k.val + 1)
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val)).fields
          ⟨k.val + 1, by omega⟩).2.2.1 =
    bankTrialDurationWorkerTokenRank (compileAdvice q).b
      (k.val + 1) (B.fields ⟨k.val + 1, by omega⟩).2.2.1
  rw [bankTrialWindowInteriorFrame
    ring root hw B hf j hj
    ⟨k.val + 1, by omega⟩ hkleft hkright]

/-- Arithmetic no-wrap at the actual compiled K, provided the
OLD pre-increment carry value is strictly below K. Proving that
word-level premise is a separate, still-open physical ledger task. -/
theorem bankTrialDurationNoWrapBelowThreshold
    (q value : Nat) (hq : 3 ≤ q)
    (hv : value < (compileAdvice q).K) :
    value + 1 < 2 ^ (compileAdvice q).b := by
  have hk := compileAdvice_K_lt_two_pow_b q hq
  omega

/-- The same no-wrap implication stated on the concrete protected
digit and in-flight-IR carry value, not an abstract counter. -/
theorem bankTrialDurationCarryNoWrapBelowThreshold {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hq : 3 ≤ q)
    (hcarry : bankTrialLiveCarryValue B < (compileAdvice q).K) :
    bankTrialLiveCarryValue B + 1 < 2 ^ (compileAdvice q).b := by
  exact bankTrialDurationNoWrapBelowThreshold q
    (bankTrialLiveCarryValue B) hq hcarry

/-- Full target reduction: class zero is discharged above and
the RECOVERY subcase of class two is discharged above. The two
remaining source obligations are class-one physical rank rows and
workerless LIVE wait nonbirth. This is conditional, not a claim
that those obligations have already been proved. -/
theorem bankTrialDurationLeaseAwareRowsOfWorkerAndOrphan
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hworker :
      ∀ (S : GrantBankReference.BankLocalReference
          (compileAdvice q).b),
        BankTrialLocalClean q S →
        ∀ z : BankTrialLocalState q,
          BankTrialDurationReachable ring root S z →
          ¬ bankTrialLocalTerminal z →
          bankTrialDurationLeaseAwareClass z = 1 →
          (∀ e : Fin n,
            bankTrialDurationLeaseAwareWorkerRemaining
              (bankTrialLocalNext ring root z e) ≤
                bankTrialDurationLeaseAwareWorkerRemaining z) ∧
          ∃ chosen : Fin n,
            bankTrialDurationLeaseAwareWorkerRemaining
              (bankTrialLocalNext ring root z chosen) + 1 ≤
                bankTrialDurationLeaseAwareWorkerRemaining z)
    (horphan :
      ∀ (S : GrantBankReference.BankLocalReference
          (compileAdvice q).b),
        BankTrialLocalClean q S →
        ∀ (B : GrantBankReference.BankLocalReference
            (compileAdvice q).b) (begun : Bool),
          BankTrialDurationReachable ring root S
            (⟨B, .live begun⟩ : BankTrialLocalState q) →
          (bankTrialLiveWaveRootMode B = .IWAIT ∨
            bankTrialLiveWaveRootMode B = .CWAIT) →
          bankTrialDurationWorkerTokenMaximum B = 0 →
          ∀ e : Fin n,
            bankTrialDurationLeaseAwareWorkerRemaining
              (bankTrialLocalNext ring root
                (⟨B, .live begun⟩ : BankTrialLocalState q) e) = 0) :
    BankTrialDurationLeaseAwareWorkerRankEdgeRows (q := q) ring root := by
  intro S hclean z hreach hnot
  refine ⟨?_, ?_, ?_⟩
  · intro hzero e hne
    exact bankTrialDurationLeaseAwareClassZeroNonroot
      ring root S hclean z hreach hzero e hne
  · intro hone
    exact hworker S hclean z hreach hnot hone
  · intro htwo e
    rcases bankTrialDurationLeaseAwareClassTwoCases z hnot htwo with
      ⟨B, hz⟩ | ⟨B, begun, hz, hm, he⟩
    · rw [hz]
      exact bankTrialDurationLeaseAwareRecoveryEdgeZero ring root e B
    · have hreach' : BankTrialDurationReachable ring root S
          (⟨B, .live begun⟩ : BankTrialLocalState q) := by
        rw [← hz]
        exact hreach
      rw [hz]
      exact horphan S hclean B begun hreach' hm he e

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-! ## Generic fold-max transfer on the original finite digit range -/

/-- The initial accumulator is no larger than its fold-max. -/
private theorem bankTrialDurationFoldMaxSeedLower
    (xs : List Nat) :
    ∀ seed : Nat, seed ≤ xs.foldl Nat.max seed := by
  induction xs with
  | nil =>
      intro seed
      exact Nat.le_refl seed
  | cons head tail ih =>
      intro seed
      change seed ≤ tail.foldl Nat.max (Nat.max seed head)
      exact Nat.le_trans (Nat.le_max_left seed head)
        (ih (Nat.max seed head))

/-- Any member is bounded by the fold-max, including with an
arbitrary initial accumulator. -/
private theorem bankTrialDurationFoldMaxMember
    (xs : List Nat) :
    ∀ (seed item : Nat), item ∈ xs →
      item ≤ xs.foldl Nat.max seed := by
  induction xs with
  | nil =>
      intro seed item h
      cases h
  | cons head tail ih =>
      intro seed item h
      change item ≤ tail.foldl Nat.max (Nat.max seed head)
      have hc : item = head ∨ item ∈ tail := by
        simpa only [List.mem_cons] using h
      rcases hc with he | ht
      · rw [he]
        exact Nat.le_trans (Nat.le_max_right seed head)
          (bankTrialDurationFoldMaxSeedLower tail _)
      · exact ih (Nat.max seed head) item ht

/-- A uniform upper bound on the seed and every member bounds
the fold-max. -/
private theorem bankTrialDurationFoldMaxBound
    (xs : List Nat) :
    ∀ (seed bound : Nat), seed ≤ bound →
      (∀ item : Nat, item ∈ xs → item ≤ bound) →
      xs.foldl Nat.max seed ≤ bound := by
  induction xs with
  | nil =>
      intro seed bound hseed _
      exact hseed
  | cons head tail ih =>
      intro seed bound hseed hall
      change tail.foldl Nat.max (Nat.max seed head) ≤ bound
      apply ih (Nat.max seed head) bound
      · exact Nat.max_le_of_le_of_le hseed
          (hall head (by simp))
      · intro item hitem
        exact hall item (by simp [hitem])

/-- Componentwise domination of two arrays implies domination
of their fold-max, even with different initial seeds. -/
private theorem bankTrialDurationOfFnFoldMaxMono :
    ∀ (n : Nat) (f g : Fin n → Nat)
      (seedF seedG : Nat),
      (∀ i : Fin n, f i ≤ g i) →
      seedF ≤ seedG →
      (List.ofFn f).foldl Nat.max seedF ≤
        (List.ofFn g).foldl Nat.max seedG := by
  intro n
  induction n with
  | zero =>
      intro f g seedF seedG _ hseed
      simpa only [List.ofFn_zero, List.foldl_nil] using hseed
  | succ k ih =>
      intro f g seedF seedG hpoint hseed
      rw [List.ofFn_succ, List.ofFn_succ,
        List.foldl_cons, List.foldl_cons]
      apply ih (fun i : Fin k => f i.succ)
        (fun i : Fin k => g i.succ)
        (Nat.max seedF (f 0)) (Nat.max seedG (g 0))
      · intro i
        exact hpoint i.succ
      · exact Nat.max_le_of_le_of_le
          (Nat.le_trans hseed (Nat.le_max_left _ _))
          (Nat.le_trans (hpoint 0) (Nat.le_max_right _ _))

/-- A fold-max whose only potentially nonzero coordinate is
the chosen one equals that coordinate exactly. -/
private theorem bankTrialDurationOfFnFoldMaxSpike
    (n : Nat) (f : Fin n → Nat) (chosen : Fin n)
    (hother : ∀ i : Fin n, i ≠ chosen → f i = 0) :
    (List.ofFn f).foldl Nat.max 0 = f chosen := by
  have hchosen : f chosen ≤
      (List.ofFn f).foldl Nat.max 0 := by
    exact bankTrialDurationFoldMaxMember
      (List.ofFn f) 0 (f chosen)
      ((List.mem_ofFn).2 ⟨chosen, rfl⟩)
  have hupper : (List.ofFn f).foldl Nat.max 0 ≤
      f chosen := by
    apply bankTrialDurationFoldMaxBound
      (List.ofFn f) 0 (f chosen) (Nat.zero_le _)
    intro item hitem
    obtain ⟨i, hi⟩ := (List.mem_ofFn).1 hitem
    rw [← hi]
    by_cases he : i = chosen
    · rw [he]
      exact Nat.le_refl _
    · rw [hother i he]
      exact Nat.zero_le _
  exact Nat.le_antisymm hupper hchosen

/-- One strict chosen-coordinate drop and zero at every other
coordinate imply an exact one-unit drop of the fold-max. -/
theorem bankTrialDurationFoldMaxUniqueDrop
    (n : Nat) (old new : Fin n → Nat)
    (chosen : Fin n)
    (hOldOther : ∀ i, i ≠ chosen → old i = 0)
    (hNewOther : ∀ i, i ≠ chosen → new i = 0)
    (hchosen : new chosen + 1 ≤ old chosen) :
    (List.ofFn new).foldl Nat.max 0 + 1 ≤
      (List.ofFn old).foldl Nat.max 0 := by
  rw [bankTrialDurationOfFnFoldMaxSpike n new chosen hNewOther,
    bankTrialDurationOfFnFoldMaxSpike n old chosen hOldOther]
  exact hchosen

/-- Pointwise domination of all real protected token ranks
controls the actual worker maximum, not merely a detached
pair of token weights. -/
theorem bankTrialDurationWorkerMaximumMono {q : Nat}
    (A B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hpoint : ∀ i : Fin (compileAdvice q).b,
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (i.val + 1) (bankTrialLiveWaveToken A i) ≤
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (i.val + 1) (bankTrialLiveWaveToken B i)) :
    bankTrialDurationWorkerTokenMaximum A ≤
      bankTrialDurationWorkerTokenMaximum B := by
  unfold bankTrialDurationWorkerTokenMaximum
  exact bankTrialDurationOfFnFoldMaxMono
    (compileAdvice q).b
    (fun i => bankTrialDurationWorkerTokenRank (compileAdvice q).b
      (i.val + 1) (bankTrialLiveWaveToken A i))
    (fun i => bankTrialDurationWorkerTokenRank (compileAdvice q).b
      (i.val + 1) (bankTrialLiveWaveToken B i))
    0 0 hpoint (Nat.le_refl 0)

/-- The rank is zero exactly for E on the protected range
1 <= j <= b. -/
theorem bankTrialDurationTokenRankZeroOnlyEmpty
    (b j : Nat) (t : BTok)
    (hj : 1 ≤ j) (hb : j ≤ b)
    (hrank : bankTrialDurationWorkerTokenRank b j t = 0) :
    t = .E := by
  cases t <;>
    simp [bankTrialDurationWorkerTokenRank] at hrank ⊢ <;>
    omega

/-- The maximum-zero premise really means every physical digit
token is E. No CLEAN lock or uniqueness is needed for this step. -/
theorem bankTrialDurationWorkerMaximumZeroTokens {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hzero : bankTrialDurationWorkerTokenMaximum B = 0) :
    ∀ i : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken B i = .E := by
  intro i
  have hle :
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (i.val + 1) (bankTrialLiveWaveToken B i) ≤
      bankTrialDurationWorkerTokenMaximum B := by
    unfold bankTrialDurationWorkerTokenMaximum
    exact bankTrialDurationFoldMaxMember
      (List.ofFn (fun j : Fin (compileAdvice q).b =>
        bankTrialDurationWorkerTokenRank (compileAdvice q).b
          (j.val + 1) (bankTrialLiveWaveToken B j)))
      0
      (bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (i.val + 1) (bankTrialLiveWaveToken B i))
      ((List.mem_ofFn).2 ⟨i, rfl⟩)
  have hrank :
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (i.val + 1) (bankTrialLiveWaveToken B i) = 0 := by
    omega
  exact bankTrialDurationTokenRankZeroOnlyEmpty
    (compileAdvice q).b (i.val + 1)
    (bankTrialLiveWaveToken B i)
    (by omega) (by exact Nat.succ_le_of_lt i.isLt) hrank

/-- Conversely, an all-empty physical token window has zero
fold-max, regardless of old bits, mode or leases. -/
theorem bankTrialDurationWorkerMaximumEmptyTokens {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hempty : ∀ i : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken B i = .E) :
    bankTrialDurationWorkerTokenMaximum B = 0 := by
  have hupper : bankTrialDurationWorkerTokenMaximum B ≤ 0 := by
    unfold bankTrialDurationWorkerTokenMaximum
    apply bankTrialDurationFoldMaxBound _ 0 0 (Nat.le_refl 0)
    intro item hitem
    obtain ⟨i, hi⟩ := (List.mem_ofFn).1 hitem
    rw [← hi, hempty i]
    exact Nat.le_refl _
  omega

/-- Genuine unique-worker token ranks give a strict drop of the
actual List.foldl Nat.max potential. The callers must prove
both old and new off-owner ranks are zero. -/
theorem bankTrialDurationWorkerMaximumUniqueDrop {q : Nat}
    (A B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (chosen : Fin (compileAdvice q).b)
    (hOldOther : ∀ i, i ≠ chosen →
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (i.val + 1) (bankTrialLiveWaveToken A i) = 0)
    (hNewOther : ∀ i, i ≠ chosen →
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (i.val + 1) (bankTrialLiveWaveToken B i) = 0)
    (hDrop :
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (chosen.val + 1) (bankTrialLiveWaveToken B chosen) + 1 ≤
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (chosen.val + 1) (bankTrialLiveWaveToken A chosen)) :
    bankTrialDurationWorkerTokenMaximum B + 1 ≤
      bankTrialDurationWorkerTokenMaximum A := by
  unfold bankTrialDurationWorkerTokenMaximum
  exact bankTrialDurationFoldMaxUniqueDrop
    (compileAdvice q).b
    (fun i => bankTrialDurationWorkerTokenRank (compileAdvice q).b
      (i.val + 1) (bankTrialLiveWaveToken A i))
    (fun i => bankTrialDurationWorkerTokenRank (compileAdvice q).b
      (i.val + 1) (bankTrialLiveWaveToken B i))
    chosen hOldOther hNewOther hDrop

/-! ## Raw boundary rows required by orphan accounting -/

/-- At an old IWAIT/CWAIT root with an empty first token, the
real outgoing BANK owner never creates a token, and its root
mode either waits or resets when the lease expires. -/
theorem bankTrialDurationOrphanRawOutgoing
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 < b)
    (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false)
    (hm : x.mode = .IWAIT ∨ x.mode = .CWAIT)
    (he : y.tok = .E) :
    (bankPair x y 1 b theta).2.tok = .E ∧
    ((bankPair x y 1 b theta).1.mode = x.mode ∨
      (bankPair x y 1 b theta).1.mode = .RESET) := by
  have hn : b ≠ 1 := by omega
  rcases hm with hi | hc
  · by_cases hl : 1 < x.lease
    · simp [bankPair, hx, hy, hg, hi, he, hb, hn, hl,
        isRetTok, isWaitMode, Id.run_pure, Id.run_bind]
    · simp [bankPair, hx, hy, hg, hi, he, hb, hn, hl,
        isRetTok, isWaitMode, Id.run_pure, Id.run_bind]
  · by_cases hl : 1 < x.lease
    · simp [bankPair, hx, hy, hg, hc, he, hb, hn, hl,
        isRetTok, isWaitMode, Id.run_pure, Id.run_bind]
    · simp [bankPair, hx, hy, hg, hc, he, hb, hn, hl,
        isRetTok, isWaitMode, Id.run_pure, Id.run_bind]

/-- The incoming root never creates a root token. With old
IWAIT/CWAIT it stays in the old mode or enters RESET. -/
theorem bankTrialDurationOrphanRawIncoming
    (x : BankCell)
    (hm : x.mode = .IWAIT ∨ x.mode = .CWAIT) :
    (GrantBankReference.incomingRootBankMap x).tok = .E ∧
    ((GrantBankReference.incomingRootBankMap x).mode = x.mode ∨
      (GrantBankReference.incomingRootBankMap x).mode = .RESET) := by
  rcases hm with hi | hc
  · by_cases hl : 1 < x.lease
    · simp [GrantBankReference.incomingRootBankMap,
        hi, hl, isWaitMode]
    · simp [GrantBankReference.incomingRootBankMap,
        hi, hl, isWaitMode]
  · by_cases hl : 1 < x.lease
    · simp [GrantBankReference.incomingRootBankMap,
        hc, hl, isWaitMode]
    · simp [GrantBankReference.incomingRootBankMap,
        hc, hl, isWaitMode]

/-- The top map cannot increase any token service rank. -/
theorem bankTrialDurationTopTokenRankNonincrease
    (b : Nat) (x : BankCell) :
    bankTrialDurationWorkerTokenRank b b
      (GrantBankReference.topBoundaryBankMap x).tok ≤
    bankTrialDurationWorkerTokenRank b b x.tok := by
  cases ht : x.tok <;>
    simp [GrantBankReference.topBoundaryBankMap,
      bankTrialDurationWorkerTokenRank, ht] <;>
    omega

/-- Specifically, an old top IR is erased and pays at least
one worker service on that boundary edge. -/
theorem bankTrialDurationTopIRRankDrop
    (b : Nat) (x : BankCell)
    (ht : x.tok = .IR) :
    bankTrialDurationWorkerTokenRank b b
      (GrantBankReference.topBoundaryBankMap x).tok + 1 ≤
    bankTrialDurationWorkerTokenRank b b x.tok := by
  simp [GrantBankReference.topBoundaryBankMap,
    bankTrialDurationWorkerTokenRank, ht]
  omega

/-! ## Exact outstanding reference-row interface -/

/-- This is the precise remaining physical E/E nonbirth row,
not a theorem. It is strictly narrower than the original
global class-2 claim: the state is an unlatched wait with
all protected tokens E and the logical window is nonaliased.
It includes all root/interior/top/incoming/outside edges. -/
def BankTrialDurationOrphanReferenceEdgeRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  BankTrialLiveWindowNonalias n q →
  ∀ (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    B.success = false →
    (bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT) →
    (∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken B j = .E) →
    ∀ e : Fin n,
      (∀ j : Fin (compileAdvice q).b,
        bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B e) j = .E) ∧
      (bankTrialLiveWaveRootMode
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B e) =
            bankTrialLiveWaveRootMode B ∨
        bankTrialLiveWaveRootMode
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B e) = .RESET)

/-- Exact horphan-premise conclusion, conditional only on the
separately displayed physical all-edge E/E row and explicit
nonaliasing. The only LIVE successor possibility is the same
IWAIT/CWAIT mode with zero token maximum; RESET successors
are observed as RECOVERY, and other terminal phases cost zero. -/
theorem bankTrialDurationLeaseAwareOrphanOfReferenceRows
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hrow : BankTrialDurationOrphanReferenceEdgeRows
      (q := q) ring root) :
    ∀ (S : GrantBankReference.BankLocalReference
        (compileAdvice q).b),
      BankTrialLocalClean q S →
      ∀ (B : GrantBankReference.BankLocalReference
          (compileAdvice q).b) (begun : Bool),
        BankTrialDurationReachable ring root S
          (⟨B, .live begun⟩ : BankTrialLocalState q) →
        (bankTrialLiveWaveRootMode B = .IWAIT ∨
          bankTrialLiveWaveRootMode B = .CWAIT) →
        bankTrialDurationWorkerTokenMaximum B = 0 →
        ∀ e : Fin n,
          bankTrialDurationLeaseAwareWorkerRemaining
            (bankTrialLocalNext ring root
              (⟨B, .live begun⟩ : BankTrialLocalState q) e) = 0 := by
  intro S hclean B begun hreach hm hmax e
  obtain ⟨word, hword⟩ := hreach
  have hf : B.success = false :=
    bankTrialProbabilityCleanLiveUnlatched
      ring root S hclean word B begun hword
  have hempty := bankTrialDurationWorkerMaximumZeroTokens B hmax
  have hphysical := hrow hw B hf hm hempty e
  have hbank := bankTrialLocalNextLiveBank ring root e B begun
  have hnextReach := bankTrialDurationReachableNext
    ring root S (⟨B, .live begun⟩ : BankTrialLocalState q)
      ⟨word, hword⟩ e
  obtain ⟨nextWord, hnextWord⟩ := hnextReach
  cases hnext : bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) e with
  | mk nextBank nextPhase =>
      have hbankEq :
          nextBank =
            GrantBankReference.bankLocalReferenceStepClamped
              ring root B e := by
        rw [hnext] at hbank
        exact hbank
      cases nextPhase with
      | live nextBegun =>
          have hwordNext :
              bankTrialLocalRun ring root nextWord
                (bankTrialLocalStart S) =
                  (⟨nextBank, .live nextBegun⟩ :
                    BankTrialLocalState q) := by
            rw [hnextWord]
            exact hnext
          have hlock := bankTrialWindowLockedCleanWords
            ring root hw S hclean nextWord
          have hnotReset :
              bankTrialLiveWaveRootMode nextBank ≠ .RESET :=
            by
              have h := hlock.2 nextBegun (by rw [hwordNext])
              rw [hwordNext] at h
              exact h
          have hnewMode :
              bankTrialLiveWaveRootMode nextBank =
                  bankTrialLiveWaveRootMode B ∨
                bankTrialLiveWaveRootMode nextBank = .RESET := by
            rw [hbankEq]
            exact hphysical.2
          have hwait :
              bankTrialLiveWaveRootMode nextBank = .IWAIT ∨
                bankTrialLiveWaveRootMode nextBank = .CWAIT := by
            rcases hnewMode with hsame | hreset
            · rw [hsame]
              exact hm
            · exact False.elim (hnotReset hreset)
          have hnewEmpty :
              ∀ j : Fin (compileAdvice q).b,
                bankTrialLiveWaveToken nextBank j = .E := by
            intro j
            rw [hbankEq]
            exact hphysical.1 j
          have hnewZero :=
            bankTrialDurationWorkerMaximumEmptyTokens
              nextBank hnewEmpty
          exact bankTrialDurationLeaseAwareOrphanRemainingZero
            nextBank nextBegun hwait hnewZero
      | recovery => rfl
      | won => rfl
      | lost => rfl

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A protected nonroot field corresponds to the preceding wave
index. This avoids arithmetic rewrites under dependent Fin bounds. -/
private theorem bankTrialDurationOrphanOldFieldEmpty {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hempty : ∀ k : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken B k = .E)
    (i : Fin ((compileAdvice q).b + 1)) (hi : 0 < i.val) :
    (B.fields i).2.2.1 = .E := by
  have hidx : i.val - 1 < (compileAdvice q).b := by
    have hib := i.isLt
    omega
  have h := hempty ⟨i.val - 1, hidx⟩
  change (B.fields ⟨i.val - 1 + 1, by omega⟩).2.2.1 = .E at h
  have heq :
      (⟨i.val - 1 + 1, by omega⟩ :
        Fin ((compileAdvice q).b + 1)) = i :=
    Fin.ext (by change i.val - 1 + 1 = i.val; omega)
  rw [heq] at h
  exact h

/-- Internal E/E at a nonroot source remains E/E. -/
private theorem bankTrialDurationOrphanInteriorEmptyPair {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hempty : ∀ k : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken B k = .E)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val) :
    (GrantBankReference.bankLocalReferenceInternalPair q B j).1.tok =
        .E ∧
    (GrantBankReference.bankLocalReferenceInternalPair q B j).2.tok =
        .E := by
  have hleft :
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by omega⟩).tok = .E :=
    bankTrialDurationOrphanOldFieldEmpty B hempty
      ⟨j.val, by omega⟩ hj
  have hright :
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val + 1, by omega⟩).tok = .E :=
    bankTrialDurationOrphanOldFieldEmpty B hempty
      ⟨j.val + 1, by omega⟩
      (by change (0 : Nat) < j.val + 1; omega)
  have hpair := bankTrialInteriorRawEmptyPair
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by omega⟩)
    (by change 1 ≤ j.val; omega) j.isLt rfl hleft hright
  exact ⟨hpair.1, hpair.2.1⟩

/-- Index-zero responder is the outgoing waiting-root row;
other responders are ordinary interior E/E rows. -/
private theorem bankTrialDurationOrphanInternalTargetEmpty {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hempty : ∀ k : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken B k = .E)
    (j : Fin (compileAdvice q).b) :
    (GrantBankReference.bankLocalReferenceInternalPair q B j).2.tok =
      .E := by
  by_cases hz : j.val = 0
  · have heq : j = ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ :=
      Fin.ext hz
    rw [heq]
    have hb : 1 < (compileAdvice q).b := by
      change 1 < (compileAdvice q).s + 11
      omega
    have hfirst :
        (GrantBankReference.bankLocalReferenceCell B
          ⟨1, by omega⟩).tok = .E :=
      bankTrialDurationOrphanOldFieldEmpty B hempty
        ⟨1, by omega⟩ (by change (0 : Nat) < 1; omega)
    have hroot :
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by omega⟩).mode = .IWAIT ∨
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by omega⟩).mode = .CWAIT := hm
    have hpair := bankTrialDurationOrphanRawOutgoing
      (compileAdvice q).b (compileAdvice q).theta
      (GrantBankReference.bankLocalReferenceCell B
        ⟨0, by omega⟩)
      (GrantBankReference.bankLocalReferenceCell B
        ⟨1, by omega⟩)
      hb rfl rfl rfl hroot hfirst
    exact hpair.1
  · exact (bankTrialDurationOrphanInteriorEmptyPair
      B hempty j (Nat.pos_of_ne_zero hz)).2

/-- The full actual field selector, with source, responder, top,
incoming and frame priorities, cannot manufacture a digit token
out of an all-empty IWAIT/CWAIT reference. -/
private theorem bankTrialDurationOrphanDigitFieldEmpty {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hempty : ∀ k : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken B k = .E)
    (i : Fin ((compileAdvice q).b + 1)) (hi : 0 < i.val) :
    (GrantBankReference.bankLocalReferenceFieldStepClamped
      ring root e B i).2.2.1 = .E := by
  classical
  unfold GrantBankReference.bankLocalReferenceFieldStepClamped
  by_cases hx : i.val < (compileAdvice q).b ∧
      e = Counter.site ring root i.val
  · rw [dif_pos hx]
    have hp := bankTrialDurationOrphanInteriorEmptyPair
      B hempty ⟨i.val, hx.1⟩ (by change 0 < i.val; exact hi)
    exact (bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair
        q B ⟨i.val, hx.1⟩).1)).2.trans hp.1
  · rw [dif_neg hx]
    by_cases hy : 0 < i.val ∧
        e = Counter.site ring root (i.val - 1)
    · rw [dif_pos hy]
      have hidx : i.val - 1 < (compileAdvice q).b := by
        have hib := i.isLt
        omega
      have hp := bankTrialDurationOrphanInternalTargetEmpty
        B hm hempty ⟨i.val - 1, hidx⟩
      exact (bankTrialLiveClampBitToken q
        ((GrantBankReference.bankLocalReferenceInternalPair
          q B ⟨i.val - 1, hidx⟩).2)).2.trans hp
    · rw [dif_neg hy]
      by_cases ht : i.val = (compileAdvice q).b ∧
          e = Counter.site ring root (compileAdvice q).b
      · rw [dif_pos ht]
        have hcell :
            (GrantBankReference.bankLocalReferenceCell B i).tok =
              .E :=
          bankTrialDurationOrphanOldFieldEmpty B hempty i hi
        have htop :
            (GrantBankReference.topBoundaryBankMap
              (GrantBankReference.bankLocalReferenceCell B i)).tok =
                .E := by
          simp [GrantBankReference.topBoundaryBankMap, hcell]
        exact (bankTrialLiveClampBitToken q
          (GrantBankReference.topBoundaryBankMap
            (GrantBankReference.bankLocalReferenceCell B i))).2.trans
              htop
      · rw [dif_neg ht]
        have hin : ¬ (i.val = 0 ∧
            ring.rightNeighbor e = root) := by
          intro h
          omega
        rw [dif_neg hin]
        exact bankTrialDurationOrphanOldFieldEmpty B hempty i hi

/-- The outgoing-root and incoming-root raw wait rows preserve
their old root mode or reset it. No digit-service guard can act
on the root mode, except the outgoing source guard. -/
private theorem bankTrialDurationOrphanRootFieldMode {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hempty : ∀ k : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken B k = .E) :
    (GrantBankReference.bankLocalReferenceFieldStepClamped
      ring root e B ⟨0, by omega⟩).1 =
        bankTrialLiveWaveRootMode B ∨
    (GrantBankReference.bankLocalReferenceFieldStepClamped
      ring root e B ⟨0, by omega⟩).1 = .RESET := by
  classical
  have hb : 1 < (compileAdvice q).b := by
    change 1 < (compileAdvice q).s + 11
    omega
  have hroot :
      (GrantBankReference.bankLocalReferenceCell B
        ⟨0, by omega⟩).mode = .IWAIT ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨0, by omega⟩).mode = .CWAIT := hm
  have hfirst :
      (GrantBankReference.bankLocalReferenceCell B
        ⟨1, by omega⟩).tok = .E :=
    bankTrialDurationOrphanOldFieldEmpty B hempty
      ⟨1, by omega⟩ (by change (0 : Nat) < 1; omega)
  have hout := bankTrialDurationOrphanRawOutgoing
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨0, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨1, by omega⟩)
    hb rfl rfl rfl hroot hfirst
  have hinrow := bankTrialDurationOrphanRawIncoming
    (GrantBankReference.bankLocalReferenceCell B
      ⟨0, by omega⟩) hroot
  unfold GrantBankReference.bankLocalReferenceFieldStepClamped
  by_cases hx : (0 : Nat) < (compileAdvice q).b ∧
      e = Counter.site ring root 0
  · rw [dif_pos hx]
    exact hout.2
  · rw [dif_neg hx]
    have hy : ¬ ((0 : Nat) < 0 ∧
        e = Counter.site ring root (0 - 1)) := by
      intro h
      omega
    rw [dif_neg hy]
    have ht : ¬ ((0 : Nat) = (compileAdvice q).b ∧
        e = Counter.site ring root (compileAdvice q).b) := by
      intro h
      omega
    rw [dif_neg ht]
    by_cases hr : (0 : Nat) = 0 ∧
        ring.rightNeighbor e = root
    · rw [dif_pos hr]
      exact hinrow.2
    · rw [dif_neg hr]
      exact Or.inl rfl

/-- All-edge E/E nonbirth and mode preservation on the exact
original scheduler, including short-ring selector priorities.
The public interface retains its explicit nonalias premise. -/
theorem bankTrialDurationOrphanReferenceRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    BankTrialDurationOrphanReferenceEdgeRows (q := q) ring root := by
  intro _ B hf hm hempty e
  constructor
  · intro k
    by_cases hs : Counter.Support q ring root e
    · change
        ((GrantBankReference.bankLocalReferenceStepClamped
          ring root B e).fields
            ⟨k.val + 1, by omega⟩).2.2.1 = .E
      rw [bankTrialLocalStepField ring root e B hs hf
        ⟨k.val + 1, by omega⟩]
      exact bankTrialDurationOrphanDigitFieldEmpty
        ring root e B hm hempty ⟨k.val + 1, by omega⟩
        (by change 0 < k.val + 1; omega)
    · rw [bankTrialLiveCarryUnsupportedRawFrame
        ring root e B hs]
      exact hempty k
  · by_cases hs : Counter.Support q ring root e
    · change
        ((GrantBankReference.bankLocalReferenceStepClamped
          ring root B e).fields ⟨0, by omega⟩).1 =
            bankTrialLiveWaveRootMode B ∨
        ((GrantBankReference.bankLocalReferenceStepClamped
          ring root B e).fields ⟨0, by omega⟩).1 = .RESET
      rw [bankTrialLocalStepField ring root e B hs hf
        ⟨0, by omega⟩]
      exact bankTrialDurationOrphanRootFieldMode
        ring root e B hm hempty
    · rw [bankTrialLiveCarryUnsupportedRawFrame
        ring root e B hs]
      exact Or.inl rfl

/-- The moving-index spike theorem: old and new unique ranks may
be carried at different physical digit coordinates. -/
theorem bankTrialDurationFoldMaxMovingUniqueDrop
    (n : Nat) (old new : Fin n → Nat)
    (oldChosen newChosen : Fin n)
    (hOldOther : ∀ k, k ≠ oldChosen → old k = 0)
    (hNewOther : ∀ k, k ≠ newChosen → new k = 0)
    (hDrop : new newChosen + 1 ≤ old oldChosen) :
    (List.ofFn new).foldl Nat.max 0 + 1 ≤
      (List.ofFn old).foldl Nat.max 0 := by
  rw [bankTrialDurationOfFnFoldMaxSpike
      n new newChosen hNewOther,
    bankTrialDurationOfFnFoldMaxSpike
      n old oldChosen hOldOther]
  exact hDrop

/-- Moving-index strict drop for the actual protected-token
maximum, with an explicit off-owner zero-rank certificate on
both sides. -/
theorem bankTrialDurationWorkerMaximumMovingUniqueDrop {q : Nat}
    (A B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (oldChosen newChosen : Fin (compileAdvice q).b)
    (hOldOther : ∀ k, k ≠ oldChosen →
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (k.val + 1) (bankTrialLiveWaveToken A k) = 0)
    (hNewOther : ∀ k, k ≠ newChosen →
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (k.val + 1) (bankTrialLiveWaveToken B k) = 0)
    (hDrop :
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (newChosen.val + 1) (bankTrialLiveWaveToken B newChosen) + 1 ≤
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (oldChosen.val + 1) (bankTrialLiveWaveToken A oldChosen)) :
    bankTrialDurationWorkerTokenMaximum B + 1 ≤
      bankTrialDurationWorkerTokenMaximum A := by
  unfold bankTrialDurationWorkerTokenMaximum
  exact bankTrialDurationFoldMaxMovingUniqueDrop
    (compileAdvice q).b
    (fun k => bankTrialDurationWorkerTokenRank (compileAdvice q).b
      (k.val + 1) (bankTrialLiveWaveToken A k))
    (fun k => bankTrialDurationWorkerTokenRank (compileAdvice q).b
      (k.val + 1) (bankTrialLiveWaveToken B k))
    oldChosen newChosen hOldOther hNewOther hDrop


/-- For a certified single worker, a selected interior transfer
between the adjacent wave slots has a strict drop in the true
fold-maximum. Both the old unique-worker proof and the
unchanged-elsewhere frame are used, not just the raw pair row. -/
theorem bankTrialDurationInteriorSelectedMaximumDrop {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (oldChosen newChosen : Fin (compileAdvice q).b)
    (hposition :
      (oldChosen = ⟨j.val - 1, by omega⟩ ∧ newChosen = j) ∨
      (oldChosen = j ∧ newChosen = ⟨j.val - 1, by omega⟩))
    (hOld : bankTrialLiveWaveToken B oldChosen ≠ .E)
    (hClear : bankTrialLiveWaveToken
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val))
      oldChosen = .E)
    (hRank :
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (newChosen.val + 1)
        (bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j.val))
          newChosen) + 1 ≤
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (oldChosen.val + 1)
        (bankTrialLiveWaveToken B oldChosen)) :
    bankTrialDurationWorkerTokenMaximum
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) + 1 ≤
      bankTrialDurationWorkerTokenMaximum B := by
  have hOldOther : ∀ k, k ≠ oldChosen →
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (k.val + 1) (bankTrialLiveWaveToken B k) = 0 := by
    intro k hk
    rw [bankTrialInteriorOldWorkerOthersEmpty
      B hc oldChosen k hOld hk]
    rfl
  have hNewOther : ∀ k, k ≠ newChosen →
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (k.val + 1)
        (bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j.val)) k) = 0 := by
    intro k hk
    by_cases ho : k = oldChosen
    · rw [ho, hClear]
      rfl
    · have hnotLeft :
          k ≠ (⟨j.val - 1, by omega⟩ :
            Fin (compileAdvice q).b) := by
        intro he
        rcases hposition with hp | hp
        · exact ho (he.trans hp.1.symm)
        · exact hk (he.trans hp.2.symm)
      have hnotRight : k ≠ j := by
        intro he
        rcases hposition with hp | hp
        · exact hk (he.trans hp.2.symm)
        · exact ho (he.trans hp.1.symm)
      have hs : k.val + 1 ≠ j.val := by
        intro he
        apply hnotLeft
        apply Fin.ext
        change k.val = j.val - 1
        omega
      have ht : k.val + 1 ≠ j.val + 1 := by
        intro he
        apply hnotRight
        apply Fin.ext
        change k.val = j.val
        omega
      rw [bankTrialDurationSelectedInteriorOutsideRank
        ring root hw B hf j hj k hs ht]
      exact hOldOther k ho
  exact bankTrialDurationWorkerMaximumMovingUniqueDrop
    B
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val))
    oldChosen newChosen hOldOther hNewOther hRank

/-- The selected IR row moves the worker one protected digit
forward and strictly decreases the actual worker maximum. -/
theorem bankTrialDurationSelectedIRMaximumDrop {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .IR)
    (hdst : (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .E) :
    bankTrialDurationWorkerTokenMaximum
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) + 1 ≤
      bankTrialDurationWorkerTokenMaximum B := by
  have hrow := bankTrialDurationSelectedIRTokenRank
    ring root hw B hf j hj hsrc hdst
  have hind :
      (⟨j.val - 1 + 1, by omega⟩ :
        Fin ((compileAdvice q).b + 1)) =
        ⟨j.val, by omega⟩ :=
    Fin.ext (by change j.val - 1 + 1 = j.val; omega)
  have hold :
      bankTrialLiveWaveToken B ⟨j.val - 1, by omega⟩ = .IR := by
    change (B.fields ⟨j.val - 1 + 1, by omega⟩).2.2.1 = .IR
    rw [hind]
    exact hsrc
  have hclear :
      bankTrialLiveWaveToken
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val))
        ⟨j.val - 1, by omega⟩ = .E := by
    change ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val - 1 + 1, by omega⟩).2.2.1 = .E
    rw [hind]
    exact hrow.1
  have hdrop :
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (j.val + 1)
        (bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j.val)) j) + 1 ≤
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        ((⟨j.val - 1, by omega⟩ :
          Fin (compileAdvice q).b).val + 1)
        (bankTrialLiveWaveToken B ⟨j.val - 1, by omega⟩) := by
    change bankTrialDurationWorkerTokenRank (compileAdvice q).b
      (j.val + 1)
        ((GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)).fields
          ⟨j.val + 1, by omega⟩).2.2.1 + 1 ≤
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (j.val - 1 + 1)
        (bankTrialLiveWaveToken B ⟨j.val - 1, by omega⟩)
    rw [show j.val - 1 + 1 = j.val by omega, hold]
    exact hrow.2
  apply bankTrialDurationInteriorSelectedMaximumDrop
    ring root hw B hf hc j hj
    ⟨j.val - 1, by omega⟩ j
    (Or.inl ⟨rfl, rfl⟩)
  · rw [hold]
    intro h
    cases h
  · exact hclear
  · exact hdrop

/-- The selected AL return row strictly decreases the worker
maximum across the reversed pair of adjacent indices. -/
theorem bankTrialDurationSelectedALMaximumDrop {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .E)
    (hdst : (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .AL) :
    bankTrialDurationWorkerTokenMaximum
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) + 1 ≤
      bankTrialDurationWorkerTokenMaximum B := by
  have hrow := bankTrialDurationSelectedALTokenRank
    ring root hw B hf j hj hsrc hdst
  have hdstWave : bankTrialLiveWaveToken B j = .AL := hdst
  have hind :
      (⟨j.val - 1 + 1, by omega⟩ :
        Fin ((compileAdvice q).b + 1)) =
        ⟨j.val, by omega⟩ :=
    Fin.ext (by change j.val - 1 + 1 = j.val; omega)
  have hclear :
      bankTrialLiveWaveToken
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) j = .E :=
    hrow.1
  have hdrop :
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        ((⟨j.val - 1, by omega⟩ :
          Fin (compileAdvice q).b).val + 1)
        (bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j.val))
          ⟨j.val - 1, by omega⟩) + 1 ≤
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (j.val + 1) (bankTrialLiveWaveToken B j) := by
    change bankTrialDurationWorkerTokenRank (compileAdvice q).b
      (j.val - 1 + 1)
        ((GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)).fields
          ⟨j.val - 1 + 1, by omega⟩).2.2.1 + 1 ≤
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (j.val + 1) (bankTrialLiveWaveToken B j)
    rw [hind]
    rw [show j.val - 1 + 1 = j.val by omega, hdstWave]
    exact hrow.2
  apply bankTrialDurationInteriorSelectedMaximumDrop
    ring root hw B hf hc j hj j
    ⟨j.val - 1, by omega⟩ (Or.inr ⟨rfl, rfl⟩)
  · rw [hdstWave]
    intro h
    cases h
  · exact hclear
  · exact hdrop

/-- A selected CR0/CR1 forward comparison pays one unit even
when the bit equality decides the new comparison-token variant. -/
theorem bankTrialDurationSelectedCRMaximumDrop {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .CR0 ∨
      (B.fields ⟨j.val, by omega⟩).2.2.1 = .CR1)
    (hdst : (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .E) :
    bankTrialDurationWorkerTokenMaximum
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) + 1 ≤
      bankTrialDurationWorkerTokenMaximum B := by
  have hrow := bankTrialDurationSelectedCRTokenRank
    ring root hw B hf j hj hsrc hdst
  have hind :
      (⟨j.val - 1 + 1, by omega⟩ :
        Fin ((compileAdvice q).b + 1)) =
        ⟨j.val, by omega⟩ :=
    Fin.ext (by change j.val - 1 + 1 = j.val; omega)
  have hold :
      bankTrialLiveWaveToken B ⟨j.val - 1, by omega⟩ = .CR0 ∨
      bankTrialLiveWaveToken B ⟨j.val - 1, by omega⟩ = .CR1 := by
    change (B.fields ⟨j.val - 1 + 1, by omega⟩).2.2.1 = .CR0 ∨
      (B.fields ⟨j.val - 1 + 1, by omega⟩).2.2.1 = .CR1
    rw [hind]
    exact hsrc
  have hclear :
      bankTrialLiveWaveToken
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val))
        ⟨j.val - 1, by omega⟩ = .E := by
    change ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val - 1 + 1, by omega⟩).2.2.1 = .E
    rw [hind]
    exact hrow.1
  have hrank :
      bankTrialDurationWorkerTokenRank (compileAdvice q).b j.val
        (bankTrialLiveWaveToken B ⟨j.val - 1, by omega⟩) =
      bankTrialDurationWorkerTokenRank (compileAdvice q).b j.val
        .CR0 := by
    rcases hold with hzero | hone
    · rw [hzero]
    · rw [hone]
      rfl
  have hdrop :
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (j.val + 1)
        (bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j.val)) j) + 1 ≤
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        ((⟨j.val - 1, by omega⟩ :
          Fin (compileAdvice q).b).val + 1)
        (bankTrialLiveWaveToken B ⟨j.val - 1, by omega⟩) := by
    change bankTrialDurationWorkerTokenRank (compileAdvice q).b
      (j.val + 1)
        ((GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)).fields
          ⟨j.val + 1, by omega⟩).2.2.1 + 1 ≤
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (j.val - 1 + 1)
        (bankTrialLiveWaveToken B ⟨j.val - 1, by omega⟩)
    rw [show j.val - 1 + 1 = j.val by omega, hrank]
    exact hrow.2
  apply bankTrialDurationInteriorSelectedMaximumDrop
    ring root hw B hf hc j hj
    ⟨j.val - 1, by omega⟩ j (Or.inl ⟨rfl, rfl⟩)
  · rcases hold with hzero | hone
    · rw [hzero]
      intro h
      cases h
    · rw [hone]
      intro h
      cases h
  · exact hclear
  · exact hdrop

/-- Selected CL0/CL1 return pays one unit independently of
which comparison bit the left-moving token carries. -/
theorem bankTrialDurationSelectedCLMaximumDrop {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .E)
    (hdst : (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .CL0 ∨
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .CL1) :
    bankTrialDurationWorkerTokenMaximum
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) + 1 ≤
      bankTrialDurationWorkerTokenMaximum B := by
  have hrow := bankTrialDurationSelectedCLTokenRank
    ring root hw B hf j hj hsrc hdst
  have hind :
      (⟨j.val - 1 + 1, by omega⟩ :
        Fin ((compileAdvice q).b + 1)) =
        ⟨j.val, by omega⟩ :=
    Fin.ext (by change j.val - 1 + 1 = j.val; omega)
  have hclear :
      bankTrialLiveWaveToken
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) j = .E :=
    hrow.1
  have hrank :
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (j.val + 1) (bankTrialLiveWaveToken B j) =
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (j.val + 1) .CL0 := by
    change bankTrialDurationWorkerTokenRank (compileAdvice q).b
      (j.val + 1)
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 =
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (j.val + 1) .CL0
    rcases hdst with hzero | hone
    · rw [hzero]
    · rw [hone]
      rfl
  have hdrop :
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        ((⟨j.val - 1, by omega⟩ :
          Fin (compileAdvice q).b).val + 1)
        (bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j.val))
          ⟨j.val - 1, by omega⟩) + 1 ≤
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (j.val + 1) (bankTrialLiveWaveToken B j) := by
    change bankTrialDurationWorkerTokenRank (compileAdvice q).b
      (j.val - 1 + 1)
        ((GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)).fields
          ⟨j.val - 1 + 1, by omega⟩).2.2.1 + 1 ≤
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (j.val + 1) (bankTrialLiveWaveToken B j)
    rw [hind]
    rw [show j.val - 1 + 1 = j.val by omega, hrank]
    exact hrow.2
  apply bankTrialDurationInteriorSelectedMaximumDrop
    ring root hw B hf hc j hj j
    ⟨j.val - 1, by omega⟩ (Or.inr ⟨rfl, rfl⟩)
  · rcases hdst with hzero | hone
    · change (B.fields ⟨j.val + 1, by omega⟩).2.2.1 ≠ .E
      rw [hzero]
      intro h
      cases h
    · change (B.fields ⟨j.val + 1, by omega⟩).2.2.1 ≠ .E
      rw [hone]
      intro h
      cases h
  · exact hclear
  · exact hdrop

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Every token service rank in the protected width is below
the worker clipping threshold. -/
theorem bankTrialDurationWorkerTokenRankCap
    (q j : Nat) (hj : 1 ≤ j)
    (hb : j ≤ (compileAdvice q).b) (tok : BTok) :
    bankTrialDurationWorkerTokenRank (compileAdvice q).b j tok ≤
      bankTrialDurationWorkerLimit q := by
  cases tok <;>
    simp only [bankTrialDurationWorkerTokenRank,
      bankTrialDurationWorkerLimit] <;> omega

/-- Clipping is never active on the maximum of genuine
protected token ranks, even with no uniqueness assumption. -/
theorem bankTrialDurationWorkerMaximumCap {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    bankTrialDurationWorkerTokenMaximum B ≤
      bankTrialDurationWorkerLimit q := by
  unfold bankTrialDurationWorkerTokenMaximum
  apply bankTrialDurationFoldMaxBound
    _ 0 (bankTrialDurationWorkerLimit q) (Nat.zero_le _)
  intro item hitem
  obtain ⟨i, hi⟩ := (List.mem_ofFn).1 hitem
  rw [← hi]
  exact bankTrialDurationWorkerTokenRankCap
    q (i.val + 1) (by omega)
    (Nat.succ_le_of_lt i.isLt)
    (bankTrialLiveWaveToken B i)

/-- A LIVE IWAIT/CWAIT with a genuine outstanding worker is
class one, has no lease fallback, and has exactly the physical
token maximum as its lease-aware worker remaining. -/
theorem bankTrialDurationLeaseAwareWaitWorkerExact {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hp : 0 < bankTrialDurationWorkerTokenMaximum B) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) =
      bankTrialDurationWorkerTokenMaximum B := by
  have hnonzero :
      bankTrialDurationWorkerTokenMaximum B ≠ 0 :=
    Nat.ne_of_gt hp
  have hnarmed : bankTrialLiveWaveRootMode B ≠ .ARMED := by
    intro h
    rcases hm with hi | hc
    · rw [h] at hi
      cases hi
    · rw [h] at hc
      cases hc
  have hncstart : bankTrialLiveWaveRootMode B ≠ .CSTART := by
    intro h
    rcases hm with hi | hc
    · rw [h] at hi
      cases hi
    · rw [h] at hc
      cases hc
  have hnotOrphan :
      ¬ ((bankTrialLiveWaveRootMode B = .IWAIT ∨
          bankTrialLiveWaveRootMode B = .CWAIT) ∧
        bankTrialDurationWorkerTokenMaximum B = 0) := by
    intro h
    exact hnonzero h.2
  have hclass :
      bankTrialDurationLeaseAwareClass
        (⟨B, .live begun⟩ : BankTrialLocalState q) = 1 := by
    change
      (if bankTrialLiveWaveRootMode B = .ARMED then 0
       else if
         ((bankTrialLiveWaveRootMode B = .IWAIT ∨
           bankTrialLiveWaveRootMode B = .CWAIT) ∧
          bankTrialDurationWorkerTokenMaximum B = 0)
       then 2 else 1) = 1
    rw [if_neg hnarmed, if_neg hnotOrphan]
  have hfallback : bankTrialDurationWorkerLeaseFallback B = 0 := by
    unfold bankTrialDurationWorkerLeaseFallback
    have hcondition :
        ¬ ((bankTrialLiveWaveRootMode B = .IWAIT ∨
            bankTrialLiveWaveRootMode B = .CWAIT ∨
            bankTrialLiveWaveRootMode B = .RWAIT) ∧
           bankTrialDurationWorkerTokenMaximum B = 0) := by
      intro h
      exact hnonzero h.2
    rw [if_neg hcondition]
  unfold bankTrialDurationLeaseAwareWorkerRemaining
  rw [hclass]
  change bankTrialDurationWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) =
        bankTrialDurationWorkerTokenMaximum B
  unfold bankTrialDurationWorkerRemaining
  rw [if_neg hnarmed, if_neg hncstart, hfallback]
  change Nat.min (bankTrialDurationWorkerLimit q)
      (Nat.max (bankTrialDurationWorkerTokenMaximum B) 0) =
        bankTrialDurationWorkerTokenMaximum B
  have h0 : Nat.max (bankTrialDurationWorkerTokenMaximum B) 0 =
      bankTrialDurationWorkerTokenMaximum B :=
    Nat.max_eq_left (Nat.zero_le _)
  rw [h0]
  exact Nat.min_eq_right (bankTrialDurationWorkerMaximumCap B)

/-- A LIVE waiting successor costs no more than its token
maximum. With zero tokens it is a class-two orphan with zero
lease-aware worker cost. -/
theorem bankTrialDurationLeaseAwareWaitWorkerLeMaximum {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) ≤
      bankTrialDurationWorkerTokenMaximum B := by
  by_cases hz : bankTrialDurationWorkerTokenMaximum B = 0
  · rw [bankTrialDurationLeaseAwareOrphanRemainingZero
      B begun hm hz]
    exact Nat.zero_le _
  · rw [bankTrialDurationLeaseAwareWaitWorkerExact
      B begun hm (Nat.pos_of_ne_zero hz)]
    exact Nat.le_refl _

/-- Transfer a strict interior token-maximum drop to the
actual lease-aware worker remaining for an old LIVE IWAIT/CWAIT.
The new phase is inspected: a LIVE wait is bounded by its
maximum, while RECOVERY/WON/LOST has zero worker cost. -/
theorem bankTrialDurationSelectedInteriorLeaseAwareDropOfMaximum
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hdrop :
      bankTrialDurationWorkerTokenMaximum
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) + 1 ≤
      bankTrialDurationWorkerTokenMaximum B) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)) + 1 ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  have hp : 0 < bankTrialDurationWorkerTokenMaximum B := by
    omega
  have hold := bankTrialDurationLeaseAwareWaitWorkerExact
    B begun hm hp
  have hmode := bankTrialWindowInteriorRootModeFrame
    ring root hw B hf j hj
  have hbank := bankTrialLocalNextLiveBank
    ring root (Counter.site ring root j.val) B begun
  cases hnext : bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q)
      (Counter.site ring root j.val) with
  | mk C phase =>
      have hbankEq :
          C = GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j.val) := by
        rw [hnext] at hbank
        exact hbank
      have hmax :
          bankTrialDurationWorkerTokenMaximum C + 1 ≤
            bankTrialDurationWorkerTokenMaximum B := by
        rw [hbankEq]
        exact hdrop
      cases phase with
      | live nextBegun =>
          have hmnew :
              bankTrialLiveWaveRootMode C = .IWAIT ∨
              bankTrialLiveWaveRootMode C = .CWAIT := by
            rw [hbankEq, hmode]
            exact hm
          have hle :=
            bankTrialDurationLeaseAwareWaitWorkerLeMaximum
              C nextBegun hmnew
          change
            bankTrialDurationLeaseAwareWorkerRemaining
              (⟨C, .live nextBegun⟩ : BankTrialLocalState q) + 1 ≤
            bankTrialDurationLeaseAwareWorkerRemaining
              (⟨B, .live begun⟩ : BankTrialLocalState q)
          rw [hold]
          omega
      | recovery =>
          change (0 : Nat) + 1 ≤
            bankTrialDurationLeaseAwareWorkerRemaining
              (⟨B, .live begun⟩ : BankTrialLocalState q)
          rw [hold]
          omega
      | won =>
          change (0 : Nat) + 1 ≤
            bankTrialDurationLeaseAwareWorkerRemaining
              (⟨B, .live begun⟩ : BankTrialLocalState q)
          rw [hold]
          omega
      | lost =>
          change (0 : Nat) + 1 ≤
            bankTrialDurationLeaseAwareWorkerRemaining
              (⟨B, .live begun⟩ : BankTrialLocalState q)
          rw [hold]
          omega

/-- Strict original-clock lease-aware class-one progress on an
interior IR forward service. -/
theorem bankTrialDurationSelectedIRLeaseAwareDrop {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .IR)
    (hdst : (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .E) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)) + 1 ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  exact bankTrialDurationSelectedInteriorLeaseAwareDropOfMaximum
    ring root hw B begun hf (Or.inl hm) j hj
    (bankTrialDurationSelectedIRMaximumDrop
      ring root hw B hf hc j hj hsrc hdst)

/-- Strict original-clock lease-aware class-one progress on an
interior AL return service. -/
theorem bankTrialDurationSelectedALLeaseAwareDrop {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .E)
    (hdst : (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .AL) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)) + 1 ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  exact bankTrialDurationSelectedInteriorLeaseAwareDropOfMaximum
    ring root hw B begun hf (Or.inl hm) j hj
    (bankTrialDurationSelectedALMaximumDrop
      ring root hw B hf hc j hj hsrc hdst)

/-- Strict original-clock lease-aware class-one progress on an
interior CR0/CR1 comparison service. -/
theorem bankTrialDurationSelectedCRLeaseAwareDrop {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .CWAIT)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .CR0 ∨
      (B.fields ⟨j.val, by omega⟩).2.2.1 = .CR1)
    (hdst : (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .E) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)) + 1 ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  exact bankTrialDurationSelectedInteriorLeaseAwareDropOfMaximum
    ring root hw B begun hf (Or.inr hm) j hj
    (bankTrialDurationSelectedCRMaximumDrop
      ring root hw B hf hc j hj hsrc hdst)

/-- Strict original-clock lease-aware class-one progress on an
interior CL0/CL1 reverse comparison service. -/
theorem bankTrialDurationSelectedCLLeaseAwareDrop {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .CWAIT)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .E)
    (hdst : (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .CL0 ∨
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .CL1) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)) + 1 ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  exact bankTrialDurationSelectedInteriorLeaseAwareDropOfMaximum
    ring root hw B begun hf (Or.inr hm) j hj
    (bankTrialDurationSelectedCLMaximumDrop
      ring root hw B hf hc j hj hsrc hdst)

/-- An observer can only decrease the lease-aware worker cost
relative to treating the same postservice BANK as still LIVE.
This covers RECOVERY, WON, and LOST without conflating them. -/
theorem bankTrialDurationLeaseAwareNextLeLiveReference {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B e, .live begun⟩ : BankTrialLocalState q) := by
  have hbank := bankTrialLocalNextLiveBank ring root e B begun
  cases hnext : bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) e with
  | mk C phase =>
      have hbankEq :
          C = GrantBankReference.bankLocalReferenceStepClamped
            ring root B e := by
        rw [hnext] at hbank
        exact hbank
      cases phase with
      | live nextBegun =>
          change bankTrialDurationLeaseAwareWorkerRemaining
              (⟨C, .live nextBegun⟩ : BankTrialLocalState q) ≤
            bankTrialDurationLeaseAwareWorkerRemaining
              (⟨GrantBankReference.bankLocalReferenceStepClamped
                ring root B e, .live begun⟩ : BankTrialLocalState q)
          rw [hbankEq] <;> exact Nat.le_refl _
      | recovery =>
          change (0 : Nat) ≤
            bankTrialDurationLeaseAwareWorkerRemaining
              (⟨GrantBankReference.bankLocalReferenceStepClamped
                ring root B e, .live begun⟩ : BankTrialLocalState q)
          exact Nat.zero_le _
      | won =>
          change (0 : Nat) ≤
            bankTrialDurationLeaseAwareWorkerRemaining
              (⟨GrantBankReference.bankLocalReferenceStepClamped
                ring root B e, .live begun⟩ : BankTrialLocalState q)
          exact Nat.zero_le _
      | lost =>
          change (0 : Nat) ≤
            bankTrialDurationLeaseAwareWorkerRemaining
              (⟨GrantBankReference.bankLocalReferenceStepClamped
                ring root B e, .live begun⟩ : BankTrialLocalState q)
          exact Nat.zero_le _

/-- A reference-level weak row implies the actual original-clock
observer inequality, regardless of the postservice phase. -/
theorem bankTrialDurationLeaseAwareNextWeakOfReference {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hrow :
      bankTrialDurationLeaseAwareWorkerRemaining
        (⟨GrantBankReference.bankLocalReferenceStepClamped
          ring root B e, .live begun⟩ : BankTrialLocalState q) ≤
      bankTrialDurationLeaseAwareWorkerRemaining
        (⟨B, .live begun⟩ : BankTrialLocalState q)) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  exact Nat.le_trans
    (bankTrialDurationLeaseAwareNextLeLiveReference
      ring root e B begun) hrow

/-- Every scheduler edge outside Counter.Support is a genuine
weak lease-aware worker row, with no spatial assumption. -/
theorem bankTrialDurationLeaseAwareOutsideWeak {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hout : ¬ Counter.Support q ring root e) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  apply bankTrialDurationLeaseAwareNextWeakOfReference
    ring root e B begun
  rw [bankTrialLiveCarryUnsupportedRawFrame
    ring root e B hout] <;> exact Nat.le_refl _


/-- The four certified forward/return service classes for
IWAIT and CWAIT at one genuine protected interior source. -/
def BankTrialDurationSelectedInteriorCondition {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) : Prop :=
  (bankTrialLiveWaveRootMode B = .IWAIT ∧
    (((B.fields ⟨j.val, by omega⟩).2.2.1 = .IR ∧
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .E) ∨
     ((B.fields ⟨j.val, by omega⟩).2.2.1 = .E ∧
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .AL))) ∨
  (bankTrialLiveWaveRootMode B = .CWAIT ∧
    ((((B.fields ⟨j.val, by omega⟩).2.2.1 = .CR0 ∨
        (B.fields ⟨j.val, by omega⟩).2.2.1 = .CR1) ∧
       (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .E) ∨
     ((B.fields ⟨j.val, by omega⟩).2.2.1 = .E ∧
       ((B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .CL0 ∨
        (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .CL1))))

/-- One of the four selected interior types supplies an actual
nominated original scheduler letter, not an abstract two-slot step. -/
theorem bankTrialDurationSelectedInteriorNomination {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hselected : BankTrialDurationSelectedInteriorCondition B j) :
    ∃ chosen : Fin n,
      bankTrialDurationLeaseAwareWorkerRemaining
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) chosen) + 1 ≤
      bankTrialDurationLeaseAwareWorkerRemaining
        (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  refine ⟨Counter.site ring root j.val, ?_⟩
  unfold BankTrialDurationSelectedInteriorCondition at hselected
  rcases hselected with hiwait | hcwait
  · obtain ⟨hm, hcase⟩ := hiwait
    rcases hcase with ⟨hsrc, hdst⟩ | ⟨hsrc, hdst⟩
    · exact bankTrialDurationSelectedIRLeaseAwareDrop
        ring root hw B begun hf hc hm j hj hsrc hdst
    · exact bankTrialDurationSelectedALLeaseAwareDrop
        ring root hw B begun hf hc hm j hj hsrc hdst
  · obtain ⟨hm, hcase⟩ := hcwait
    rcases hcase with ⟨hsrc, hdst⟩ | ⟨hsrc, hdst⟩
    · exact bankTrialDurationSelectedCRLeaseAwareDrop
        ring root hw B begun hf hc hm j hj hsrc hdst
    · exact bankTrialDurationSelectedCLLeaseAwareDrop
        ring root hw B begun hf hc hm j hj hsrc hdst

/-- A strict nominated physical service not covered by the four ordinary
interior IR/AL/CR/CL cases.  The last alternative is the genuinely
interior top turn (source b-1, responder b); it must not be confused
with the top-boundary service whose source is b.  Only old pair-local
source/destination tokens enter that new alternative. -/
def BankTrialDurationOtherNominatedEdge {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool) : Prop :=
  ∃ e : Fin n,
    (e = root ∨ ring.rightNeighbor e = root ∨
      e = Counter.site ring root (compileAdvice q).b ∨
      (bankTrialLiveWaveRootMode B = .RWAIT ∧
        Counter.Support q ring root e) ∨
      (e = Counter.site ring root ((compileAdvice q).b - 1) ∧
        (B.fields ⟨(compileAdvice q).b - 1, by omega⟩).2.2.1 = .E ∧
        ((bankTrialLiveWaveRootMode B = .IWAIT ∧
          (B.fields ⟨(compileAdvice q).b, by omega⟩).2.2.1 = .IR) ∨
         (bankTrialLiveWaveRootMode B = .CWAIT ∧
          ((B.fields ⟨(compileAdvice q).b, by omega⟩).2.2.1 = .CR0 ∨
           (B.fields ⟨(compileAdvice q).b, by omega⟩).2.2.1 = .CR1))))) ∧
    bankTrialDurationLeaseAwareWorkerRemaining
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e) + 1 ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q)

/-- Explicit residual service-coverage obligation. The four
interior cases can be discharged above; all other nominated
physical services are isolated by OtherNominatedEdge. -/
def BankTrialDurationClassOneServiceCoverage {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
        (compileAdvice q).b),
    BankTrialLocalClean q S →
    ∀ (B : GrantBankReference.BankLocalReference
        (compileAdvice q).b) (begun : Bool),
      BankTrialDurationReachable ring root S
        (⟨B, .live begun⟩ : BankTrialLocalState q) →
      bankTrialDurationLeaseAwareClass
        (⟨B, .live begun⟩ : BankTrialLocalState q) = 1 →
      (∃ j : Fin (compileAdvice q).b,
        0 < j.val ∧ BankTrialDurationSelectedInteriorCondition B j) ∨
      BankTrialDurationOtherNominatedEdge ring root B begun

/-- The reachable unique-worker lock authenticates whichever
interior service the coverage premise selects. -/
theorem bankTrialDurationClassOneCoveredNomination {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hcover : BankTrialDurationClassOneServiceCoverage
      (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hreach : BankTrialDurationReachable ring root S
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hclass : bankTrialDurationLeaseAwareClass
      (⟨B, .live begun⟩ : BankTrialLocalState q) = 1) :
    ∃ chosen : Fin n,
      bankTrialDurationLeaseAwareWorkerRemaining
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) chosen) + 1 ≤
      bankTrialDurationLeaseAwareWorkerRemaining
        (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  rcases hcover S hclean B begun hreach hclass with
    ⟨j, hj, hselected⟩ | hother
  · obtain ⟨word, hword⟩ := hreach
    have hphase :
        (bankTrialLocalRun ring root word
          (bankTrialLocalStart S)).phase = .live begun := by
      rw [hword]
    have hc := (bankTrialWindowLockedCleanWords
      ring root hw S hclean word).1 begun hphase
    rw [hword] at hc
    have hf := bankTrialProbabilityCleanLiveUnlatched
      ring root S hclean word B begun hword
    exact bankTrialDurationSelectedInteriorNomination
      ring root hw B begun hf hc j hj hselected
  · obtain ⟨chosen, _, hstrict⟩ := hother
    exact ⟨chosen, hstrict⟩

/-- The remaining raw all-edge weak owner contract, evaluated
at the genuine updated reference but provisionally kept LIVE.
The phase-transfer theorem above handles RECOVERY/WON/LOST. -/
def BankTrialDurationClassOneReferenceWeakRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
        (compileAdvice q).b),
    BankTrialLocalClean q S →
    ∀ (B : GrantBankReference.BankLocalReference
        (compileAdvice q).b) (begun : Bool),
      BankTrialDurationReachable ring root S
        (⟨B, .live begun⟩ : BankTrialLocalState q) →
      bankTrialDurationLeaseAwareClass
        (⟨B, .live begun⟩ : BankTrialLocalState q) = 1 →
      ∀ e : Fin n,
        bankTrialDurationLeaseAwareWorkerRemaining
          (⟨GrantBankReference.bankLocalReferenceStepClamped
            ring root B e, .live begun⟩ : BankTrialLocalState q) ≤
        bankTrialDurationLeaseAwareWorkerRemaining
          (⟨B, .live begun⟩ : BankTrialLocalState q)

/-- Conditional assembly of the full lease-aware edge rows.
Only two raw row obligations remain: all-edge weak monotonicity
and existence of an actual nominated service beyond the four
interior cases. Class zero and orphan class two are discharged
by the earlier theorems. Nonalias is explicit. -/
theorem bankTrialDurationLeaseAwareRowsOfWeakAndServiceCoverage
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hweak : BankTrialDurationClassOneReferenceWeakRows
      (q := q) ring root)
    (hcover : BankTrialDurationClassOneServiceCoverage
      (q := q) ring root) :
    BankTrialDurationLeaseAwareWorkerRankEdgeRows
      (q := q) ring root := by
  apply bankTrialDurationLeaseAwareRowsOfWorkerAndOrphan ring root
  · intro S hclean z hreach hnot hclass
    cases z with
    | mk B phase =>
        cases phase with
        | live begun =>
            constructor
            · intro e
              exact bankTrialDurationLeaseAwareNextWeakOfReference
                ring root e B begun
                (hweak S hclean B begun hreach hclass e)
            · exact bankTrialDurationClassOneCoveredNomination
                ring root hw hcover S hclean B begun hreach hclass
        | recovery =>
            change (2 : Nat) = 1 at hclass
            omega
        | won =>
            change (2 : Nat) = 1 at hclass
            omega
        | lost =>
            change (2 : Nat) = 1 at hclass
            omega
  · exact bankTrialDurationLeaseAwareOrphanOfReferenceRows
      ring root hw (bankTrialDurationOrphanReferenceRows ring root)


/-- In class one an ARMED root is impossible: the ARMED
branch is exactly class zero. -/
theorem bankTrialDurationClassOneNotArmed {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun : Bool)
    (hclass : bankTrialDurationLeaseAwareClass
      (⟨B, .live begun⟩ : BankTrialLocalState q) = 1) :
    bankTrialLiveWaveRootMode B ≠ .ARMED := by
  intro hm
  change
    (if bankTrialLiveWaveRootMode B = .ARMED then 0
     else if
       ((bankTrialLiveWaveRootMode B = .IWAIT ∨
         bankTrialLiveWaveRootMode B = .CWAIT) ∧
        bankTrialDurationWorkerTokenMaximum B = 0)
     then 2 else 1) = 1 at hclass
  rw [if_pos hm] at hclass
  omega

/-- The only class-one LIVE modes under the no-RESET invariant:
CSTART, RWAIT, or IWAIT/CWAIT with a nonzero worker maximum.
This isolates the source cases whose all-edge weak rows remain. -/
theorem bankTrialDurationClassOneModeCases {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun : Bool)
    (hclass : bankTrialDurationLeaseAwareClass
      (⟨B, .live begun⟩ : BankTrialLocalState q) = 1)
    (hnreset : bankTrialLiveWaveRootMode B ≠ .RESET) :
    bankTrialLiveWaveRootMode B = .CSTART ∨
    bankTrialLiveWaveRootMode B = .RWAIT ∨
    ((bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT) ∧
      0 < bankTrialDurationWorkerTokenMaximum B) := by
  have hnarmed := bankTrialDurationClassOneNotArmed B begun hclass
  cases hm : bankTrialLiveWaveRootMode B with
  | RESET =>
      exact False.elim (hnreset hm)
  | ARMED =>
      exact False.elim (hnarmed hm)
  | RWAIT =>
      exact Or.inr (Or.inl rfl)
  | IWAIT =>
      have hp : 0 < bankTrialDurationWorkerTokenMaximum B := by
        by_cases hz : bankTrialDurationWorkerTokenMaximum B = 0
        · have htwo := bankTrialDurationLeaseAwareOrphanClass
            B begun (Or.inl hm) hz
          rw [htwo] at hclass
          omega
        · exact Nat.pos_of_ne_zero hz
      exact Or.inr (Or.inr ⟨Or.inl rfl, hp⟩)
  | CSTART =>
      exact Or.inl rfl
  | CWAIT =>
      have hp : 0 < bankTrialDurationWorkerTokenMaximum B := by
        by_cases hz : bankTrialDurationWorkerTokenMaximum B = 0
        · have htwo := bankTrialDurationLeaseAwareOrphanClass
            B begun (Or.inr hm) hz
          rw [htwo] at hclass
          omega
        · exact Nat.pos_of_ne_zero hz
      exact Or.inr (Or.inr ⟨Or.inr rfl, hp⟩)

/-- The CLEAN-reachable class-one observer satisfies the
trichotomy, using the same nonalias condition as the live lock. -/
theorem bankTrialDurationClassOneReachableModeCases {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun : Bool)
    (hreach : BankTrialDurationReachable ring root S
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hclass : bankTrialDurationLeaseAwareClass
      (⟨B, .live begun⟩ : BankTrialLocalState q) = 1) :
    bankTrialLiveWaveRootMode B = .CSTART ∨
    bankTrialLiveWaveRootMode B = .RWAIT ∨
    ((bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT) ∧
      0 < bankTrialDurationWorkerTokenMaximum B) := by
  obtain ⟨word, hword⟩ := hreach
  have hphase :
      (bankTrialLocalRun ring root word
        (bankTrialLocalStart S)).phase = .live begun := by
    rw [hword]
  have hnot := (bankTrialWindowLockedCleanWords
    ring root hw S hclean word).2 begun hphase
  rw [hword] at hnot
  exact bankTrialDurationClassOneModeCases B begun hclass hnot


/-- A LIVE waiting wave with a real worker has weak progress on
any edge whose reference token maximum does not increase and
whose LIVE successor retains the old waiting root mode.
Non-LIVE postservice phases have zero lease-aware worker cost. -/
theorem bankTrialDurationWaitWorkerNextWeakOfMaximum {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hp : 0 < bankTrialDurationWorkerTokenMaximum B)
    (hmaximum :
      bankTrialDurationWorkerTokenMaximum
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) ≤
      bankTrialDurationWorkerTokenMaximum B)
    (hliveMode : ∀ nextBegun : Bool,
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase =
        .live nextBegun →
      bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) = bankTrialLiveWaveRootMode B) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  have hold := bankTrialDurationLeaseAwareWaitWorkerExact
    B begun hm hp
  have hbank := bankTrialLocalNextLiveBank ring root e B begun
  cases hnext : bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) e with
  | mk C phase =>
      have hbankEq :
          C = GrantBankReference.bankLocalReferenceStepClamped
            ring root B e := by
        rw [hnext] at hbank
        exact hbank
      have hmax :
          bankTrialDurationWorkerTokenMaximum C ≤
            bankTrialDurationWorkerTokenMaximum B := by
        rw [hbankEq]
        exact hmaximum
      cases phase with
      | live nextBegun =>
          have hphase :
              (bankTrialLocalNext ring root
                (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase =
                  .live nextBegun := by
            rw [hnext]
          have hmodeSame := hliveMode nextBegun hphase
          have hmnew :
              bankTrialLiveWaveRootMode C = .IWAIT ∨
              bankTrialLiveWaveRootMode C = .CWAIT := by
            rw [hbankEq, hmodeSame]
            exact hm
          have hle := bankTrialDurationLeaseAwareWaitWorkerLeMaximum
            C nextBegun hmnew
          change bankTrialDurationLeaseAwareWorkerRemaining
              (⟨C, .live nextBegun⟩ : BankTrialLocalState q) ≤
            bankTrialDurationLeaseAwareWorkerRemaining
              (⟨B, .live begun⟩ : BankTrialLocalState q)
          rw [hold]
          omega
      | recovery =>
          change (0 : Nat) ≤
            bankTrialDurationLeaseAwareWorkerRemaining
              (⟨B, .live begun⟩ : BankTrialLocalState q)
          exact Nat.zero_le _
      | won =>
          change (0 : Nat) ≤
            bankTrialDurationLeaseAwareWorkerRemaining
              (⟨B, .live begun⟩ : BankTrialLocalState q)
          exact Nat.zero_le _
      | lost =>
          change (0 : Nat) ≤
            bankTrialDurationLeaseAwareWorkerRemaining
              (⟨B, .live begun⟩ : BankTrialLocalState q)
          exact Nat.zero_le _

/-- Exact source-level top row: the only selected reference
field is the top field. Other fields are frames under nonalias. -/
theorem bankTrialDurationTopFieldsRow {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root (compileAdvice q).b)).fields =
      (fun i : Fin ((compileAdvice q).b + 1) =>
        if i.val = (compileAdvice q).b then
          GrantBankReference.bankLocalReferenceClampedQuad q
            (GrantBankReference.topBoundaryBankMap
              (GrantBankReference.bankLocalReferenceCell B i))
        else B.fields i) := by
  funext i
  have hs : Counter.Support q ring root
      (Counter.site ring root (compileAdvice q).b) :=
    Or.inr ⟨(compileAdvice q).b, by omega, rfl⟩
  by_cases ht : i.val = (compileAdvice q).b
  · have hx : ¬ (i.val < (compileAdvice q).b ∧
        Counter.site ring root (compileAdvice q).b =
          Counter.site ring root i.val) := by
      intro h
      omega
    have hy : ¬ (0 < i.val ∧
        Counter.site ring root (compileAdvice q).b =
          Counter.site ring root (i.val - 1)) := by
      intro h
      have hv := bankTrialWindowSitesDistinct ring root hw
        (compileAdvice q).b (i.val - 1)
        (by omega) (by omega) h.2
      omega
    rw [bankTrialLiveCarryTopSelected ring root
      (Counter.site ring root (compileAdvice q).b) B hs hf
      i hx hy ⟨ht, rfl⟩]
    rw [if_pos ht]
  · have hx : ¬ (i.val < (compileAdvice q).b ∧
        Counter.site ring root (compileAdvice q).b =
          Counter.site ring root i.val) := by
      intro h
      have hv := bankTrialWindowSitesDistinct ring root hw
        (compileAdvice q).b i.val
        (by omega) (by omega) h.2
      exact ht hv.symm
    have hy : ¬ (0 < i.val ∧
        Counter.site ring root (compileAdvice q).b =
          Counter.site ring root (i.val - 1)) := by
      intro h
      have hv := bankTrialWindowSitesDistinct ring root hw
        (compileAdvice q).b (i.val - 1)
        (by omega) (by omega) h.2
      have hi := i.isLt
      omega
    have htop : ¬ (i.val = (compileAdvice q).b ∧
        Counter.site ring root (compileAdvice q).b =
          Counter.site ring root (compileAdvice q).b) := by
      intro h
      exact ht h.1
    have hin : ¬ (i.val = 0 ∧
        ring.rightNeighbor
          (Counter.site ring root (compileAdvice q).b) = root) := by
      intro h
      have he :
          Counter.site ring root ((compileAdvice q).b + 1) =
          Counter.site ring root 0 := h.2
      have hv := bankTrialWindowSitesDistinct ring root hw
        ((compileAdvice q).b + 1) 0 (by omega) (by omega) he
      omega
    rw [bankTrialLiveCarryUnselectedField ring root
      (Counter.site ring root (compileAdvice q).b)
      B hs hf i hx hy htop hin]
    rw [if_neg ht]

/-- A top service frames the root mode, independently of any
token or the old waiting mode. -/
theorem bankTrialDurationTopRootModeFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false) :
    bankTrialLiveWaveRootMode
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root (compileAdvice q).b)) =
      bankTrialLiveWaveRootMode B := by
  have hfields := bankTrialDurationTopFieldsRow ring root hw B hf
  change
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root (compileAdvice q).b)).fields
        ⟨0, by omega⟩).1 = (B.fields ⟨0, by omega⟩).1
  rw [hfields]
  have hn : (0 : Nat) ≠ (compileAdvice q).b := by
    have hb := bankTrialWindowWidthPos q
    omega
  simp [hn]

/-- Every protected token rank is nonincreasing on a genuine
top service. The only non-frame index uses the top erasure row. -/
theorem bankTrialDurationTopMaximumWeak {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false) :
    bankTrialDurationWorkerTokenMaximum
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root (compileAdvice q).b)) ≤
      bankTrialDurationWorkerTokenMaximum B := by
  apply bankTrialDurationWorkerMaximumMono
  intro k
  have hfields := bankTrialDurationTopFieldsRow ring root hw B hf
  change bankTrialDurationWorkerTokenRank (compileAdvice q).b
      (k.val + 1)
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root (compileAdvice q).b)).fields
        ⟨k.val + 1, by omega⟩).2.2.1 ≤
    bankTrialDurationWorkerTokenRank (compileAdvice q).b
      (k.val + 1) (B.fields ⟨k.val + 1, by omega⟩).2.2.1
  rw [hfields]
  by_cases ht : k.val + 1 = (compileAdvice q).b
  · simp only [Fin.val_mk, if_pos ht]
    rw [(bankTrialLiveClampBitToken q
      (GrantBankReference.topBoundaryBankMap
        (GrantBankReference.bankLocalReferenceCell B
          ⟨k.val + 1, by omega⟩))).2]
    change bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (k.val + 1)
        (GrantBankReference.topBoundaryBankMap
          (GrantBankReference.bankLocalReferenceCell B
            ⟨k.val + 1, by omega⟩)).tok ≤
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (k.val + 1)
        (GrantBankReference.bankLocalReferenceCell B
          ⟨k.val + 1, by omega⟩).tok
    calc
      _ = bankTrialDurationWorkerTokenRank (compileAdvice q).b
          (compileAdvice q).b
          (GrantBankReference.topBoundaryBankMap
            (GrantBankReference.bankLocalReferenceCell B
              ⟨k.val + 1, by omega⟩)).tok :=
        congrArg (fun x : Nat =>
          bankTrialDurationWorkerTokenRank (compileAdvice q).b x
            (GrantBankReference.topBoundaryBankMap
              (GrantBankReference.bankLocalReferenceCell B
                ⟨k.val + 1, by omega⟩)).tok) ht
      _ ≤ bankTrialDurationWorkerTokenRank (compileAdvice q).b
          (compileAdvice q).b
          (GrantBankReference.bankLocalReferenceCell B
            ⟨k.val + 1, by omega⟩).tok :=
        bankTrialDurationTopTokenRankNonincrease
          (compileAdvice q).b
          (GrantBankReference.bankLocalReferenceCell B
            ⟨k.val + 1, by omega⟩)
      _ = _ := congrArg (fun x : Nat =>
        bankTrialDurationWorkerTokenRank (compileAdvice q).b x
          (GrantBankReference.bankLocalReferenceCell B
            ⟨k.val + 1, by omega⟩).tok) ht.symm
  · simpa only [Fin.val_mk, if_neg ht] using
      (Nat.le_refl (bankTrialDurationWorkerTokenRank
        (compileAdvice q).b (k.val + 1)
        (B.fields ⟨k.val + 1, by omega⟩).2.2.1))

/-- A top edge is weakly nonincreasing on IWAIT/CWAIT with a
real worker, including exits to RECOVERY/WON/LOST. -/
theorem bankTrialDurationTopWaitWorkerWeak {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hp : 0 < bankTrialDurationWorkerTokenMaximum B) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root (compileAdvice q).b)) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  apply bankTrialDurationWaitWorkerNextWeakOfMaximum
    ring root (Counter.site ring root (compileAdvice q).b)
    B begun hm hp
  · exact bankTrialDurationTopMaximumWeak ring root hw B hf
  · intro nextBegun _
    exact bankTrialDurationTopRootModeFrame ring root hw B hf

/-- A successor reported as LIVE cannot have its updated root in
RESET: that branch of the observer is RECOVERY, not LIVE. -/
theorem bankTrialDurationNextLiveNonreset {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun nextBegun : Bool)
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase =
        .live nextBegun) :
    bankTrialLiveWaveRootMode
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) ≠ .RESET := by
  classical
  intro hreset
  have hr :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨0, by have := bankTrialWindowWidthPos q; omega⟩).1 = .RESET :=
    hreset
  by_cases hwin :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).success = true
  · simp [bankTrialLocalNext, hwin] at hnext
  · by_cases hclean :
        BankTrialLocalClean q
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B e) ∧
        (begun = true ∨ e = root ∨ ring.rightNeighbor e = root)
    · simp [bankTrialLocalNext, hwin, hclean] at hnext
    · have hzero : (0 : Fin ((compileAdvice q).b + 1)) =
          ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ := Fin.ext rfl
      rw [← hzero] at hr
      simp [bankTrialLocalNext, hwin, hclean, hr] at hnext

/-- Incoming-root service cannot alias any of the protected
source/responder/top selectors when b+2 <= n. -/
theorem bankTrialDurationIncomingFieldsRow {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hin : ring.rightNeighbor e = root)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields =
        (fun i : Fin ((compileAdvice q).b + 1) =>
          if i.val = 0 then
            GrantBankReference.bankLocalReferenceClampedQuad q
              (GrantBankReference.incomingRootBankMap
                (GrantBankReference.bankLocalReferenceCell B i))
          else B.fields i) := by
  funext i
  have hs : Counter.Support q ring root e := Or.inl hin
  by_cases hz : i.val = 0
  · have hx : ¬ (i.val < (compileAdvice q).b ∧
        e = Counter.site ring root i.val) := by
      intro h
      have he : Counter.site ring root 1 =
          Counter.site ring root 0 := by
        have he0 : e = root := by
          simpa [Counter.site, hz] using h.2
        rw [he0] at hin
        exact hin
      have hv := bankTrialWindowSitesDistinct ring root hw
        1 0 (by omega) (by omega) he
      omega
    have hy : ¬ (0 < i.val ∧
        e = Counter.site ring root (i.val - 1)) := by
      intro h
      omega
    have ht : ¬ (i.val = (compileAdvice q).b ∧
        e = Counter.site ring root (compileAdvice q).b) := by
      intro h
      have hb : 0 < (compileAdvice q).b := by
        change 0 < (compileAdvice q).s + 11
        omega
      omega
    rw [bankTrialLiveCarryIncomingSelected ring root
      e B hs hf i hx hy ht ⟨hz, hin⟩]
    change GrantBankReference.bankLocalReferenceClampedQuad q
        (GrantBankReference.incomingRootBankMap
          (GrantBankReference.bankLocalReferenceCell B i)) =
      (if i.val = 0 then
        GrantBankReference.bankLocalReferenceClampedQuad q
          (GrantBankReference.incomingRootBankMap
            (GrantBankReference.bankLocalReferenceCell B i))
       else B.fields i)
    rw [if_pos hz]
  · have hx : ¬ (i.val < (compileAdvice q).b ∧
        e = Counter.site ring root i.val) := by
      intro h
      have he : Counter.site ring root (i.val + 1) =
          Counter.site ring root 0 := by
        change ring.rightNeighbor (Counter.site ring root i.val) =
          root
        rw [← h.2]
        exact hin
      have hv := bankTrialWindowSitesDistinct ring root hw
        (i.val + 1) 0 (by
          have hi := i.isLt
          omega) (by omega) he
      omega
    have hy : ¬ (0 < i.val ∧
        e = Counter.site ring root (i.val - 1)) := by
      intro h
      have he : Counter.site ring root i.val =
          Counter.site ring root 0 := by
        have hsuc : i.val - 1 + 1 = i.val := by omega
        rw [← hsuc]
        change ring.rightNeighbor
          (Counter.site ring root (i.val - 1)) = root
        rw [← h.2]
        exact hin
      have hv := bankTrialWindowSitesDistinct ring root hw
        i.val 0 (by omega) (by omega) he
      omega
    have ht : ¬ (i.val = (compileAdvice q).b ∧
        e = Counter.site ring root (compileAdvice q).b) := by
      intro h
      have he : Counter.site ring root ((compileAdvice q).b + 1) =
          Counter.site ring root 0 := by
        change ring.rightNeighbor
          (Counter.site ring root (compileAdvice q).b) = root
        rw [← h.2]
        exact hin
      have hv := bankTrialWindowSitesDistinct ring root hw
        ((compileAdvice q).b + 1) 0 (by omega) (by omega) he
      omega
    have hr : ¬ (i.val = 0 ∧ ring.rightNeighbor e = root) := by
      intro h
      exact hz h.1
    rw [bankTrialLiveCarryUnselectedField ring root
      e B hs hf i hx hy ht hr]
    change B.fields i =
      (if i.val = 0 then
        GrantBankReference.bankLocalReferenceClampedQuad q
          (GrantBankReference.incomingRootBankMap
            (GrantBankReference.bankLocalReferenceCell B i))
       else B.fields i)
    rw [if_neg hz]


/-- Equality of the entire protected token vector implies equality
of the actual fold-maximum, regardless of mode or success latch. -/
theorem bankTrialDurationMaximumTokenCongr {q : Nat}
    (A B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (htokens : ∀ k : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken A k = bankTrialLiveWaveToken B k) :
    bankTrialDurationWorkerTokenMaximum A =
      bankTrialDurationWorkerTokenMaximum B := by
  apply Nat.le_antisymm
  · apply bankTrialDurationWorkerMaximumMono
    intro k
    rw [htokens k] <;> exact Nat.le_refl _
  · apply bankTrialDurationWorkerMaximumMono
    intro k
    rw [← htokens k] <;> exact Nat.le_refl _

/-- An incoming-root edge frames every protected worker token,
not merely the scalar potential. Nonalias excludes incoming
simultaneously selecting a protected internal owner. -/
theorem bankTrialDurationIncomingMaximumFrame {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hin : ring.rightNeighbor e = root)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false) :
    bankTrialDurationWorkerTokenMaximum
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) =
    bankTrialDurationWorkerTokenMaximum B := by
  apply bankTrialDurationMaximumTokenCongr
  intro k
  have hfields := bankTrialDurationIncomingFieldsRow
    ring root e hw hin B hf
  change
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨k.val + 1, by omega⟩).2.2.1 =
    (B.fields ⟨k.val + 1, by omega⟩).2.2.1
  rw [hfields]
  have hn : k.val + 1 ≠ 0 := by omega
  simpa only [Fin.val_mk, if_neg hn]

/-- An incoming-root service of a waiting root either leaves its
mode unchanged or sets RESET. The top/internals cannot alias
that incoming letter under nonalias. -/
theorem bankTrialDurationIncomingWaitModeCases {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hin : ring.rightNeighbor e = root)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT) :
    bankTrialLiveWaveRootMode
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) = bankTrialLiveWaveRootMode B ∨
    bankTrialLiveWaveRootMode
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) = .RESET := by
  have hfields := bankTrialDurationIncomingFieldsRow
    ring root e hw hin B hf
  have hraw := (bankTrialDurationOrphanRawIncoming
    (GrantBankReference.bankLocalReferenceCell B
      ⟨0, by omega⟩) hm).2
  have hmode :
      bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) =
      (GrantBankReference.incomingRootBankMap
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by omega⟩)).mode := by
    change
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨0, by omega⟩).1 =
      (GrantBankReference.incomingRootBankMap
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by omega⟩)).mode
    rw [hfields]
    simp [GrantBankReference.bankLocalReferenceClampedQuad,
      GrantBankReference.bankAgentLeaseQuad, copyBank]
  rcases hraw with hsame | hreset
  · exact Or.inl (hmode.trans hsame)
  · exact Or.inr (hmode.trans hreset)

/-- Weak class-one progress on the genuine incoming-root edge
for IWAIT/CWAIT with a real worker. A RESET result is not LIVE
and therefore costs zero on the actual observer phase. -/
theorem bankTrialDurationIncomingWaitWorkerWeak {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hin : ring.rightNeighbor e = root)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hp : 0 < bankTrialDurationWorkerTokenMaximum B) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  apply bankTrialDurationWaitWorkerNextWeakOfMaximum
    ring root e B begun hm hp
  · rw [bankTrialDurationIncomingMaximumFrame
      ring root e hw hin B hf]
    exact Nat.le_refl _
  · intro nextBegun hnext
    rcases bankTrialDurationIncomingWaitModeCases
      ring root e hw hin B hf hm with hsame | hreset
    · exact hsame
    · exact False.elim ((bankTrialDurationNextLiveNonreset
        ring root e B begun nextBegun hnext) hreset)

/-- The only digit altered on a root outgoing edge is digit one.
This is a statement about the literal clamped reference fields,
not the physical configuration's function representation. -/
theorem bankTrialDurationRootFieldsRow {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B root).fields =
        (fun i : Fin ((compileAdvice q).b + 1) =>
          if i.val = 0 then
            GrantBankReference.bankLocalReferenceClampedQuad q
              ((GrantBankReference.bankLocalReferenceInternalPair q B
                ⟨0, bankTrialWindowWidthPos q⟩).1)
          else if i.val = 1 then
            GrantBankReference.bankLocalReferenceClampedQuad q
              ((GrantBankReference.bankLocalReferenceInternalPair q B
                ⟨0, bankTrialWindowWidthPos q⟩).2)
          else B.fields i) := by
  funext i
  have hs : Counter.Support q ring root root :=
    Or.inr ⟨0, Nat.zero_le _, rfl⟩
  have hn : 2 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    omega
  by_cases hz : i.val = 0
  · have heq : i = ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ := Fin.ext hz
    rw [heq, bankTrialLocalStepField ring root root B hs hf,
      bankTrialLocalFieldRootOutgoing ring root B]
    simp
  · by_cases ho : i.val = 1
    · have heq : i = ⟨1, by omega⟩ := Fin.ext ho
      rw [heq, bankTrialLocalStepField ring root root B hs hf,
        bankTrialLocalFieldOneOutgoing ring root hn B]
      simp
    · have hx : ¬ (i.val < (compileAdvice q).b ∧
          root = Counter.site ring root i.val) := by
        intro h
        have hv := bankTrialWindowSitesDistinct ring root hw
          0 i.val (by omega) (by omega) h.2
        omega
      have hy : ¬ (0 < i.val ∧
          root = Counter.site ring root (i.val - 1)) := by
        intro h
        have hv := bankTrialWindowSitesDistinct ring root hw
          0 (i.val - 1) (by omega) (by omega) h.2
        omega
      have ht : ¬ (i.val = (compileAdvice q).b ∧
          root = Counter.site ring root (compileAdvice q).b) := by
        intro h
        have hv := bankTrialWindowSitesDistinct ring root hw
          0 (compileAdvice q).b (by omega) (by omega) h.2
        have hb : 0 < (compileAdvice q).b := by
          change 0 < (compileAdvice q).s + 11
          omega
        omega
      have hr : ¬ (i.val = 0 ∧
          ring.rightNeighbor root = root) := by
        intro h
        exact hz h.1
      rw [bankTrialLiveCarryUnselectedField ring root root
        B hs hf i hx hy ht hr]
      change B.fields i =
        (if i.val = 0 then
          GrantBankReference.bankLocalReferenceClampedQuad q
            (GrantBankReference.bankLocalReferenceInternalPair q B ⟨0, by omega⟩).1
         else if i.val = 1 then
          GrantBankReference.bankLocalReferenceClampedQuad q
            (GrantBankReference.bankLocalReferenceInternalPair q B ⟨0, by omega⟩).2
         else B.fields i)
      rw [if_neg hz, if_neg ho]

/-- With an empty first digit, outgoing-root IWAIT/CWAIT leaves
the complete worker maximum unchanged even when the root lease
expires. All other protected digits are exact frames. -/
theorem bankTrialDurationRootWaitEmptyMaximumFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hfirst : bankTrialLiveWaveToken B
      ⟨0, bankTrialWindowWidthPos q⟩ = .E) :
    bankTrialDurationWorkerTokenMaximum
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root) =
    bankTrialDurationWorkerTokenMaximum B := by
  apply bankTrialDurationMaximumTokenCongr
  intro k
  have hfields := bankTrialDurationRootFieldsRow ring root hw B hf
  change
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B root).fields ⟨k.val + 1, by omega⟩).2.2.1 =
    (B.fields ⟨k.val + 1, by omega⟩).2.2.1
  rw [hfields]
  by_cases hk : k.val = 0
  · have hb : 1 < (compileAdvice q).b := by
      change 1 < (compileAdvice q).s + 11
      omega
    have hroot :
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by omega⟩).mode = .IWAIT ∨
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by omega⟩).mode = .CWAIT := hm
    have hfirstCell :
        (GrantBankReference.bankLocalReferenceCell B
          ⟨1, by omega⟩).tok = .E := hfirst
    have hraw := bankTrialDurationOrphanRawOutgoing
      (compileAdvice q).b (compileAdvice q).theta
      (GrantBankReference.bankLocalReferenceCell B
        ⟨0, by omega⟩)
      (GrantBankReference.bankLocalReferenceCell B
        ⟨1, by omega⟩)
      hb rfl rfl rfl hroot hfirstCell
    have hclamped :
        (GrantBankReference.bankLocalReferenceClampedQuad q
          ((GrantBankReference.bankLocalReferenceInternalPair q B
            ⟨0, by omega⟩).2)).2.2.1 = .E :=
      (bankTrialLiveClampBitToken q
        ((GrantBankReference.bankLocalReferenceInternalPair q B
          ⟨0, by omega⟩).2)).2.trans hraw.1
    have hold :
        (B.fields ⟨1, by omega⟩).2.2.1 = .E := hfirst
    simpa [hk] using hclamped.trans hold.symm
  · have hzero : k.val + 1 ≠ 0 := by omega
    have hone : k.val + 1 ≠ 1 := by omega
    simp only [Fin.val_mk, hzero, hone, ↓reduceIte]

/-- At an outgoing-root edge with no first-digit worker, an old
IWAIT/CWAIT root either stays in the same waiting mode or RESET. -/
theorem bankTrialDurationRootWaitEmptyModeCases {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hfirst : bankTrialLiveWaveToken B
      ⟨0, bankTrialWindowWidthPos q⟩ = .E) :
    bankTrialLiveWaveRootMode
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root) = bankTrialLiveWaveRootMode B ∨
    bankTrialLiveWaveRootMode
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root) = .RESET := by
  have hb : 1 < (compileAdvice q).b := by
    change 1 < (compileAdvice q).s + 11
    omega
  have hroot :
      (GrantBankReference.bankLocalReferenceCell B
        ⟨0, by omega⟩).mode = .IWAIT ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨0, by omega⟩).mode = .CWAIT := hm
  have hfirstCell :
      (GrantBankReference.bankLocalReferenceCell B
        ⟨1, by omega⟩).tok = .E := hfirst
  have hraw := bankTrialDurationOrphanRawOutgoing
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨0, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨1, by omega⟩)
    hb rfl rfl rfl hroot hfirstCell
  have hfields := bankTrialDurationRootFieldsRow ring root hw B hf
  have hmode :
      bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) =
      (GrantBankReference.bankLocalReferenceInternalPair q B
        ⟨0, by omega⟩).1.mode := by
    change
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B root).fields ⟨0, by omega⟩).1 =
      (GrantBankReference.bankLocalReferenceInternalPair q B
        ⟨0, by omega⟩).1.mode
    rw [hfields]
    simp [GrantBankReference.bankLocalReferenceClampedQuad,
      GrantBankReference.bankAgentLeaseQuad, copyBank]
  rcases hraw.2 with hsame | hreset
  · exact Or.inl (hmode.trans hsame)
  · exact Or.inr (hmode.trans hreset)

/-- For a waiting wave with an outstanding worker away from the
root, outgoing root is weakly nonincreasing on the actual observer.
RESET becomes RECOVERY rather than a new class-one debt. -/
theorem bankTrialDurationRootWaitEmptyWorkerWeak {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hp : 0 < bankTrialDurationWorkerTokenMaximum B)
    (hfirst : bankTrialLiveWaveToken B
      ⟨0, bankTrialWindowWidthPos q⟩ = .E) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) root) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  apply bankTrialDurationWaitWorkerNextWeakOfMaximum
    ring root root B begun hm hp
  · rw [bankTrialDurationRootWaitEmptyMaximumFrame
      ring root hw B hf hm hfirst] <;> exact Nat.le_refl _
  · intro nextBegun hnext
    rcases bankTrialDurationRootWaitEmptyModeCases
      ring root hw B hf hm hfirst with hsame | hreset
    · exact hsame
    · exact False.elim ((bankTrialDurationNextLiveNonreset
        ring root root B begun nextBegun hnext) hreset)

end L3

/-!
Source deductions.
This closes the class-zero/nonroot clause for the ORIGINAL
bankTrialDurationWorkerRemaining (rather than its lease-aware variant).
The class-one physical all-edge rows remain an explicit premise.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The ORIGINAL worker observer is zero whenever the current
reference root is ARMED, independently of the observer phase. -/
theorem bankTrialDurationWorkerArmedAnyPhase {q : Nat}
    (z : BankTrialLocalState q)
    (hm : bankTrialLiveWaveRootMode z.bank = .ARMED) :
    bankTrialDurationWorkerRemaining z = 0 := by
  cases z with
  | mk B phase =>
      cases phase with
      | live begun =>
          exact bankTrialDurationWorkerRemainingArmed B begun hm
      | recovery => rfl
      | won => rfl
      | lost => rfl

/-- Actual CLEAN-reachable class-zero nonroot clause for the
ORIGINAL worker potential. A root-incoming edge changes the
observer to RECOVERY; all other nonroot letters preserve the
ARMED root mode, even if their protected digit fields change. -/
theorem bankTrialDurationWorkerClassZeroNonrootProved {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (z : BankTrialLocalState q)
    (hreach : BankTrialDurationReachable ring root S z)
    (hclass : bankTrialDurationClass z = 0)
    (e : Fin n) (hne : e ≠ root) :
    bankTrialDurationWorkerRemaining
      (bankTrialLocalNext ring root z e) = 0 := by
  cases z with
  | mk B phase =>
      cases phase with
      | live begun =>
          have hm : bankTrialLiveWaveRootMode B = .ARMED := by
            by_cases ha : bankTrialLiveWaveRootMode B = .ARMED
            · exact ha
            · change
                (if bankTrialLiveWaveRootMode B = .ARMED
                  then 0 else 1) = 0 at hclass
              rw [if_neg ha] at hclass
              omega
          obtain ⟨word, hword⟩ := hreach
          have hf : B.success = false :=
            bankTrialProbabilityCleanLiveUnlatched
              ring root S hclean word B begun hword
          by_cases hin : ring.rightNeighbor e = root
          · rw [bankTrialProbabilityIncomingArmedEntersRecovery
                ring root e B begun hf hm hne hin]
            rfl
          · have hframe := bankTrialLocalRootNonincidentFrame
              ring root e B hf hne hin
            have hnextMode :
                bankTrialLiveWaveRootMode
                  (bankTrialLocalNext ring root
                    (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank =
                  .ARMED := by
              change
                ((bankTrialLocalNext ring root
                  (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank.fields
                  ⟨0, by omega⟩).1 = .ARMED
              rw [bankTrialLocalNextLiveBank]
              rw [hframe]
              exact hm
            exact bankTrialDurationWorkerArmedAnyPhase
              (bankTrialLocalNext ring root
                (⟨B, .live begun⟩ : BankTrialLocalState q) e)
              hnextMode
      | recovery =>
          change (2 : Nat) = 0 at hclass
          omega
      | won =>
          change (2 : Nat) = 0 at hclass
          omega
      | lost =>
          change (2 : Nat) = 0 at hclass
          omega

/-- Every CLEAN-reachable old class-one LIVE state is CSTART,
RWAIT, IWAIT or CWAIT. The old class does NOT remove a
workerless IWAIT/CWAIT state; this differs from the lease-aware
class which assigns those states to class two. -/
theorem bankTrialDurationOriginalClassOneModeCases {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun : Bool)
    (hreach : BankTrialDurationReachable ring root S
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hclass : bankTrialDurationClass
      (⟨B, .live begun⟩ : BankTrialLocalState q) = 1) :
    bankTrialLiveWaveRootMode B = .CSTART ∨
    bankTrialLiveWaveRootMode B = .RWAIT ∨
    bankTrialLiveWaveRootMode B = .IWAIT ∨
    bankTrialLiveWaveRootMode B = .CWAIT := by
  obtain ⟨word, hword⟩ := hreach
  have hphase :
      (bankTrialLocalRun ring root word
        (bankTrialLocalStart S)).phase = .live begun := by
    rw [hword]
  have hnreset := (bankTrialWindowLockedCleanWords
    ring root hw S hclean word).2 begun hphase
  rw [hword] at hnreset
  have hnarmed : bankTrialLiveWaveRootMode B ≠ .ARMED := by
    intro ha
    change (if bankTrialLiveWaveRootMode B = .ARMED
      then 0 else 1) = 1 at hclass
    rw [if_pos ha] at hclass
    omega
  cases hm : bankTrialLiveWaveRootMode B with
  | RESET =>
      exact False.elim (hnreset hm)
  | ARMED =>
      exact False.elim (hnarmed hm)
  | RWAIT =>
      exact Or.inr (Or.inl rfl)
  | IWAIT =>
      exact Or.inr (Or.inr (Or.inl rfl))
  | CSTART =>
      exact Or.inl rfl
  | CWAIT =>
      exact Or.inr (Or.inr (Or.inr rfl))

/-- Only the original-clock class-one all-edge monotonicity and
actual nominated-edge progress are needed after the
class-zero result. This is a conditional interface, not a
new assumption added to the headline budget. -/
theorem bankTrialDurationWorkerRankRowsOfClassOne {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hclassOne :
      ∀ S : GrantBankReference.BankLocalReference
          (compileAdvice q).b,
        BankTrialLocalClean q S →
        ∀ z : BankTrialLocalState q,
          BankTrialDurationReachable ring root S z →
          ¬ bankTrialLocalTerminal z →
          bankTrialDurationClass z = 1 →
          (∀ e : Fin n,
            bankTrialDurationWorkerRemaining
              (bankTrialLocalNext ring root z e) ≤
                bankTrialDurationWorkerRemaining z) ∧
          ∃ chosen : Fin n,
            bankTrialDurationWorkerRemaining
              (bankTrialLocalNext ring root z chosen) + 1 ≤
                bankTrialDurationWorkerRemaining z) :
    BankTrialDurationWorkerRankEdgeRows (q := q) ring root := by
  intro S hclean z hreach hnot
  constructor
  · intro hzero e hne
    exact bankTrialDurationWorkerClassZeroNonrootProved
      ring root S hclean z hreach hzero e hne
  · intro hone
    exact hclassOne S hclean z hreach hnot hone

/-- Connect the remaining original class-one row contract
to the exact C.6 worker budget through the already-installed
bankTrialDurationWorkerBudgetOfRankEdges theorem. -/
theorem bankTrialDurationWorkerBudgetOfClassOne {n q : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (hclassOne :
      ∀ S : GrantBankReference.BankLocalReference
          (compileAdvice q).b,
        BankTrialLocalClean q S →
        ∀ z : BankTrialLocalState q,
          BankTrialDurationReachable ring root S z →
          ¬ bankTrialLocalTerminal z →
          bankTrialDurationClass z = 1 →
          (∀ e : Fin n,
            bankTrialDurationWorkerRemaining
              (bankTrialLocalNext ring root z e) ≤
                bankTrialDurationWorkerRemaining z) ∧
          ∃ chosen : Fin n,
            bankTrialDurationWorkerRemaining
              (bankTrialLocalNext ring root z chosen) + 1 ≤
                bankTrialDurationWorkerRemaining z) :
    BankTrialDurationWorkerBudget (q := q) ring root := by
  exact bankTrialDurationWorkerBudgetOfRankEdges
    ring hn root
    (bankTrialDurationWorkerRankRowsOfClassOne
      ring root hclassOne)

end L3

/-!
No CLEAN-reachable no-orphan theorem is asserted here.
The exact no-orphan condition is an explicit transfer premise.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The original and lease-aware C.6 observers can agree on all
CLEAN-reachable states only if no LIVE wait has zero worker tokens. -/
def BankTrialDurationNoReachableOrphan {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ S : GrantBankReference.BankLocalReference
      (compileAdvice q).b,
    BankTrialLocalClean q S →
    ∀ z : BankTrialLocalState q,
      BankTrialDurationReachable ring root S z →
      ∀ begun : Bool, z.phase = .live begun →
        (bankTrialLiveWaveRootMode z.bank = .IWAIT ∨
         bankTrialLiveWaveRootMode z.bank = .CWAIT) →
        0 < bankTrialDurationWorkerTokenMaximum z.bank

/-- On an individual state without a LIVE orphan, the two
stage-class functions agree exactly. -/
theorem bankTrialDurationClassAgreementOfNoOrphan {q : Nat}
    (z : BankTrialLocalState q)
    (hno : ∀ begun : Bool, z.phase = .live begun →
      (bankTrialLiveWaveRootMode z.bank = .IWAIT ∨
       bankTrialLiveWaveRootMode z.bank = .CWAIT) →
      0 < bankTrialDurationWorkerTokenMaximum z.bank) :
    bankTrialDurationLeaseAwareClass z =
      bankTrialDurationClass z := by
  cases z with
  | mk B phase =>
      cases phase with
      | live begun =>
          have hnot :
              ¬ ((bankTrialLiveWaveRootMode B = .IWAIT ∨
                   bankTrialLiveWaveRootMode B = .CWAIT) ∧
                  bankTrialDurationWorkerTokenMaximum B = 0) := by
            intro h
            have hp := hno begun rfl h.1
            rw [h.2] at hp
            omega
          change
            (if bankTrialLiveWaveRootMode B = .ARMED then 0
             else if
               ((bankTrialLiveWaveRootMode B = .IWAIT ∨
                 bankTrialLiveWaveRootMode B = .CWAIT) ∧
                bankTrialDurationWorkerTokenMaximum B = 0)
             then 2 else 1) =
            (if bankTrialLiveWaveRootMode B = .ARMED then 0 else 1)
          by_cases ha : bankTrialLiveWaveRootMode B = .ARMED
          · simp [ha]
          · simp [ha, hnot]
      | recovery => rfl
      | won => rfl
      | lost => rfl

/-- Equality of classes also yields equality of the two
worker-remaining functions; RECOVERY, WON and LOST cost zero. -/
theorem bankTrialDurationRankAgreementOfNoOrphan {q : Nat}
    (z : BankTrialLocalState q)
    (hno : ∀ begun : Bool, z.phase = .live begun →
      (bankTrialLiveWaveRootMode z.bank = .IWAIT ∨
       bankTrialLiveWaveRootMode z.bank = .CWAIT) →
      0 < bankTrialDurationWorkerTokenMaximum z.bank) :
    bankTrialDurationLeaseAwareWorkerRemaining z =
      bankTrialDurationWorkerRemaining z := by
  have hclass := bankTrialDurationClassAgreementOfNoOrphan z hno
  cases z with
  | mk B phase =>
      cases phase with
      | live begun =>
          have hOldNotTwo :
              bankTrialDurationClass
                (⟨B, .live begun⟩ : BankTrialLocalState q) ≠ 2 := by
            change
              (if bankTrialLiveWaveRootMode B = .ARMED
                then (0 : Nat) else 1) ≠ 2
            split <;> omega
          have hAwareNotTwo :
              bankTrialDurationLeaseAwareClass
                (⟨B, .live begun⟩ : BankTrialLocalState q) ≠ 2 := by
            rw [hclass]
            exact hOldNotTwo
          unfold bankTrialDurationLeaseAwareWorkerRemaining
          rw [if_neg hAwareNotTwo]
      | recovery => rfl
      | won => rfl
      | lost => rfl

/-- All reachable states, including terminal successors, inherit
both exact observer equalities from no-orphan reachability. -/
theorem bankTrialDurationReachableAgreementsOfNoOrphan {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hno : BankTrialDurationNoReachableOrphan (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (z : BankTrialLocalState q)
    (hreach : BankTrialDurationReachable ring root S z) :
    bankTrialDurationLeaseAwareClass z =
      bankTrialDurationClass z ∧
    bankTrialDurationLeaseAwareWorkerRemaining z =
      bankTrialDurationWorkerRemaining z := by
  have hlocal := hno S hclean z hreach
  exact ⟨bankTrialDurationClassAgreementOfNoOrphan z hlocal,
    bankTrialDurationRankAgreementOfNoOrphan z hlocal⟩

/-- Transfer all three required ORIGINAL worker-row clauses
from lease-aware rows under no-orphan reachability. Next-state
rank equality is justified by actual chronological reachability. -/
theorem bankTrialDurationRankRowsOfLeaseAwareNoOrphan {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hno : BankTrialDurationNoReachableOrphan (q := q) ring root)
    (hrows : BankTrialDurationLeaseAwareWorkerRankEdgeRows
      (q := q) ring root) :
    BankTrialDurationWorkerRankEdgeRows (q := q) ring root := by
  intro S hclean z hreach hnot
  have hOld := bankTrialDurationReachableAgreementsOfNoOrphan
    ring root hno S hclean z hreach
  have hSource := hrows S hclean z hreach hnot
  have hNext :
      ∀ e : Fin n,
        bankTrialDurationLeaseAwareWorkerRemaining
          (bankTrialLocalNext ring root z e) =
        bankTrialDurationWorkerRemaining
          (bankTrialLocalNext ring root z e) := by
    intro e
    exact (bankTrialDurationReachableAgreementsOfNoOrphan
      ring root hno S hclean
      (bankTrialLocalNext ring root z e)
      (bankTrialDurationReachableNext
        ring root S z hreach e)).2
  constructor
  · intro hzero e hne
    have ha : bankTrialDurationLeaseAwareClass z = 0 :=
      hOld.1.trans hzero
    rw [← hNext e]
    exact hSource.1 ha e hne
  · intro hone
    have ha : bankTrialDurationLeaseAwareClass z = 1 :=
      hOld.1.trans hone
    obtain ⟨hmono, hdrop⟩ := hSource.2.1 ha
    constructor
    · intro e
      rw [← hNext e, ← hOld.2]
      exact hmono e
    · obtain ⟨chosen, hs⟩ := hdrop
      refine ⟨chosen, ?_⟩
      rw [← hNext chosen, ← hOld.2]
      exact hs

/-- Original C.6 worker budget follows from genuine no-orphan
reachability and all lease-aware rows, with no rank substitution
on uncertified successor states. -/
theorem bankTrialDurationWorkerBudgetOfLeaseAwareNoOrphan
    {n q : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n) (root : Fin n)
    (hno : BankTrialDurationNoReachableOrphan (q := q) ring root)
    (hrows : BankTrialDurationLeaseAwareWorkerRankEdgeRows
      (q := q) ring root) :
    BankTrialDurationWorkerBudget (q := q) ring root := by
  exact bankTrialDurationWorkerBudgetOfRankEdges ring hn root
    (bankTrialDurationRankRowsOfLeaseAwareNoOrphan
      ring root hno hrows)

/-- Core-Nat list membership-to-sum inequality. -/
private theorem bankTrialDurationNatMemberLeSum (xs : List Nat) :
    ∀ x : Nat, x ∈ xs → x ≤ xs.sum := by
  induction xs with
  | nil =>
      intro x h
      cases h
  | cons head tail ih =>
      intro x h
      have hm : x = head ∨ x ∈ tail := by
        simpa only [List.mem_cons] using h
      rcases hm with hh | ht
      · rw [hh]
        simp only [List.sum_cons]
        omega
      · have hb := ih x ht
        simp only [List.sum_cons]
        omega

/-- The last protected digit, with an explicit positive-width
certificate rather than arithmetic on an anonymous Fin value. -/
def bankTrialDurationTopDigit (q : Nat) :
    Fin (compileAdvice q).b :=
  ⟨(compileAdvice q).b - 1, by
    have hpos := bankTrialWindowWidthPos q
    omega⟩

/-- A top-position IR already contributes at least 2^b to the
actual in-flight carry potential, irrespective of all other bits. -/
theorem bankTrialDurationTopIRCarryFloor {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (htop : bankTrialLiveWaveToken B
      (bankTrialDurationTopDigit q) = .IR) :
    2 ^ (compileAdvice q).b ≤ bankTrialLiveCarryValue B := by
  have hindex :
      (bankTrialDurationTopDigit q).val + 1 =
        (compileAdvice q).b := by
    unfold bankTrialDurationTopDigit
    simp only [Fin.val_mk]
    have hpos := bankTrialWindowWidthPos q
    omega
  have htok :
      (B.fields ⟨(bankTrialDurationTopDigit q).val + 1,
        Nat.succ_lt_succ (bankTrialDurationTopDigit q).isLt⟩).2.2.1 =
          .IR := by
    exact htop
  have hmem :
      bankTrialLiveSlotPotential (bankTrialDurationTopDigit q).val
        (B.fields ⟨(bankTrialDurationTopDigit q).val + 1,
          Nat.succ_lt_succ (bankTrialDurationTopDigit q).isLt⟩).2.1
        (B.fields ⟨(bankTrialDurationTopDigit q).val + 1,
          Nat.succ_lt_succ (bankTrialDurationTopDigit q).isLt⟩).2.2.1 ∈
      (List.ofFn (fun j : Fin (compileAdvice q).b =>
        bankTrialLiveSlotPotential j.val
          (B.fields ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩).2.1
          (B.fields ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩).2.2.1)) := by
    exact (List.mem_ofFn).2 ⟨bankTrialDurationTopDigit q, rfl⟩
  have hsum :
      bankTrialLiveSlotPotential (bankTrialDurationTopDigit q).val
        (B.fields ⟨(bankTrialDurationTopDigit q).val + 1,
          Nat.succ_lt_succ (bankTrialDurationTopDigit q).isLt⟩).2.1
        (B.fields ⟨(bankTrialDurationTopDigit q).val + 1,
          Nat.succ_lt_succ (bankTrialDurationTopDigit q).isLt⟩).2.2.1 ≤
      bankTrialLiveCarryValue B := by
    unfold bankTrialLiveCarryValue
    exact bankTrialDurationNatMemberLeSum _ _ hmem
  have hweight :
      2 ^ (compileAdvice q).b ≤
        bankTrialLiveSlotPotential (bankTrialDurationTopDigit q).val
          (B.fields ⟨(bankTrialDurationTopDigit q).val + 1,
            Nat.succ_lt_succ (bankTrialDurationTopDigit q).isLt⟩).2.1
          (B.fields ⟨(bankTrialDurationTopDigit q).val + 1,
            Nat.succ_lt_succ (bankTrialDurationTopDigit q).isLt⟩).2.2.1 := by
    unfold bankTrialLiveSlotPotential
    simp only [htok, ↓reduceIte]
    have hpow :
        2 ^ ((bankTrialDurationTopDigit q).val + 1) =
          2 ^ (compileAdvice q).b :=
      congrArg (fun x : Nat => 2 ^ x) hindex
    rw [hpow]
    omega
  exact Nat.le_trans hweight hsum

/-- If a LIVE carry ceiling by K were available, K < 2^b
would exclude the top-IR erasure mechanism. The required
chronological carry ceiling is not asserted by this lemma. -/
theorem bankTrialDurationNoTopIRFromCarryLeK {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hCarry : bankTrialLiveCarryValue B ≤ (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    bankTrialLiveWaveToken B
      (bankTrialDurationTopDigit q) ≠ .IR := by
  intro hIR
  have hlarge := bankTrialDurationTopIRCarryFloor B hIR
  omega

end L3

/-!
The root/interior/top/incoming preservation producers are NOT
proved by the finite projection check. No unconditional
all-n no-orphan theorem is claimed below.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A state-only LIVE certificate. Besides the already proved
non-RESET unique-worker and positive-comparison genealogy,
it records the no-wrap ceiling, strict ARMED threshold, actual
waiting worker, and negative comparator provenance. -/
structure BankTrialDurationOrphanInv (q : Nat)
    (z : BankTrialLocalState q) : Prop where
  locked : BankTrialLiveNoResetLocked z
  noLiveResetWait :
    ∀ begun : Bool, z.phase = .live begun →
      bankTrialLiveWaveRootMode z.bank ≠ .RWAIT
  carryBound :
    ∀ begun : Bool, z.phase = .live begun →
      bankTrialLiveCarryValue z.bank ≤ (compileAdvice q).K
  armedBeforeThreshold :
    ∀ begun : Bool, z.phase = .live begun →
      bankTrialLiveWaveRootMode z.bank = .ARMED →
      bankTrialLiveCarryValue z.bank < (compileAdvice q).K
  workerPresent :
    ∀ begun : Bool, z.phase = .live begun →
      (bankTrialLiveWaveRootMode z.bank = .IWAIT ∨
       bankTrialLiveWaveRootMode z.bank = .CWAIT) →
      ∃ j : Fin (compileAdvice q).b,
        bankTrialLiveWaveToken z.bank j ≠ .E
  zeroOutMismatch :
    ∀ begun : Bool, z.phase = .live begun →
      ∀ j : Fin (compileAdvice q).b,
        bankTrialLiveWaveToken z.bank j = .CR0 →
        ∃ k : Fin (compileAdvice q).b,
          k.val ≤ j.val ∧
          bankTrialLiveWaveBit z.bank k ≠
            (compileAdvice q).theta k.val
  zeroBackMismatch :
    ∀ begun : Bool, z.phase = .live begun →
      ∀ j : Fin (compileAdvice q).b,
        bankTrialLiveWaveToken z.bank j = .CL0 →
        ∃ k : Fin (compileAdvice q).b,
          bankTrialLiveWaveBit z.bank k ≠
            (compileAdvice q).theta k.val

private theorem bankTrialDurationOrphanCleanTokens {q : Nat}
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken S j = .E := by
  intro j
  exact (hclean.2.2.1 (j.val + 1)
    (by omega : 1 ≤ j.val + 1)
    (by omega : j.val + 1 ≤ (compileAdvice q).b)).2

/-- CLEAN produces the strengthened invariant, assuming K>0. -/
theorem bankTrialDurationOrphanInvClean {q : Nat}
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hpositive : 0 < (compileAdvice q).K) :
    BankTrialDurationOrphanInv q (bankTrialLocalStart S) := by
  have harm : bankTrialLiveWaveRootMode S = .ARMED :=
    hclean.2.1
  have hempty := bankTrialDurationOrphanCleanTokens S hclean
  refine {
    locked := bankTrialLiveNoResetLockedStart S hclean,
    noLiveResetWait := ?_,
    carryBound := ?_,
    armedBeforeThreshold := ?_,
    workerPresent := ?_,
    zeroOutMismatch := ?_,
    zeroBackMismatch := ?_
  }
  · intro begun _ hm
    change bankTrialLiveWaveRootMode S = _ at hm
    rw [harm] at hm
    cases hm
  · intro begun _
    change bankTrialLiveCarryValue S ≤ (compileAdvice q).K
    rw [bankTrialLiveCarryClean S hclean]
    exact Nat.zero_le _
  · intro begun _ _
    change bankTrialLiveCarryValue S < (compileAdvice q).K
    rw [bankTrialLiveCarryClean S hclean]
    exact hpositive
  · intro begun _ hm
    rcases hm with hm | hm
    · change bankTrialLiveWaveRootMode S = _ at hm
      rw [harm] at hm
      cases hm
    · change bankTrialLiveWaveRootMode S = _ at hm
      rw [harm] at hm
      cases hm
  · intro begun _ j ht
    change bankTrialLiveWaveToken S j = _ at ht
    rw [hempty j] at ht
    cases ht
  · intro begun _ j ht
    change bankTrialLiveWaveToken S j = _ at ht
    rw [hempty j] at ht
    cases ht

/-- Nonempty physical token implies a positive real worker rank. -/
theorem bankTrialDurationNoOrphanOfInv {q : Nat}
    (z : BankTrialLocalState q)
    (hinv : BankTrialDurationOrphanInv q z)
    (begun : Bool) (hlive : z.phase = .live begun)
    (hmode : bankTrialLiveWaveRootMode z.bank = .IWAIT ∨
      bankTrialLiveWaveRootMode z.bank = .CWAIT) :
    0 < bankTrialDurationWorkerTokenMaximum z.bank := by
  obtain ⟨j, hj⟩ := hinv.workerPresent begun hlive hmode
  have hn : bankTrialDurationWorkerTokenMaximum z.bank ≠ 0 := by
    intro hzero
    have he := bankTrialDurationWorkerMaximumZeroTokens
      z.bank hzero j
    exact hj he
  exact Nat.pos_of_ne_zero hn

/-- The carry ceiling excludes top-IR erasure when K<2^b. -/
theorem bankTrialDurationOrphanInvNoTopIR {q : Nat}
    (z : BankTrialLocalState q)
    (hinv : BankTrialDurationOrphanInv q z)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (begun : Bool) (hlive : z.phase = .live begun) :
    bankTrialLiveWaveToken z.bank
      (bankTrialDurationTopDigit q) ≠ .IR := by
  exact bankTrialDurationNoTopIRFromCarryLeK
    z.bank (hinv.carryBound begun hlive) hK

/-- A LIVE successor always has an old LIVE predecessor. -/
private theorem bankTrialDurationNextLiveOrigin {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialLocalState q) (nextBegun : Bool)
    (hnext : (bankTrialLocalNext ring root z e).phase =
      .live nextBegun) :
    ∃ begun : Bool, z.phase = .live begun := by
  cases z with
  | mk B phase =>
    cases phase with
    | live begun =>
        exact ⟨begun, rfl⟩
    | recovery =>
        simp [bankTrialLocalNext] at hnext <;>
          (repeat' split at hnext) <;> cases hnext
    | won =>
        simp [bankTrialLocalNext] at hnext
    | lost =>
        simp [bankTrialLocalNext] at hnext

/-- A full BANK frame preserves all seven invariant clauses. -/
private theorem bankTrialDurationOrphanInvOfFrame {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialLocalState q)
    (hinv : BankTrialDurationOrphanInv q z)
    (hframe : (bankTrialLocalNext ring root z e).bank =
      z.bank) :
    BankTrialDurationOrphanInv q
      (bankTrialLocalNext ring root z e) := by
  have horigin := bankTrialDurationNextLiveOrigin
    ring root e z
  refine {
    locked := ?_,
    noLiveResetWait := ?_,
    carryBound := ?_,
    armedBeforeThreshold := ?_,
    workerPresent := ?_,
    zeroOutMismatch := ?_,
    zeroBackMismatch := ?_
  }
  · constructor
    · intro nextBegun hnext
      obtain ⟨begun, hprev⟩ := horigin nextBegun hnext
      rw [hframe]
      exact hinv.locked.1 begun hprev
    · intro nextBegun hnext
      obtain ⟨begun, hprev⟩ := horigin nextBegun hnext
      rw [hframe]
      exact hinv.locked.2 begun hprev
  · intro nextBegun hnext
    obtain ⟨begun, hprev⟩ := horigin nextBegun hnext
    rw [hframe]
    exact hinv.noLiveResetWait begun hprev
  · intro nextBegun hnext
    obtain ⟨begun, hprev⟩ := horigin nextBegun hnext
    rw [hframe]
    exact hinv.carryBound begun hprev
  · intro nextBegun hnext hm
    obtain ⟨begun, hprev⟩ := horigin nextBegun hnext
    rw [hframe] at hm ⊢
    exact hinv.armedBeforeThreshold begun hprev hm
  · intro nextBegun hnext hm
    obtain ⟨begun, hprev⟩ := horigin nextBegun hnext
    rw [hframe] at hm ⊢
    exact hinv.workerPresent begun hprev hm
  · intro nextBegun hnext j ht
    obtain ⟨begun, hprev⟩ := horigin nextBegun hnext
    rw [hframe] at ht ⊢
    exact hinv.zeroOutMismatch begun hprev j ht
  · intro nextBegun hnext j ht
    obtain ⟨begun, hprev⟩ := horigin nextBegun hnext
    rw [hframe] at ht ⊢
    exact hinv.zeroBackMismatch begun hprev j ht

/-- Unsupported physical edges frame BANK even in RECOVERY. -/
private theorem bankTrialDurationOutsideWholeBankFrame {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialLocalState q)
    (hout : ¬ Counter.Support q ring root e) :
    (bankTrialLocalNext ring root z e).bank = z.bank := by
  cases z with
  | mk B phase =>
    cases phase with
    | live begun =>
        exact bankTrialLiveOutsideBankFrame
          ring root e B begun hout
    | recovery =>
        rw [bankTrialLocalNextRecoveryBank]
        exact bankTrialLocalStepOutside ring root e B hout
    | won =>
        rfl
    | lost =>
        rfl

/-- The outside edge class is proved without a nonalias premise. -/
theorem bankTrialDurationOrphanInvOutside {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hout : ¬ Counter.Support q ring root e)
    (z : BankTrialLocalState q)
    (hinv : BankTrialDurationOrphanInv q z) :
    BankTrialDurationOrphanInv q
      (bankTrialLocalNext ring root z e) := by
  exact bankTrialDurationOrphanInvOfFrame ring root e z hinv
    (bankTrialDurationOutsideWholeBankFrame
      ring root e z hout)

/-- A supported-row preservation goal, not a proved row. -/
def BankTrialDurationOrphanInvEdge {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n) : Prop :=
  ∀ z : BankTrialLocalState q,
    BankTrialDurationOrphanInv q z →
      BankTrialDurationOrphanInv q
        (bankTrialLocalNext ring root z e)

/-- Four independent supported-row obligations; the outside case is proved. -/
structure BankTrialDurationOrphanRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop where
  rootRow :
    BankTrialDurationOrphanInvEdge (q := q) ring root root
  interiorRows :
    ∀ j : Fin (compileAdvice q).b, 0 < j.val →
      BankTrialDurationOrphanInvEdge (q := q)
        ring root (Counter.site ring root j.val)
  topRow :
    BankTrialDurationOrphanInvEdge (q := q)
      ring root (Counter.site ring root (compileAdvice q).b)
  incomingRows :
    ∀ e : Fin n, ring.rightNeighbor e = root →
      BankTrialDurationOrphanInvEdge (q := q) ring root e

theorem bankTrialDurationOrphanInvEdgeOutside {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hout : ¬ Counter.Support q ring root e) :
    BankTrialDurationOrphanInvEdge (q := q) ring root e := by
  intro z hinv
  exact bankTrialDurationOrphanInvOutside
    ring root e hout z hinv

/-- Original edge-class geometry, with no invented fifth class. -/
theorem bankTrialDurationOrphanInvAllEdgesOfRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hrows : BankTrialDurationOrphanRows (q := q) ring root) :
    ∀ e : Fin n,
      BankTrialDurationOrphanInvEdge (q := q) ring root e := by
  intro e
  rcases Counter.resetTrialEdgeGeometry (q := q)
      ring root e with hsource | hin | hout
  · obtain ⟨j, hj, he⟩ := hsource
    by_cases htop : j = (compileAdvice q).b
    · subst j
      rw [he]
      exact hrows.topRow
    · by_cases hzero : j = 0
      · subst j
        change e = root at he
        rw [he]
        exact hrows.rootRow
      · have hjfin : j < (compileAdvice q).b := by omega
        rw [he]
        exact hrows.interiorRows
          ⟨j, hjfin⟩ (Nat.pos_of_ne_zero hzero)
  · exact hrows.incomingRows e hin
  · have houtside : ¬ Counter.Support q ring root e := by
      intro hs
      rcases hs with hinc | ⟨j, hj, he⟩
      · have hp := (hout 0 (by omega)).2
        change ring.rightNeighbor e ≠ root at hp
        exact hp hinc
      · exact (hout j hj).1 he
    exact bankTrialDurationOrphanInvEdgeOutside
      ring root e houtside

/-- Finite-word invariant induction, conditional on supported rows. -/
theorem bankTrialDurationOrphanInvRunOfRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hrows : BankTrialDurationOrphanRows (q := q) ring root) :
    ∀ (w : List (Fin n)) (z : BankTrialLocalState q),
      BankTrialDurationOrphanInv q z →
      BankTrialDurationOrphanInv q
        (bankTrialLocalRun ring root w z) := by
  have hall := bankTrialDurationOrphanInvAllEdgesOfRows
    ring root hrows
  intro w
  induction w with
  | nil =>
      intro z hinv
      exact hinv
  | cons e tail ih =>
      intro z hinv
      change BankTrialDurationOrphanInv q
        (bankTrialLocalRun ring root tail
          (bankTrialLocalNext ring root z e))
      exact ih _ ((hall e) z hinv)

/-- NOT the unconditional headline. Four supported rows are
explicit premises, with all four prescribed parameter assumptions. -/
theorem bankTrialDurationNoReachableOrphanHoldsOfRows
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hnonalias : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hrows : BankTrialDurationOrphanRows (q := q) ring root) :
    BankTrialDurationNoReachableOrphan (q := q) ring root := by
  intro S hclean z hreach begun hlive hmode
  obtain ⟨w, hw⟩ := hreach
  have hinv := bankTrialDurationOrphanInvRunOfRows
    ring root hrows w (bankTrialLocalStart S)
    (bankTrialDurationOrphanInvClean S hclean hpositive)
  rw [hw] at hinv
  exact bankTrialDurationNoOrphanOfInv
    z hinv begun hlive hmode

end L3

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The literal top-turn pair has precisely one outgoing destination
token: IR is erased, CR0 turns to CL0, and CR1 turns to CL1.  In every
case the rank of the surviving source token drops strictly. -/
theorem bankTrialDurationTopTurnOwnerRank
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1) (htop : y.role = b)
    (hsrc : x.tok = .E)
    (hdst : y.tok = .IR ∨ y.tok = .CR0 ∨ y.tok = .CR1) :
    (bankPair x y y.role b theta).2.tok = .E ∧
    bankTrialDurationWorkerTokenRank b x.role
        (bankPair x y y.role b theta).1.tok + 1 ≤
      bankTrialDurationWorkerTokenRank b y.role y.tok := by
  rcases hdst with hir | hcomp
  · have hr := bankTrialInteriorTopIRAbsorbed
      b theta x y hx hlt hy htop hsrc hir
    refine ⟨hr.2.1, ?_⟩
    rw [hr.1, hir]
    simp only [bankTrialDurationWorkerTokenRank]
    omega
  · rcases hcomp with hzero | hone
    · have hr := bankTrialInteriorCRZeroTop
        b theta x y hx hlt hy htop hsrc hzero
      refine ⟨hr.2.2.1, ?_⟩
      rw [hr.1, hzero]
      simp only [bankTrialDurationWorkerTokenRank]
      omega
    · have hb : 2 ≤ b := by omega
      have hlast : x.role = b - 1 := by omega
      have hr := bankTrialLiveTopCRCreatesCL
        b theta x y hb hlast htop hsrc hone
      rw [htop]
      refine ⟨hr.2, ?_⟩
      rw [hr.1, hone]
      simp only [bankTrialDurationWorkerTokenRank]
      omega

/-- The source-pair top turn is the actual physical edge site(j),
including the protected last-interior j=b-1 case; clamp preserves
both token results. -/
theorem bankTrialDurationTopTurnTokenRank {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (htop : j.val + 1 = (compileAdvice q).b)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .E)
    (hdst :
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .IR ∨
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .CR0 ∨
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .CR1) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val + 1, by omega⟩).2.2.1 = .E ∧
    bankTrialDurationWorkerTokenRank (compileAdvice q).b j.val
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val)).fields
          ⟨j.val, by omega⟩).2.2.1 + 1 ≤
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (j.val + 1)
        (B.fields ⟨j.val + 1, by omega⟩).2.2.1 := by
  have hr := bankTrialDurationTopTurnOwnerRank
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by omega⟩)
    (by change 1 ≤ j.val; omega) j.isLt
    (by rfl) (by change j.val + 1 = (compileAdvice q).b; exact htop)
    hsrc hdst
  constructor
  · rw [bankTrialWindowInteriorResponder ring root hw B hf j]
    rw [(bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).2)).2]
    exact hr.1
  · rw [bankTrialWindowInteriorSource ring root B hf j]
    rw [(bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).1)).2]
    exact hr.2

/-- One certified unique worker at the last protected digit
strictly drops the global fold-max on the top-turn edge,
even when the worker is entirely erased (IR case). -/
theorem bankTrialDurationTopTurnMaximumDrop {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (htop : j.val + 1 = (compileAdvice q).b)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .E)
    (hdst :
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .IR ∨
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .CR0 ∨
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .CR1) :
    bankTrialDurationWorkerTokenMaximum
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val)) + 1 ≤
      bankTrialDurationWorkerTokenMaximum B := by
  have hrow := bankTrialDurationTopTurnTokenRank
    ring root hw B hf j hj htop hsrc hdst
  have hind :
      (⟨j.val - 1 + 1, by omega⟩ :
        Fin ((compileAdvice q).b + 1)) =
        ⟨j.val, by omega⟩ :=
    Fin.ext (by change j.val - 1 + 1 = j.val; omega)
  have hclear :
      bankTrialLiveWaveToken
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) j = .E :=
    hrow.1
  have hold : bankTrialLiveWaveToken B j ≠ .E := by
    change (B.fields ⟨j.val + 1, by omega⟩).2.2.1 ≠ .E
    rcases hdst with hi | hc0
    · rw [hi]
      intro h
      cases h
    · rcases hc0 with hz | ho
      · rw [hz]
        intro h
        cases h
      · rw [ho]
        intro h
        cases h
  have hdrop :
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        ((⟨j.val - 1, by omega⟩ :
          Fin (compileAdvice q).b).val + 1)
        (bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j.val))
          ⟨j.val - 1, by omega⟩) + 1 ≤
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (j.val + 1) (bankTrialLiveWaveToken B j) := by
    change bankTrialDurationWorkerTokenRank (compileAdvice q).b
      (j.val - 1 + 1)
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val)).fields
          ⟨j.val - 1 + 1, by omega⟩).2.2.1 + 1 ≤
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (j.val + 1)
        (B.fields ⟨j.val + 1, by omega⟩).2.2.1
    rw [hind]
    rw [show j.val - 1 + 1 = j.val by omega]
    exact hrow.2
  apply bankTrialDurationInteriorSelectedMaximumDrop
    ring root hw B hf hc j hj j
    ⟨j.val - 1, by omega⟩ (Or.inr ⟨rfl, rfl⟩)
  · exact hold
  · exact hclear
  · exact hdrop

/-- The strict original-clock top-turn transition, under its
old pair-local token guards and the CLEAN-reachable uniqueness
certificate.  Handles IWAIT/IR, CWAIT/CR0, and CWAIT/CR1. -/
theorem bankTrialDurationTopTurnLeaseAwareDrop {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (htop : j.val + 1 = (compileAdvice q).b)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .E)
    (hdst :
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .IR ∨
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .CR0 ∨
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .CR1) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)) + 1 ≤
      bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  exact bankTrialDurationSelectedInteriorLeaseAwareDropOfMaximum
    ring root hw B begun hf hm j hj
    (bankTrialDurationTopTurnMaximumDrop
      ring root hw B hf hc j hj htop hsrc hdst)

/-- Missing cell: CR0/CR1 at digit b, empty digit b-1,
CWAIT; the physical edge is b-1, not the top edge b. -/
theorem bankTrialDurationCWaitTopTurnStrict {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .CWAIT)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (htop : j.val + 1 = (compileAdvice q).b)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .E)
    (hdst :
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .CR0 ∨
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .CR1) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)) + 1 ≤
      bankTrialDurationLeaseAwareWorkerRemaining
        (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  exact bankTrialDurationTopTurnLeaseAwareDrop
    ring root hw B begun hf hc (Or.inr hm)
    j hj htop hsrc (Or.inr hdst)

/-- Missing cell: IR already at digit b, empty digit b-1,
IWAIT; the same last-interior service erases that IR. -/
theorem bankTrialDurationIWaitTopTurnStrict {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (htop : j.val + 1 = (compileAdvice q).b)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .E)
    (hdst : (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .IR) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)) + 1 ≤
      bankTrialDurationLeaseAwareWorkerRemaining
        (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  exact bankTrialDurationTopTurnLeaseAwareDrop
    ring root hw B begun hf hc (Or.inl hm)
    j hj htop hsrc (Or.inl hdst)

/-- The repaired OtherNominatedEdge is inhabited by the
actual last-interior CWAIT/CR source-row witness. -/
theorem bankTrialDurationCWaitTopTurnNominated {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .CWAIT)
    (hsrc :
      (B.fields ⟨(compileAdvice q).b - 1, by omega⟩).2.2.1 = .E)
    (hdst :
      (B.fields ⟨(compileAdvice q).b, by omega⟩).2.2.1 = .CR0 ∨
      (B.fields ⟨(compileAdvice q).b, by omega⟩).2.2.1 = .CR1) :
    BankTrialDurationOtherNominatedEdge ring root B begun := by
  have hb : 2 ≤ (compileAdvice q).b := by
    change 2 ≤ (compileAdvice q).s + 11
    omega
  have hdest :
      (B.fields ⟨(compileAdvice q).b - 1 + 1, by omega⟩).2.2.1 = .CR0 ∨
      (B.fields ⟨(compileAdvice q).b - 1 + 1, by omega⟩).2.2.1 = .CR1 := by
    simpa only [show (compileAdvice q).b - 1 + 1 =
      (compileAdvice q).b by omega] using hdst
  have hstrict := bankTrialDurationCWaitTopTurnStrict
    ring root hw B begun hf hc hm
    ⟨(compileAdvice q).b - 1, by omega⟩
    (by change 0 < (compileAdvice q).b - 1; omega)
    (by change (compileAdvice q).b - 1 + 1 =
      (compileAdvice q).b; omega)
    hsrc hdest
  refine ⟨Counter.site ring root ((compileAdvice q).b - 1), ?_, hstrict⟩
  exact Or.inr (Or.inr (Or.inr (Or.inr
    ⟨rfl, hsrc, Or.inr ⟨hm, hdst⟩⟩)))

/-- The repaired OtherNominatedEdge also admits the IWAIT
top-turn IR erasure; this is not a top-boundary service. -/
theorem bankTrialDurationIWaitTopTurnNominated {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT)
    (hsrc :
      (B.fields ⟨(compileAdvice q).b - 1, by omega⟩).2.2.1 = .E)
    (hdst :
      (B.fields ⟨(compileAdvice q).b, by omega⟩).2.2.1 = .IR) :
    BankTrialDurationOtherNominatedEdge ring root B begun := by
  have hb : 2 ≤ (compileAdvice q).b := by
    change 2 ≤ (compileAdvice q).s + 11
    omega
  have hdest :
      (B.fields ⟨(compileAdvice q).b - 1 + 1, by omega⟩).2.2.1 = .IR := by
    simpa only [show (compileAdvice q).b - 1 + 1 =
      (compileAdvice q).b by omega] using hdst
  have hstrict := bankTrialDurationIWaitTopTurnStrict
    ring root hw B begun hf hc hm
    ⟨(compileAdvice q).b - 1, by omega⟩
    (by change 0 < (compileAdvice q).b - 1; omega)
    (by change (compileAdvice q).b - 1 + 1 =
      (compileAdvice q).b; omega)
    hsrc hdest
  refine ⟨Counter.site ring root ((compileAdvice q).b - 1), ?_, hstrict⟩
  exact Or.inr (Or.inr (Or.inr (Or.inr
    ⟨rfl, hsrc, Or.inl ⟨hm, hdst⟩⟩)))

end L3

/-!
Top and incoming preservation are reduced to literal digit-frame rows.
Root carry and interior root-mode facts are proved separately.
Root and interior *full* invariant preservation remain GAP.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Use the already proved nonaliased single-worker lock on the
actual clamped reference, not an idealized transition. -/
private theorem bankTrialDurationOrphanLockedNext
    {n q : Nat} (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q)
    (hinv : BankTrialDurationOrphanInv q z) :
    BankTrialLiveNoResetLocked
      (bankTrialLocalNext ring root z e) := by
  have hrows : ∀ f : Fin n,
      BankTrialLiveWindowLockedEdgeRow (q := q) ring root f :=
    bankTrialWindowRowsOfClasses ring root
      (bankTrialWindowRootOutgoingRows ring root)
      (bankTrialWindowInteriorRowsOfPairRows ring root
        (bankTrialLiveInteriorPairRows q))
      (bankTrialWindowTopRows ring root)
      (bankTrialWindowIncomingRows ring root)
  exact bankTrialWindowLockedNextOfRows
    ring root e hw hrows z hinv.locked

/-- An abstract *actual service* transfer. If each LIVE
successor keeps root mode and all protected digit bits/tokens,
then the strengthened LIVE invariant is preserved as well. -/
private theorem bankTrialDurationOrphanDigitFrameNext
    {n q : Nat} (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hrow :
      ∀ (B : GrantBankReference.BankLocalReference
            (compileAdvice q).b) (begun nextBegun : Bool),
        BankTrialDurationOrphanInv q
          (⟨B, .live begun⟩ : BankTrialLocalState q) →
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase =
          .live nextBegun →
        bankTrialLiveWaveRootMode
          (bankTrialLocalNext ring root
            (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank =
          bankTrialLiveWaveRootMode B ∧
        (∀ j : Fin (compileAdvice q).b,
          bankTrialLiveWaveToken
            (bankTrialLocalNext ring root
              (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank j =
          bankTrialLiveWaveToken B j) ∧
        (∀ j : Fin (compileAdvice q).b,
          bankTrialLiveWaveBit
            (bankTrialLocalNext ring root
              (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank j =
          bankTrialLiveWaveBit B j)) :
    BankTrialDurationOrphanInvEdge (q := q) ring root e := by
  intro z hinv
  have hlock := bankTrialDurationOrphanLockedNext
    ring root e hw z hinv
  have hframe :
      ∀ nextBegun : Bool,
        (bankTrialLocalNext ring root z e).phase =
          .live nextBegun →
        bankTrialLiveWaveRootMode
          (bankTrialLocalNext ring root z e).bank =
          bankTrialLiveWaveRootMode z.bank ∧
        (∀ j : Fin (compileAdvice q).b,
          bankTrialLiveWaveToken
            (bankTrialLocalNext ring root z e).bank j =
          bankTrialLiveWaveToken z.bank j) ∧
        (∀ j : Fin (compileAdvice q).b,
          bankTrialLiveWaveBit
            (bankTrialLocalNext ring root z e).bank j =
          bankTrialLiveWaveBit z.bank j) := by
    intro nextBegun hnext
    obtain ⟨begun, hprev⟩ :=
      bankTrialDurationNextLiveOrigin
        ring root e z nextBegun hnext
    cases z with
    | mk B phase =>
      cases phase with
      | live old =>
          exact hrow B old nextBegun hinv hnext
      | recovery => cases hprev
      | won => cases hprev
      | lost => cases hprev
  have hcarry :
      ∀ nextBegun : Bool,
        (bankTrialLocalNext ring root z e).phase =
          .live nextBegun →
        bankTrialLiveCarryValue
          (bankTrialLocalNext ring root z e).bank =
        bankTrialLiveCarryValue z.bank := by
    intro nextBegun hnext
    unfold bankTrialLiveCarryValue
    apply ofFn_sum_eq
    intro j
    change bankTrialLiveSlotPotential j.val
        (bankTrialLiveWaveBit
          (bankTrialLocalNext ring root z e).bank j)
        (bankTrialLiveWaveToken
          (bankTrialLocalNext ring root z e).bank j) =
      bankTrialLiveSlotPotential j.val
        (bankTrialLiveWaveBit z.bank j)
        (bankTrialLiveWaveToken z.bank j)
    rw [(hframe nextBegun hnext).2.2 j,
      (hframe nextBegun hnext).2.1 j]
  refine {
    locked := hlock,
    noLiveResetWait := ?_,
    carryBound := ?_,
    armedBeforeThreshold := ?_,
    workerPresent := ?_,
    zeroOutMismatch := ?_,
    zeroBackMismatch := ?_
  }
  · intro nextBegun hnext
    obtain ⟨begun, hprev⟩ :=
      bankTrialDurationNextLiveOrigin
        ring root e z nextBegun hnext
    rw [(hframe nextBegun hnext).1]
    exact hinv.noLiveResetWait begun hprev
  · intro nextBegun hnext
    rw [hcarry nextBegun hnext]
    obtain ⟨begun, hprev⟩ :=
      bankTrialDurationNextLiveOrigin
        ring root e z nextBegun hnext
    exact hinv.carryBound begun hprev
  · intro nextBegun hnext hmode
    rw [hcarry nextBegun hnext]
    rw [(hframe nextBegun hnext).1] at hmode
    obtain ⟨begun, hprev⟩ :=
      bankTrialDurationNextLiveOrigin
        ring root e z nextBegun hnext
    exact hinv.armedBeforeThreshold begun hprev hmode
  · intro nextBegun hnext hmode
    rw [(hframe nextBegun hnext).1] at hmode
    obtain ⟨begun, hprev⟩ :=
      bankTrialDurationNextLiveOrigin
        ring root e z nextBegun hnext
    obtain ⟨j, hj⟩ :=
      hinv.workerPresent begun hprev hmode
    refine ⟨j, ?_⟩
    rw [(hframe nextBegun hnext).2.1 j]
    exact hj
  · intro nextBegun hnext j htok
    obtain ⟨begun, hprev⟩ :=
      bankTrialDurationNextLiveOrigin
        ring root e z nextBegun hnext
    have hold : bankTrialLiveWaveToken z.bank j = .CR0 :=
      ((hframe nextBegun hnext).2.1 j).symm.trans htok
    obtain ⟨k, hk, hmismatch⟩ :=
      hinv.zeroOutMismatch begun hprev j hold
    refine ⟨k, hk, ?_⟩
    rw [(hframe nextBegun hnext).2.2 k]
    exact hmismatch
  · intro nextBegun hnext j htok
    obtain ⟨begun, hprev⟩ :=
      bankTrialDurationNextLiveOrigin
        ring root e z nextBegun hnext
    have hold : bankTrialLiveWaveToken z.bank j = .CL0 :=
      ((hframe nextBegun hnext).2.1 j).symm.trans htok
    obtain ⟨k, hmismatch⟩ :=
      hinv.zeroBackMismatch begun hprev j hold
    refine ⟨k, ?_⟩
    rw [(hframe nextBegun hnext).2.2 k]
    exact hmismatch

/-- On a proper top service the only potentially changed digit
token is the top IR. The invariant's carry<=K<2^b rules that
case out, so every actual digit bit/token is a frame. -/
theorem bankTrialDurationOrphanTopRow
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    BankTrialDurationOrphanInvEdge (q := q)
      ring root (Counter.site ring root (compileAdvice q).b) := by
  apply bankTrialDurationOrphanDigitFrameNext
    ring root (Counter.site ring root (compileAdvice q).b) hw
  intro B begun nextBegun hinv hnext
  have hf := bankTrialWindowLiveOldNotLatched
    ring root (Counter.site ring root (compileAdvice q).b)
    B begun nextBegun hnext
  have hbank := bankTrialLocalNextLiveBank
    ring root (Counter.site ring root (compileAdvice q).b)
    B begun
  have hfields := bankTrialDurationTopFieldsRow
    ring root hw B hf
  have hmode :
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q)
          (Counter.site ring root (compileAdvice q).b)).bank =
      bankTrialLiveWaveRootMode B := by
    rw [hbank]
    exact bankTrialDurationTopRootModeFrame ring root hw B hf
  have hslots :
      ∀ j : Fin (compileAdvice q).b,
        ((GrantBankReference.bankLocalReferenceStepClamped
          ring root B
          (Counter.site ring root (compileAdvice q).b)).fields
            ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩).2.1 =
          (B.fields
            ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩).2.1 ∧
        ((GrantBankReference.bankLocalReferenceStepClamped
          ring root B
          (Counter.site ring root (compileAdvice q).b)).fields
            ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩).2.2.1 =
          (B.fields
            ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩).2.2.1 := by
    intro j
    rw [hfields]
    by_cases ht : j.val + 1 = (compileAdvice q).b
    · simp only [Fin.val_mk, if_pos ht]
      constructor
      · rw [(bankTrialLiveClampBitToken q
          (GrantBankReference.topBoundaryBankMap
            (GrantBankReference.bankLocalReferenceCell B
              ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩))).1]
        rfl
      · rw [(bankTrialLiveClampBitToken q
          (GrantBankReference.topBoundaryBankMap
            (GrantBankReference.bankLocalReferenceCell B
              ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩))).2]
        change (GrantBankReference.topBoundaryBankMap
            (GrantBankReference.bankLocalReferenceCell B
              ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)).tok =
          (GrantBankReference.bankLocalReferenceCell B
            ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩).tok
        apply bankTrialLiveTopMapNoIR
        have htop : j = bankTrialDurationTopDigit q := by
          apply Fin.ext
          change j.val = (compileAdvice q).b - 1
          have hpos := bankTrialWindowWidthPos q
          omega
        change bankTrialLiveWaveToken B j ≠ .IR
        rw [htop]
        exact bankTrialDurationOrphanInvNoTopIR
          (⟨B, .live begun⟩ : BankTrialLocalState q)
          hinv hK begun rfl
    · simp only [Fin.val_mk, if_neg ht]
      constructor <;> first | trivial | rfl
  refine ⟨hmode, ?_, ?_⟩
  · intro j
    rw [hbank]
    change ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root (compileAdvice q).b)).fields
        ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩).2.2.1 =
      (B.fields ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩).2.2.1
    exact (hslots j).2
  · intro j
    rw [hbank]
    change ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root (compileAdvice q).b)).fields
        ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩).2.1 =
      (B.fields ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩).2.1
    exact (hslots j).1

/-- The literal incomingRootBankMap preserves mode or sets
RESET. A RESET observer successor cannot still be LIVE. -/
private theorem bankTrialDurationOrphanIncomingRawMode
    (x : BankCell) :
    (GrantBankReference.incomingRootBankMap x).mode = x.mode ∨
    (GrantBankReference.incomingRootBankMap x).mode = .RESET := by
  cases hm : x.mode <;>
    simp [GrantBankReference.incomingRootBankMap,
      hm, isWaitMode] <;>
    (repeat' split) <;> simp

/-- Incoming root changes no protected digit. If its successor
remains LIVE, it must preserve the root mode as well. -/
theorem bankTrialDurationOrphanIncomingRows
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q) :
    ∀ e : Fin n, ring.rightNeighbor e = root →
      BankTrialDurationOrphanInvEdge (q := q) ring root e := by
  intro e hin
  apply bankTrialDurationOrphanDigitFrameNext ring root e hw
  intro B begun nextBegun hinv hnext
  have hf := bankTrialWindowLiveOldNotLatched
    ring root e B begun nextBegun hnext
  have hbank := bankTrialLocalNextLiveBank
    ring root e B begun
  have hfields := bankTrialDurationIncomingFieldsRow
    ring root e hw hin B hf
  have hroot :
      bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) =
      (GrantBankReference.incomingRootBankMap
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by omega⟩)).mode := by
    change
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨0, by omega⟩).1 =
      (GrantBankReference.incomingRootBankMap
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by omega⟩)).mode
    rw [hfields]
    simp [GrantBankReference.bankLocalReferenceClampedQuad,
      GrantBankReference.bankAgentLeaseQuad, copyBank]
  have hraw := bankTrialDurationOrphanIncomingRawMode
    (GrantBankReference.bankLocalReferenceCell B
      ⟨0, by omega⟩)
  have hmodeRaw :
      (GrantBankReference.incomingRootBankMap
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by omega⟩)).mode =
        bankTrialLiveWaveRootMode B ∨
      (GrantBankReference.incomingRootBankMap
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by omega⟩)).mode = .RESET := by
    exact hraw
  have hnot := bankTrialDurationNextLiveNonreset
    ring root e B begun nextBegun hnext
  have hmodeStep :
      bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) = bankTrialLiveWaveRootMode B := by
    rcases hmodeRaw with hs | hr
    · exact hroot.trans hs
    · exact False.elim (hnot (hroot.trans hr))
  have hmode :
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank =
      bankTrialLiveWaveRootMode B := by
    rw [hbank]
    exact hmodeStep
  have hslots :
      ∀ j : Fin (compileAdvice q).b,
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e).fields
          ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ =
        B.fields ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := by
    intro j
    rw [hfields]
    have hn : j.val + 1 ≠ 0 := by omega
    simp only [Fin.val_mk, if_neg hn]
  refine ⟨hmode, ?_, ?_⟩
  · intro j
    rw [hbank]
    change ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields
        ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩).2.2.1 =
      (B.fields ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩).2.2.1
    rw [hslots j]
  · intro j
    rw [hbank]
    change ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields
        ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩).2.1 =
      (B.fields ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩).2.1
    rw [hslots j]

/-- The locked carry row gives root carry<=K: a LIVE ARMED
root spends at most one unit and begins strictly below K. -/
theorem bankTrialDurationOrphanRootCarryBound
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun nextBegun : Bool)
    (hinv : BankTrialDurationOrphanInv q
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q)
      root).phase = .live nextBegun) :
    bankTrialLiveCarryValue
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) root).bank ≤
      (compileAdvice q).K := by
  have hstep := bankTrialProbabilityLockedCarryLiveStep
    ring root root hw B begun nextBegun hinv.locked hnext
  have hdelta :
      (if BankTrialProbabilityArmedGate
        (⟨B, .live begun⟩ : BankTrialLocalState q) ∧
        root = root then 1 else 0) =
      (if bankTrialLiveWaveRootMode B = .ARMED
       then 1 else 0) := by
    by_cases hm : bankTrialLiveWaveRootMode B = .ARMED
    · have hg : BankTrialProbabilityArmedGate
          (⟨B, .live begun⟩ : BankTrialLocalState q) :=
        ⟨⟨begun, rfl⟩, hm⟩
      simp [hg, hm]
    · have hg : ¬ BankTrialProbabilityArmedGate
          (⟨B, .live begun⟩ : BankTrialLocalState q) := by
        intro h
        exact hm h.2
      simp [hg, hm]
  rw [hdelta] at hstep
  by_cases hm : bankTrialLiveWaveRootMode B = .ARMED
  · simp only [if_pos hm] at hstep
    have hprior := hinv.armedBeforeThreshold begun rfl hm
    change bankTrialLiveCarryValue B < (compileAdvice q).K at hprior
    omega
  · simp only [if_neg hm] at hstep
    have hprior := hinv.carryBound begun rfl
    change bankTrialLiveCarryValue B ≤ (compileAdvice q).K at hprior
    omega

/-- Nonaliased proper interior edges frame the root mode on a
LIVE successor. The missing cells concern tokens and mismatch. -/
theorem bankTrialDurationOrphanInteriorRootModeFrame
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun nextBegun : Bool)
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q)
      (Counter.site ring root j.val)).phase = .live nextBegun) :
    bankTrialLiveWaveRootMode
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)).bank =
      bankTrialLiveWaveRootMode B := by
  rw [bankTrialLocalNextLiveBank]
  exact bankTrialWindowInteriorRootModeFrame
    ring root hw B
    (bankTrialWindowLiveOldNotLatched
      ring root (Counter.site ring root j.val)
      B begun nextBegun hnext)
    j hj

/-- A conditional two-remaining-classes interface:
the earlier four-field structure is assembled only after
genuine root and interior proofs have been provided. -/
theorem bankTrialDurationOrphanRowsOfRootInterior
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hroot : BankTrialDurationOrphanInvEdge (q := q)
      ring root root)
    (hinterior : ∀ j : Fin (compileAdvice q).b, 0 < j.val →
      BankTrialDurationOrphanInvEdge (q := q)
        ring root (Counter.site ring root j.val)) :
    BankTrialDurationOrphanRows (q := q) ring root := by
  exact ⟨hroot, hinterior,
    bankTrialDurationOrphanTopRow ring root hw hK,
    bankTrialDurationOrphanIncomingRows ring root hw⟩

/-- No unconditional all-n theorem: two source-row premises
must still be proved on every invariant state. -/
theorem bankTrialDurationNoReachableOrphanOfRootInterior
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hroot : BankTrialDurationOrphanInvEdge (q := q)
      ring root root)
    (hinterior : ∀ j : Fin (compileAdvice q).b, 0 < j.val →
      BankTrialDurationOrphanInvEdge (q := q)
        ring root (Counter.site ring root j.val)) :
    BankTrialDurationNoReachableOrphan (q := q) ring root := by
  exact bankTrialDurationNoReachableOrphanHoldsOfRows
    ring root hsmall hw hpositive hK
    (bankTrialDurationOrphanRowsOfRootInterior
      ring root hw hK hroot hinterior)

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Under the supplied width bound the compiled theta word equals K. -/
private theorem bankTrialDurationOrphanThetaByWidth (q : Nat)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    bankTrialLiveThetaBinary q = (compileAdvice q).K := by
  by_cases hq : 3 ≤ q
  · exact bankTrialProbabilityThetaBinaryEqualsK q hq
  · have hsmall : q = 0 ∨ q = 1 ∨ q = 2 := by omega
    rcases hsmall with hz | ho | ht
    · subst q
      decide
    · subst q
      decide
    · subst q
      decide

/-- A negative comparator bit is a negative whole-word comparison. -/
private theorem bankTrialDurationOrphanMismatchBinary {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hwitness : ∃ k : Fin (compileAdvice q).b,
      bankTrialLiveWaveBit B k ≠ (compileAdvice q).theta k.val) :
    bankTrialLiveBinaryValue B ≠ bankTrialLiveThetaBinary q := by
  intro hvalue
  obtain ⟨k, hbad⟩ := hwitness
  have htheta := bankTrialDurationOrphanThetaByWidth q hK
  have hdigit := bankTrialC5BitValueDigit
    (compileAdvice q).b (bankTrialC5WindowBit B) k.val k.isLt
  rw [bankTrialC5BitValueWindow B, hvalue, htheta] at hdigit
  have htarget :
      (compileAdvice q).theta k.val =
        decide ((compileAdvice q).K / 2 ^ k.val % 2 = 1) := rfl
  have hmatch :
      bankTrialLiveWaveBit B k = (compileAdvice q).theta k.val := by
    calc
      bankTrialLiveWaveBit B k =
        bankTrialC5WindowBit B k.val :=
          (bankTrialC5WindowBitAt B k).symm
      _ = decide ((compileAdvice q).K / 2 ^ k.val % 2 = 1) :=
        hdigit
      _ = (compileAdvice q).theta k.val := htarget.symm
  exact hbad hmatch

/-- No CWAIT comparison token carries IR credit. -/
private theorem bankTrialDurationOrphanCWaitNoIR {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .CWAIT) :
    ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken B j ≠ .IR := by
  intro j
  exact (bankTrialLiveWaveCWaitNoWriters B hc hm j).1

/-- When no IR is present the carry equals the binary digit value. -/
private theorem bankTrialDurationOrphanCWaitCarryBinary {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hno : ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken B j ≠ .IR) :
    bankTrialLiveCarryValue B = bankTrialLiveBinaryValue B := by
  unfold bankTrialLiveCarryValue bankTrialLiveBinaryValue
  apply ofFn_sum_eq
  intro j
  change
    bankTrialLiveSlotPotential j.val
      (bankTrialLiveWaveBit B j) (bankTrialLiveWaveToken B j) =
      (if bankTrialLiveWaveBit B j then 2 ^ j.val else 0)
  simp [bankTrialLiveSlotPotential, hno j]

/-- An authenticated failed CL0 return has strict OLD carry < K. -/
theorem bankTrialDurationOrphanCWaitCLZeroStrict {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool)
    (hinv : BankTrialDurationOrphanInv q
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hm : bankTrialLiveWaveRootMode B = .CWAIT)
    (j : Fin (compileAdvice q).b)
    (hCL : bankTrialLiveWaveToken B j = .CL0) :
    bankTrialLiveCarryValue B < (compileAdvice q).K := by
  have hc : BankTrialLiveWaveCertificate q B :=
    hinv.locked.1 begun rfl
  have hcarry := bankTrialDurationOrphanCWaitCarryBinary B
    (bankTrialDurationOrphanCWaitNoIR B hc hm)
  have hwitness := hinv.zeroBackMismatch begun rfl j hCL
  have hbad := bankTrialDurationOrphanMismatchBinary B hK hwitness
  have htheta := bankTrialDurationOrphanThetaByWidth q hK
  have hnot : bankTrialLiveBinaryValue B ≠ (compileAdvice q).K := by
    intro heq
    exact hbad (heq.trans htheta.symm)
  have hbound := hinv.carryBound begun rfl
  change bankTrialLiveCarryValue B ≤ (compileAdvice q).K at hbound
  rw [hcarry] at hbound
  omega

/-- The locked field is already proved for the actual root service. -/
private theorem bankTrialDurationOrphanRootLockedField {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q)
    (hinv : BankTrialDurationOrphanInv q z) :
    BankTrialLiveNoResetLocked
      (bankTrialLocalNext ring root z root) := by
  exact bankTrialDurationOrphanLockedNext ring root root hw z hinv

/-- The actual selected root carryBound field. -/
theorem bankTrialDurationOrphanRootCarryField {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun nextBegun : Bool)
    (hinv : BankTrialDurationOrphanInv q
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q)
      root).phase = .live nextBegun) :
    bankTrialLiveCarryValue
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) root).bank ≤
    (compileAdvice q).K := by
  exact bankTrialDurationOrphanRootCarryBound
    ring root hw B begun nextBegun hinv hnext

/-- On the root raw owner, neither ARMED nor CSTART nor IWAIT
nor CWAIT can create RWAIT. -/
private theorem bankTrialDurationOrphanRawRootNoWait
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 < b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false)
    (hnr : x.mode ≠ .RESET) (hnw : x.mode ≠ .RWAIT) :
    (bankPair x y 1 b theta).1.mode ≠ .RWAIT := by
  have hpos : 1 ≤ b := by omega
  have hone : b ≠ 1 := by omega
  cases hm : x.mode with
  | RESET => exact False.elim (hnr hm)
  | RWAIT => exact False.elim (hnw hm)
  | ARMED =>
      cases ht : y.tok <;> cases hbit : y.bit <;>
        simp [bankPair, hx, hy, hg, hm, ht, hbit,
          hpos, hone, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp
  | IWAIT =>
      cases ht : y.tok <;>
        by_cases hl : 1 < x.lease <;>
        simp [bankPair, hx, hy, hg, hm, ht, hl,
          hpos, hone, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp
  | CSTART =>
      cases ht : y.tok <;> cases hbit : y.bit <;>
        simp [bankPair, hx, hy, hg, hm, ht, hbit,
          hpos, hone, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp
  | CWAIT =>
      cases ht : y.tok <;>
        by_cases hl : 1 < x.lease <;>
        simp [bankPair, hx, hy, hg, hm, ht, hl,
          hpos, hone, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp

/-- The root noLiveResetWait field, using the physical clamped map. -/
theorem bankTrialDurationOrphanRootNoWaitField {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun nextBegun : Bool)
    (hinv : BankTrialDurationOrphanInv q
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q)
      root).phase = .live nextBegun) :
    bankTrialLiveWaveRootMode
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        root).bank ≠ .RWAIT := by
  have hf := bankTrialWindowLiveOldNotLatched
    ring root root B begun nextBegun hnext
  have hfields := bankTrialDurationRootFieldsRow ring root hw B hf
  have hmode :
      bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) =
      (GrantBankReference.bankLocalReferenceInternalPair q B
        ⟨0, by have := bankTrialWindowWidthPos q; omega⟩).1.mode := by
    change
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B root).fields ⟨0, by have := bankTrialWindowWidthPos q; omega⟩).1 =
      (GrantBankReference.bankLocalReferenceInternalPair q B
        ⟨0, by have := bankTrialWindowWidthPos q; omega⟩).1.mode
    rw [hfields]
    simp [GrantBankReference.bankLocalReferenceClampedQuad,
      GrantBankReference.bankAgentLeaseQuad, copyBank]
  have hraw :
      (GrantBankReference.bankLocalReferenceInternalPair q B
        ⟨0, by have := bankTrialWindowWidthPos q; omega⟩).1.mode ≠ .RWAIT := by
    change (bankPair
      (GrantBankReference.bankLocalReferenceCell B
        ⟨0, by have := bankTrialWindowWidthPos q; omega⟩)
      (GrantBankReference.bankLocalReferenceCell B
        ⟨1, by have hb := bankTrialWindowWidthPos q; omega⟩)
      1 (compileAdvice q).b (compileAdvice q).theta).1.mode ≠ .RWAIT
    exact bankTrialDurationOrphanRawRootNoWait
      (compileAdvice q).b (compileAdvice q).theta
      (GrantBankReference.bankLocalReferenceCell B
        ⟨0, by have := bankTrialWindowWidthPos q; omega⟩)
      (GrantBankReference.bankLocalReferenceCell B
        ⟨1, by have hb := bankTrialWindowWidthPos q; omega⟩)
      (by change 1 < (compileAdvice q).s + 11; omega)
      rfl rfl rfl
      (hinv.locked.2 begun rfl)
      (hinv.noLiveResetWait begun rfl)
  rw [bankTrialLocalNextLiveBank ring root root B begun, hmode]
  exact hraw

/-- The interior locked field is an existing nonaliased-row result. -/
private theorem bankTrialDurationOrphanInteriorLockedField {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (z : BankTrialLocalState q)
    (hinv : BankTrialDurationOrphanInv q z) :
    BankTrialLiveNoResetLocked
      (bankTrialLocalNext ring root z
        (Counter.site ring root j.val)) := by
  exact bankTrialDurationOrphanLockedNext ring root
    (Counter.site ring root j.val) hw z hinv

/-- Proper interior service cannot increase the complete carry. -/
theorem bankTrialDurationOrphanInteriorCarryNonincrease {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun nextBegun : Bool)
    (hlock : BankTrialLiveNoResetLocked
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q)
      (Counter.site ring root j.val)).phase = .live nextBegun) :
    bankTrialLiveCarryValue
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)).bank ≤
    bankTrialLiveCarryValue B := by
  have hnotroot :=
    bankTrialWindowInteriorNotRoot ring root hw j hj
  have hzero :
      ¬ (BankTrialProbabilityArmedGate
        (⟨B, .live begun⟩ : BankTrialLocalState q) ∧
        Counter.site ring root j.val = root) := by
    intro h
    exact hnotroot h.2
  have hstep := bankTrialProbabilityLockedCarryLiveStep
    ring root (Counter.site ring root j.val) hw
    B begun nextBegun hlock hnext
  simpa only [if_neg hzero, Nat.add_zero] using hstep

/-- Proper interior noLiveResetWait field. -/
theorem bankTrialDurationOrphanInteriorNoWaitField {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun nextBegun : Bool)
    (hinv : BankTrialDurationOrphanInv q
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q)
      (Counter.site ring root j.val)).phase = .live nextBegun) :
    bankTrialLiveWaveRootMode
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)).bank ≠ .RWAIT := by
  rw [bankTrialDurationOrphanInteriorRootModeFrame
    ring root hw j hj B begun nextBegun hnext]
  exact hinv.noLiveResetWait begun rfl

/-- Proper interior carryBound field. -/
theorem bankTrialDurationOrphanInteriorCarryField {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun nextBegun : Bool)
    (hinv : BankTrialDurationOrphanInv q
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q)
      (Counter.site ring root j.val)).phase = .live nextBegun) :
    bankTrialLiveCarryValue
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)).bank ≤
    (compileAdvice q).K := by
  have hstep := bankTrialDurationOrphanInteriorCarryNonincrease
    ring root hw j hj B begun nextBegun hinv.locked hnext
  have hprior := hinv.carryBound begun rfl
  change bankTrialLiveCarryValue B ≤ (compileAdvice q).K at hprior
  exact Nat.le_trans hstep hprior

/-- Proper interior armedBeforeThreshold field. -/
theorem bankTrialDurationOrphanInteriorArmedField {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun nextBegun : Bool)
    (hinv : BankTrialDurationOrphanInv q
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q)
      (Counter.site ring root j.val)).phase = .live nextBegun)
    (harmed : bankTrialLiveWaveRootMode
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)).bank = .ARMED) :
    bankTrialLiveCarryValue
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)).bank <
    (compileAdvice q).K := by
  have hmode := bankTrialDurationOrphanInteriorRootModeFrame
    ring root hw j hj B begun nextBegun hnext
  have hold : bankTrialLiveWaveRootMode B = .ARMED :=
    hmode.symm.trans harmed
  have hprior := hinv.armedBeforeThreshold begun rfl hold
  change bankTrialLiveCarryValue B < (compileAdvice q).K at hprior
  have hstep := bankTrialDurationOrphanInteriorCarryNonincrease
    ring root hw j hj B begun nextBegun hinv.locked hnext
  exact Nat.lt_of_le_of_lt hstep hprior

end L3

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The exact original-clock charge over K correct HEAD labels,
including paths which subsequently LOST or are still LIVE. This is
strictly larger than the WON-only cost observer and is not itself
a success-conditioned cost. -/
noncomputable def bankTrialDurationAllKHeadCostMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) : Nat :=
  Prob.scheduleSum n T (fun w =>
    if bankTrialProbabilityHeadEvent ring root w
        (compileAdvice q).K (bankTrialLocalStart S) then
      costWord (bankTrialLocalNext ring root)
        bankTrialLocalTerminal (bankTrialLocalStart S) w
    else 0)

/-- FIRST MISSING FACT FOR G12e. The all-K-HEAD event includes
every successful word, but also selected words whose workers
abort after correct head labels. This bound is stronger than the
desired WON-only inequality, and is NOT asserted as a theorem.
Its factor 3/4 must come from a literal, adapted watchdog
survival coupling for the K labelled worker excursions; C.6's
three unconditional budgets cannot establish it. The C.6 premise
is provided by those budgets, not postulated at a CLEAN cut.
The physical domain is the paper's spatial branch only. -/
def BankTrialDurationAllKHeadWorkerPathCost {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    BankTrialLocalClean q S →
    (compileAdvice q).useSmall = false →
    2 * (compileAdvice q).bankLeaseCap ≤ n →
    ∀ T : Nat,
      costNumerator (bankTrialLocalNext ring root)
        bankTrialLocalTerminal (bankTrialLocalStart S) T ≤
          n ^ T * ((8 * (compileAdvice q).b + 12) * n) →
      3 * bankTrialDurationAllKHeadCostMass ring root S T ≤
        4 * (bankTrialProbabilityWinMass ring root S T +
          bankTrialDurationActiveMass ring root S T) *
          ((2 * (2 * (compileAdvice q).b + 2) + 2) *
            ((compileAdvice q).K + 1) * n)

/-- Genuine CLEAN-start WON words authenticate all K head labels.
This uses the existing locked-window comparator credit and carry
ledger, not a guess about an arbitrary forged CWAIT snapshot. -/
theorem bankTrialDurationWinHasAllHeads {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (w : List (Fin n))
    (hwin : (bankTrialLocalRun ring root w
      (bankTrialLocalStart S)).phase = .won) :
    bankTrialProbabilityHeadEvent ring root w
      (compileAdvice q).K (bankTrialLocalStart S) := by
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hn : 2 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    omega
  have hq : 3 ≤ q := by
    have hsmall : (compileAdvice q).useSmall =
        decide (q ≤ qStar) := rfl
    rw [hsmall] at hsp
    have hnot : ¬ q ≤ qStar := of_decide_eq_false hsp
    change ¬ q ≤ 79 at hnot
    omega
  have htheta : (compileAdvice q).K ≤
      bankTrialLiveThetaBinary q := by
    rw [bankTrialProbabilityThetaBinaryEqualsK q hq]
    exact Nat.le_refl _
  have htrace :=
    bankTrialProbabilityCleanWinGuardTrace
      ring root hn S hclean
  obtain ⟨pre, suffix, B, begun, hword, hpre, hm, ht⟩ :=
    htrace w hwin
  have hcredit := bankTrialProbabilityCleanWordsComparatorCredit
    ring root hw S hclean htheta pre
  rw [hpre] at hcredit
  have hcarry := bankTrialProbabilityLockedCarryCleanWords
    ring root hw S hclean pre
  rw [hpre] at hcarry
  have hpreHeads : (compileAdvice q).K ≤
      bankTrialLiveHeadCount ring root pre
        (bankTrialLocalStart S) :=
    Nat.le_trans (hcredit begun rfl hm ht) (hcarry begun rfl)
  have hwholeHeads :
      bankTrialLiveHeadCount ring root pre
          (bankTrialLocalStart S) ≤
        bankTrialLiveHeadCount ring root w
          (bankTrialLocalStart S) := by
    rw [hword, bankTrialLiveHeadCountAppend]
    omega
  have hno := bankTrialProbabilityCleanWinNoArmedIncoming
    ring root hn S hclean w hwin
  exact bankTrialHeadEventOfCount
    ring root w (compileAdvice q).K (bankTrialLocalStart S)
    hno (Nat.le_trans hpreHeads hwholeHeads)

/-- The all-K-head cost counts EVERY completed WON word, with its
unchanged stopped costWord, pointwise on the same Fin n tape. -/
theorem bankTrialDurationSuccessCostLeAllHeads {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (T : Nat) :
    bankTrialDurationSuccessCostMass ring root S T ≤
      bankTrialDurationAllKHeadCostMass ring root S T := by
  unfold bankTrialDurationSuccessCostMass
    bankTrialDurationAllKHeadCostMass
  apply bankTrialProbabilityScheduleSumMono n T
  intro w
  by_cases hw :
      (bankTrialLocalRun ring root w
        (bankTrialLocalStart S)).phase = .won
  · have hh := bankTrialDurationWinHasAllHeads
      ring root S hclean hsp hlarge w hw
    simp only [if_pos hw, if_pos hh]
    exact Nat.le_refl _
  · simp only [if_neg hw]
    exact Nat.zero_le _

/-- The paper's coefficient is twice the mean unobstructed
all-head worker-path coefficient; opaque b,K,n are plain Nats. -/
private theorem bankTrialDurationSuccessCoefficient
    (b K n : Nat) :
    (8 * b + 12) * (K + 1) * n =
      2 * ((2 * (2 * b + 2) + 2) * (K + 1) * n) := by
  have hfactor :
      8 * b + 12 = 2 * (2 * (2 * b + 2) + 2) := by
    omega
  rw [hfactor]
  simp only [Nat.mul_assoc]

/-- Pure Nat conditional-charge cancellation: 4/3 of one worker
path budget is below twice that budget. No division or Real mass. -/
private theorem bankTrialDurationSuccessChargeArithmetic
    (cost nonfailure worker : Nat)
    (hcharge : 3 * cost ≤ 4 * nonfailure * worker) :
    cost ≤ nonfailure * (2 * worker) := by
  have hcoef : 4 ≤ 6 := by omega
  have hstep :
      4 * nonfailure * worker ≤
        3 * (nonfailure * (2 * worker)) := by
    calc
      4 * nonfailure * worker =
          4 * (nonfailure * worker) := by
            rw [Nat.mul_assoc]
      _ ≤ 6 * (nonfailure * worker) :=
        Nat.mul_le_mul_right _ hcoef
      _ = 3 * (nonfailure * (2 * worker)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have htriple :
      3 * cost ≤ 3 * (nonfailure * (2 * worker)) :=
    Nat.le_trans hcharge hstep
  omega

/-- G12e: the spatial (q>=80, nonalias) version of the actual
finite-prefix success-conditioned target. The three original C.6
budgets provide the unconditional first-hit cost; the ONE new
missing physical fact is the all-K-head path cost above.
No totality/survival assumption is silently obtained from C.6.
The unrestricted target at line 464 is not asserted. -/
theorem bankTrialDurationSuccessConditionalOfBudgets {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hrace : BankTrialDurationRaceBudget (q := q) ring root)
    (hworker : BankTrialDurationWorkerBudget (q := q) ring root)
    (hreset : BankTrialDurationRecoveryBudget (q := q) ring root)
    (hpaths : BankTrialDurationAllKHeadWorkerPathCost
      (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (T : Nat) :
    bankTrialDurationSuccessCostMass ring root S T ≤
      (bankTrialProbabilityWinMass ring root S T +
        bankTrialDurationActiveMass ring root S T) *
        ((8 * (compileAdvice q).b + 12) *
          ((compileAdvice q).K + 1) * n) := by
  have hC6 := bankTrialDurationC6OfBudgets
    ring root hrace hworker hreset S hclean T
  have hpath := hpaths S hclean hsp hlarge T hC6
  have hsub := bankTrialDurationSuccessCostLeAllHeads
    ring root S hclean hsp hlarge T
  have htriple :
      3 * bankTrialDurationSuccessCostMass ring root S T ≤
        4 * (bankTrialProbabilityWinMass ring root S T +
          bankTrialDurationActiveMass ring root S T) *
          ((2 * (2 * (compileAdvice q).b + 2) + 2) *
            ((compileAdvice q).K + 1) * n) :=
    Nat.le_trans (Nat.mul_le_mul_left 3 hsub) hpath
  have hbound := bankTrialDurationSuccessChargeArithmetic
    (bankTrialDurationSuccessCostMass ring root S T)
    (bankTrialProbabilityWinMass ring root S T +
      bankTrialDurationActiveMass ring root S T)
    ((2 * (2 * (compileAdvice q).b + 2) + 2) *
      ((compileAdvice q).K + 1) * n)
    htriple
  rw [bankTrialDurationSuccessCoefficient
    (compileAdvice q).b (compileAdvice q).K n]
  exact hbound

/-- A concrete n=5 CLEAN reference, to make the test domain
nonempty. It is NOT a spatially nonalias C.8 test instance. -/
def bankTrialDurationFiveCleanReference (q : Nat) :
    GrantBankReference.BankLocalReference (compileAdvice q).b :=
  { fields := fun i =>
      if i.val = 0 then (.ARMED, false, .E, 0)
      else (.RESET, false, .E, 0)
    success := false }

theorem bankTrialDurationFiveCleanWitness (q : Nat) :
    BankTrialLocalClean q
      (bankTrialDurationFiveCleanReference q) := by
  unfold BankTrialLocalClean
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [bankTrialDurationFiveCleanReference]
  · intro j hj hbound
    have hnonzero : j ≠ 0 := by omega
    simp [bankTrialDurationFiveCleanReference, hnonzero]
  · intro j hj
    simp [bankTrialDurationFiveCleanReference]

/-- The demanded non-vacuous n=5 check CANNOT test the spatial
C.8 premises: bankLeaseCap = 13*(b+2) already exceeds 2. -/
theorem bankTrialDurationFiveNonaliasImpossible (q : Nat) :
    ¬ 2 * (compileAdvice q).bankLeaseCap ≤ 5 := by
  intro h
  change 2 * (13 * ((compileAdvice q).b + 2)) ≤ 5 at h
  omega

/-- A small closed T=0 check on the actual CLEAN n=5 seed.
It verifies that finite-prefix success cost starts at zero,
but does NOT discharge the all-T all-K-head missing Prop. -/
theorem bankTrialDurationFiveCleanZeroHorizon (q : Nat) :
    bankTrialDurationSuccessCostMass
      (⟨by decide⟩ : DirectedRing 5) (0 : Fin 5)
      (bankTrialDurationFiveCleanReference q) 0 = 0 := by
  unfold bankTrialDurationSuccessCostMass
  rw [bankTrialProbabilityScheduleSumZero]
  simp [bankTrialLocalRun, bankTrialLocalStart]

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- A zero-valued leftward comparator token can occur only in CWAIT. -/
private theorem bankTrialDurationOrphanCLZeroRequiresCWait {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (hnr : bankTrialLiveWaveRootMode B ≠ .RESET)
    (hnw : bankTrialLiveWaveRootMode B ≠ .RWAIT)
    (j : Fin (compileAdvice q).b)
    (hCL : bankTrialLiveWaveToken B j = .CL0) :
    bankTrialLiveWaveRootMode B = .CWAIT := by
  cases hm : bankTrialLiveWaveRootMode B with
  | RESET => exact False.elim (hnr hm)
  | RWAIT => exact False.elim (hnw hm)
  | ARMED =>
      have he := hc.headClear j (Or.inl hm)
      rw [he] at hCL
      cases hCL
  | CSTART =>
      have he := hc.headClear j (Or.inr hm)
      rw [he] at hCL
      cases hCL
  | IWAIT =>
      rcases hc.iwaitTokens j hm with ht | ht | ht
      · rw [ht] at hCL
        cases hCL
      · rw [ht] at hCL
        cases hCL
      · rw [ht] at hCL
        cases hCL
  | CWAIT => rfl

/-- A zero-valued rightward comparator token can occur only in CWAIT. -/
private theorem bankTrialDurationOrphanCRZeroRequiresCWait {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (hnr : bankTrialLiveWaveRootMode B ≠ .RESET)
    (hnw : bankTrialLiveWaveRootMode B ≠ .RWAIT)
    (j : Fin (compileAdvice q).b)
    (hCR : bankTrialLiveWaveToken B j = .CR0) :
    bankTrialLiveWaveRootMode B = .CWAIT := by
  cases hm : bankTrialLiveWaveRootMode B with
  | RESET => exact False.elim (hnr hm)
  | RWAIT => exact False.elim (hnw hm)
  | ARMED =>
      have he := hc.headClear j (Or.inl hm)
      rw [he] at hCR
      cases hCR
  | CSTART =>
      have he := hc.headClear j (Or.inr hm)
      rw [he] at hCR
      cases hCR
  | IWAIT =>
      rcases hc.iwaitTokens j hm with ht | ht | ht
      · rw [ht] at hCR
        cases hCR
      · rw [ht] at hCR
        cases hCR
      · rw [ht] at hCR
        cases hCR
  | CWAIT => rfl

/-- The literal outgoing-root owner can produce a fresh ARMED root
only by consuming CL0 in CWAIT. -/
private theorem bankTrialDurationOrphanRawRootNewArmedOnlyCLZero
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 < b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false)
    (hnr : x.mode ≠ .RESET) (hnw : x.mode ≠ .RWAIT)
    (hhead : (x.mode = .ARMED ∨ x.mode = .CSTART) →
      y.tok = .E)
    (hnew : (bankPair x y 1 b theta).1.mode = .ARMED) :
    x.mode = .CWAIT ∧ y.tok = .CL0 := by
  have hbpos : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  cases hm : x.mode with
  | RESET => exact False.elim (hnr hm)
  | RWAIT => exact False.elim (hnw hm)
  | ARMED =>
      have ht := hhead (Or.inl hm)
      cases hbit : y.bit <;>
        simp [bankPair, hx, hy, hg, hm, ht, hbit,
          hbpos, hbne, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] at hnew
  | CSTART =>
      have ht := hhead (Or.inr hm)
      simp [bankPair, hx, hy, hg, hm, ht,
        hbpos, hbne, isRetTok, isWaitMode,
        Id.run_pure, Id.run_bind] at hnew
  | IWAIT =>
      cases ht : y.tok <;>
        by_cases hl : 1 < x.lease <;>
        simp [bankPair, hx, hy, hg, hm, ht, hl,
          hbpos, hbne, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] at hnew
  | CWAIT =>
      cases ht : y.tok <;>
        by_cases hl : 1 < x.lease <;>
        simp [bankPair, hx, hy, hg, hm, ht, hl,
          hbpos, hbne, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] at hnew ⊢

/-- Strict ARMED carry after an outgoing-root service.  Old ARMED
uses the installed strict threshold; newly ARMED is the CWAIT/CL0
return and uses the authenticated negative predecessor. -/
theorem bankTrialDurationOrphanRootArmedField {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun nextBegun : Bool)
    (hinv : BankTrialDurationOrphanInv q
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) root).phase =
        .live nextBegun)
    (harmed : bankTrialLiveWaveRootMode
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) root).bank =
        .ARMED) :
    bankTrialLiveCarryValue
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) root).bank <
      (compileAdvice q).K := by
  have hf := bankTrialWindowLiveOldNotLatched
    ring root root B begun nextBegun hnext
  have hbank := bankTrialLocalNextLiveBank ring root root B begun
  have hc : BankTrialLiveWaveCertificate q B :=
    hinv.locked.1 begun rfl
  have hhead :
      ((GrantBankReference.bankLocalReferenceCell B
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩).mode = .ARMED ∨
       (GrantBankReference.bankLocalReferenceCell B
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩).mode = .CSTART) →
      (GrantBankReference.bankLocalReferenceCell B
        ⟨1, by have hb := bankTrialCmpWidth q; omega⟩).tok = .E := by
    intro hm
    exact hc.headClear
      ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ hm
  rw [hbank] at harmed
  have hproj := bankTrialCmpRoot ring root hw B hf
  have hrawArmed :
      (GrantBankReference.bankLocalReferenceInternalPair q B
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩).1.mode = .ARMED :=
    hproj.1.symm.trans harmed
  have hraw := bankTrialDurationOrphanRawRootNewArmedOnlyCLZero
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨0, by have hb := bankTrialCmpWidth q; omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
    (by have hb := bankTrialCmpWidth q; omega)
    rfl rfl rfl
    (hinv.locked.2 begun rfl)
    (hinv.noLiveResetWait begun rfl)
    hhead hrawArmed
  have hcwait : bankTrialLiveWaveRootMode B = .CWAIT := hraw.1
  have hstrict := bankTrialDurationOrphanCWaitCLZeroStrict
    B begun hinv hK hcwait
    ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ hraw.2
  have hstep := bankTrialProbabilityLockedCarryLiveStep
    ring root root hw B begun nextBegun hinv.locked hnext
  have hzero :
      ¬ (BankTrialProbabilityArmedGate
        (⟨B, .live begun⟩ : BankTrialLocalState q) ∧ root = root) := by
    intro h
    have hold := h.1.2
    change bankTrialLiveWaveRootMode B = .ARMED at hold
    rw [hcwait] at hold
    cases hold
  rw [if_neg hzero, Nat.add_zero] at hstep
  exact Nat.lt_of_le_of_lt hstep hstrict

/-- A head-clear root service which leaves a wait mode creates its
worker at digit zero. -/
private theorem bankTrialDurationOrphanRawRootStartsWorker
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 < b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false)
    (hm : x.mode = .ARMED ∨ x.mode = .CSTART)
    (ht : y.tok = .E)
    (hnew : (bankPair x y 1 b theta).1.mode = .IWAIT ∨
      (bankPair x y 1 b theta).1.mode = .CWAIT) :
    (bankPair x y 1 b theta).2.tok ≠ .E := by
  have hbpos : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  rcases hm with hm | hm
  · cases hbit : y.bit <;>
      simp [bankPair, hx, hy, hg, hm, ht, hbit,
        hbpos, hbne, isRetTok, isWaitMode,
        Id.run_pure, Id.run_bind] at hnew ⊢
  · cases hbit : y.bit <;> cases htheta : theta 0 <;>
      simp [bankPair, hx, hy, hg, hm, ht, hbit, htheta,
        hbpos, hbne, isRetTok, isWaitMode,
        Id.run_pure, Id.run_bind] at hnew ⊢

/-- If the old digit-zero worker belongs to the old wait stage and
the root remains in a wait stage, that worker is not erased. -/
private theorem bankTrialDurationOrphanRawRootWaitWorker
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 < b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false)
    (hstage :
      (x.mode = .IWAIT ∧ (y.tok = .IR ∨ y.tok = .AL)) ∨
      (x.mode = .CWAIT ∧
        (y.tok = .CR0 ∨ y.tok = .CR1 ∨
         y.tok = .CL0 ∨ y.tok = .CL1)))
    (hnew : (bankPair x y 1 b theta).1.mode = .IWAIT ∨
      (bankPair x y 1 b theta).1.mode = .CWAIT) :
    (bankPair x y 1 b theta).2.tok ≠ .E := by
  have hbpos : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  rcases hstage with ⟨hm, hir | hal⟩ |
      ⟨hm, hcrzero | hcrone | hclzero | hclone⟩
  · by_cases hl : 1 < x.lease <;>
      simp [bankPair, hx, hy, hg, hm, hir, hl,
        hbpos, hbne, isRetTok, isWaitMode,
        Id.run_pure, Id.run_bind] at hnew ⊢
  · by_cases hl : 1 < x.lease <;>
      simp [bankPair, hx, hy, hg, hm, hal, hl,
        hbpos, hbne, isRetTok, isWaitMode,
        Id.run_pure, Id.run_bind] at hnew ⊢
  · by_cases hl : 1 < x.lease <;>
      simp [bankPair, hx, hy, hg, hm, hcrzero, hl,
        hbpos, hbne, isRetTok, isWaitMode,
        Id.run_pure, Id.run_bind] at hnew ⊢
  · by_cases hl : 1 < x.lease <;>
      simp [bankPair, hx, hy, hg, hm, hcrone, hl,
        hbpos, hbne, isRetTok, isWaitMode,
        Id.run_pure, Id.run_bind] at hnew ⊢
  · by_cases hl : 1 < x.lease <;>
      simp [bankPair, hx, hy, hg, hm, hclzero, hl,
        hbpos, hbne, isRetTok, isWaitMode,
        Id.run_pure, Id.run_bind] at hnew ⊢
  · by_cases hl : 1 < x.lease <;>
      simp [bankPair, hx, hy, hg, hm, hclone, hl,
        hbpos, hbne, isRetTok, isWaitMode,
        Id.run_pure, Id.run_bind] at hnew ⊢

/-- Outgoing-root preservation of the explicit non-orphan field. -/
theorem bankTrialDurationOrphanRootWorkerField {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun nextBegun : Bool)
    (hinv : BankTrialDurationOrphanInv q
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) root).phase =
        .live nextBegun)
    (hmode : bankTrialLiveWaveRootMode
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) root).bank = .IWAIT ∨
      bankTrialLiveWaveRootMode
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) root).bank = .CWAIT) :
    ∃ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) root).bank j ≠ .E := by
  have hf := bankTrialWindowLiveOldNotLatched
    ring root root B begun nextBegun hnext
  have hbank := bankTrialLocalNextLiveBank ring root root B begun
  have hcmp := bankTrialCmpRoot ring root hw B hf
  have hc : BankTrialLiveWaveCertificate q B :=
    hinv.locked.1 begun rfl
  rw [hbank] at hmode ⊢
  have hrawMode :
      (GrantBankReference.bankLocalReferenceInternalPair q B
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩).1.mode = .IWAIT ∨
      (GrantBankReference.bankLocalReferenceInternalPair q B
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩).1.mode = .CWAIT := by
    rcases hmode with hm | hm
    · exact Or.inl (hcmp.1.symm.trans hm)
    · exact Or.inr (hcmp.1.symm.trans hm)
  cases hmold : bankTrialLiveWaveRootMode B with
  | RESET => exact False.elim ((hinv.locked.2 begun rfl) hmold)
  | RWAIT => exact False.elim ((hinv.noLiveResetWait begun rfl) hmold)
  | ARMED =>
      have hold := hc.headClear
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ (Or.inl hmold)
      have hraw := bankTrialDurationOrphanRawRootStartsWorker
        (compileAdvice q).b (compileAdvice q).theta
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by have hb := bankTrialCmpWidth q; omega⟩)
        (GrantBankReference.bankLocalReferenceCell B
          ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
        (by have hb := bankTrialCmpWidth q; omega)
        rfl rfl rfl (Or.inl hmold) hold hrawMode
      refine ⟨⟨0, by have hb := bankTrialCmpWidth q; omega⟩, ?_⟩
      rw [((hcmp.2
        (⟨0, by have hb := bankTrialCmpWidth q; omega⟩ :
          Fin (compileAdvice q).b)).1 rfl).2]
      exact hraw
  | CSTART =>
      have hold := hc.headClear
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ (Or.inr hmold)
      have hraw := bankTrialDurationOrphanRawRootStartsWorker
        (compileAdvice q).b (compileAdvice q).theta
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by have hb := bankTrialCmpWidth q; omega⟩)
        (GrantBankReference.bankLocalReferenceCell B
          ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
        (by have hb := bankTrialCmpWidth q; omega)
        rfl rfl rfl (Or.inr hmold) hold hrawMode
      refine ⟨⟨0, by have hb := bankTrialCmpWidth q; omega⟩, ?_⟩
      rw [((hcmp.2
        (⟨0, by have hb := bankTrialCmpWidth q; omega⟩ :
          Fin (compileAdvice q).b)).1 rfl).2]
      exact hraw
  | IWAIT =>
      obtain ⟨j, hj⟩ := hinv.workerPresent begun rfl (Or.inl hmold)
      by_cases hz : j.val = 0
      · have heq : j =
            ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ := Fin.ext hz
        have hyne :
            (GrantBankReference.bankLocalReferenceCell B
              ⟨1, by have hb := bankTrialCmpWidth q; omega⟩).tok ≠ .E := by
          change bankTrialLiveWaveToken B
            ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ ≠ .E
          rw [← heq]
          exact hj
        have hcase :
            (GrantBankReference.bankLocalReferenceCell B
              ⟨1, by have hb := bankTrialCmpWidth q; omega⟩).tok = .IR ∨
            (GrantBankReference.bankLocalReferenceCell B
              ⟨1, by have hb := bankTrialCmpWidth q; omega⟩).tok = .AL := by
          rcases hc.iwaitTokens
            ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ hmold with
              he | hir | hal
          · exact False.elim (hyne he)
          · exact Or.inl hir
          · exact Or.inr hal
        have hraw := bankTrialDurationOrphanRawRootWaitWorker
          (compileAdvice q).b (compileAdvice q).theta
          (GrantBankReference.bankLocalReferenceCell B
            ⟨0, by have hb := bankTrialCmpWidth q; omega⟩)
          (GrantBankReference.bankLocalReferenceCell B
            ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
          (by have hb := bankTrialCmpWidth q; omega)
          rfl rfl rfl (Or.inl ⟨hmold, hcase⟩) hrawMode
        refine ⟨⟨0, by have hb := bankTrialCmpWidth q; omega⟩, ?_⟩
        rw [((hcmp.2
          (⟨0, by have hb := bankTrialCmpWidth q; omega⟩ :
            Fin (compileAdvice q).b)).1 rfl).2]
        exact hraw
      · refine ⟨j, ?_⟩
        rw [((hcmp.2 j).2 hz).2]
        exact hj
  | CWAIT =>
      obtain ⟨j, hj⟩ := hinv.workerPresent begun rfl (Or.inr hmold)
      by_cases hz : j.val = 0
      · have heq : j =
            ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ := Fin.ext hz
        have hyne :
            (GrantBankReference.bankLocalReferenceCell B
              ⟨1, by have hb := bankTrialCmpWidth q; omega⟩).tok ≠ .E := by
          change bankTrialLiveWaveToken B
            ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ ≠ .E
          rw [← heq]
          exact hj
        have hcase :
            (GrantBankReference.bankLocalReferenceCell B
              ⟨1, by have hb := bankTrialCmpWidth q; omega⟩).tok = .CR0 ∨
            (GrantBankReference.bankLocalReferenceCell B
              ⟨1, by have hb := bankTrialCmpWidth q; omega⟩).tok = .CR1 ∨
            (GrantBankReference.bankLocalReferenceCell B
              ⟨1, by have hb := bankTrialCmpWidth q; omega⟩).tok = .CL0 ∨
            (GrantBankReference.bankLocalReferenceCell B
              ⟨1, by have hb := bankTrialCmpWidth q; omega⟩).tok = .CL1 := by
          rcases hc.cwaitTokens
            ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ hmold with
              he | hcomp
          · exact False.elim (hyne he)
          · exact hcomp
        have hraw := bankTrialDurationOrphanRawRootWaitWorker
          (compileAdvice q).b (compileAdvice q).theta
          (GrantBankReference.bankLocalReferenceCell B
            ⟨0, by have hb := bankTrialCmpWidth q; omega⟩)
          (GrantBankReference.bankLocalReferenceCell B
            ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
          (by have hb := bankTrialCmpWidth q; omega)
          rfl rfl rfl (Or.inr ⟨hmold, hcase⟩) hrawMode
        refine ⟨⟨0, by have hb := bankTrialCmpWidth q; omega⟩, ?_⟩
        rw [((hcmp.2
          (⟨0, by have hb := bankTrialCmpWidth q; omega⟩ :
            Fin (compileAdvice q).b)).1 rfl).2]
        exact hraw
      · refine ⟨j, ?_⟩
        rw [((hcmp.2 j).2 hz).2]
        exact hj

/-- The root service cannot create CL0 at digit zero. -/
private theorem bankTrialDurationOrphanRawRootNeverProducesCLZero
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 < b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false) :
    (bankPair x y 1 b theta).2.tok ≠ .CL0 := by
  have hbpos : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  cases hm : x.mode <;> cases ht : y.tok <;>
    simp [bankPair, hx, hy, hg, hm, ht,
      hbpos, hbne, isRetTok, isWaitMode,
      Id.run_pure, Id.run_bind] <;>
    (repeat' split) <;> simp

/-- CWAIT root service frames all protected bits. -/
private theorem bankTrialDurationOrphanCWaitRootBitFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hf : B.success = false)
    (hcwait : bankTrialLiveWaveRootMode B = .CWAIT) :
    ∀ i : Fin (compileAdvice q).b,
      bankTrialLiveWaveBit
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) i = bankTrialLiveWaveBit B i := by
  have hcmp := bankTrialCmpRoot ring root hw B hf
  have hraw := bankTrialLiveRawCWaitBitFrame
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨0, by have hb := bankTrialCmpWidth q; omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
    (by have hb := bankTrialCmpWidth q; omega)
    rfl rfl rfl hcwait
  intro i
  by_cases hi : i.val = 0
  · have heq : i =
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ := Fin.ext hi
    rw [heq]
    calc
      bankTrialLiveWaveBit
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B root)
          ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ =
        (GrantBankReference.bankLocalReferenceInternalPair q B
          ⟨0, by have hb := bankTrialCmpWidth q; omega⟩).2.bit :=
        ((hcmp.2
          (⟨0, by have hb := bankTrialCmpWidth q; omega⟩ :
            Fin (compileAdvice q).b)).1 rfl).1
      _ = bankTrialLiveWaveBit B
          ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ := hraw
  · exact ((hcmp.2 i).2 hi).1

/-- Outgoing-root CL0 provenance. -/
theorem bankTrialDurationOrphanRootCLZeroField {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun nextBegun : Bool)
    (hinv : BankTrialDurationOrphanInv q
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) root).phase =
        .live nextBegun)
    (j : Fin (compileAdvice q).b)
    (hnew : bankTrialLiveWaveToken
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) root).bank j = .CL0) :
    ∃ k : Fin (compileAdvice q).b,
      bankTrialLiveWaveBit
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) root).bank k ≠
        (compileAdvice q).theta k.val := by
  have hf := bankTrialWindowLiveOldNotLatched
    ring root root B begun nextBegun hnext
  have hbank := bankTrialLocalNextLiveBank ring root root B begun
  have hcmp := bankTrialCmpRoot ring root hw B hf
  rw [hbank] at hnew ⊢
  have hnever : bankTrialLiveWaveToken
      (GrantBankReference.bankLocalReferenceStepClamped ring root B root)
      ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ ≠ .CL0 := by
    have hp := ((hcmp.2
      (⟨0, by have hb := bankTrialCmpWidth q; omega⟩ :
        Fin (compileAdvice q).b)).1 rfl).2
    rw [hp]
    exact bankTrialDurationOrphanRawRootNeverProducesCLZero
      (compileAdvice q).b (compileAdvice q).theta
      (GrantBankReference.bankLocalReferenceCell B
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩)
      (GrantBankReference.bankLocalReferenceCell B
        ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
      (by have hb := bankTrialCmpWidth q; omega) rfl rfl rfl
  have hjzero : j.val ≠ 0 := by
    intro hz
    have hj : j =
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ := Fin.ext hz
    rw [hj] at hnew
    exact hnever hnew
  have hold : bankTrialLiveWaveToken B j = .CL0 := by
    rw [((hcmp.2 j).2 hjzero).2] at hnew
    exact hnew
  have hc := hinv.locked.1 begun rfl
  have hm := bankTrialDurationOrphanCLZeroRequiresCWait B hc
    (hinv.locked.2 begun rfl) (hinv.noLiveResetWait begun rfl) j hold
  obtain ⟨k, hbad⟩ := hinv.zeroBackMismatch begun rfl j hold
  refine ⟨k, ?_⟩
  rw [bankTrialDurationOrphanCWaitRootBitFrame ring root hw B hf hm k]
  exact hbad

/-- Literal roots of a new digit-zero CR0. -/
private theorem bankTrialDurationOrphanRawRootCRZeroOrigins
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 < b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false)
    (hnr : x.mode ≠ .RESET) (hnw : x.mode ≠ .RWAIT)
    (hhead : (x.mode = .ARMED ∨ x.mode = .CSTART) → y.tok = .E)
    (hiwait : x.mode = .IWAIT →
      y.tok = .E ∨ y.tok = .IR ∨ y.tok = .AL)
    (hcwait : x.mode = .CWAIT →
      y.tok = .E ∨ y.tok = .CR0 ∨ y.tok = .CR1 ∨
        y.tok = .CL0 ∨ y.tok = .CL1)
    (hnew : (bankPair x y 1 b theta).2.tok = .CR0) :
    (x.mode = .CSTART ∧ y.tok = .E ∧ y.bit ≠ theta 0) ∨
    (x.mode = .CWAIT ∧ y.tok = .CR0) := by
  have hbpos : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  cases hm : x.mode with
  | RESET => exact False.elim (hnr hm)
  | RWAIT => exact False.elim (hnw hm)
  | ARMED =>
      have ht := hhead (Or.inl hm)
      cases hbit : y.bit <;>
        simp [bankPair, hx, hy, hg, hm, ht, hbit,
          hbpos, hbne, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] at hnew
  | CSTART =>
      have ht := hhead (Or.inr hm)
      cases hbit : y.bit <;> cases htheta : theta 0 <;>
        simp [bankPair, hx, hy, hg, hm, ht, hbit, htheta,
          hbpos, hbne, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] at hnew ⊢
  | IWAIT =>
      rcases hiwait hm with ht | ht | ht <;>
        by_cases hl : 1 < x.lease <;>
        simp [bankPair, hx, hy, hg, hm, ht, hl,
          hbpos, hbne, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] at hnew
  | CWAIT =>
      rcases hcwait hm with ht | ht | ht | ht | ht <;>
        by_cases hl : 1 < x.lease <;>
        simp [bankPair, hx, hy, hg, hm, ht, hl,
          hbpos, hbne, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] at hnew ⊢

/-- Outgoing-root CR0 provenance. -/
theorem bankTrialDurationOrphanRootCRZeroField {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun nextBegun : Bool)
    (hinv : BankTrialDurationOrphanInv q
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) root).phase =
        .live nextBegun)
    (j : Fin (compileAdvice q).b)
    (hnew : bankTrialLiveWaveToken
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) root).bank j = .CR0) :
    ∃ k : Fin (compileAdvice q).b,
      k.val ≤ j.val ∧
      bankTrialLiveWaveBit
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) root).bank k ≠
        (compileAdvice q).theta k.val := by
  have hf := bankTrialWindowLiveOldNotLatched
    ring root root B begun nextBegun hnext
  have hbank := bankTrialLocalNextLiveBank ring root root B begun
  have hcmp := bankTrialCmpRoot ring root hw B hf
  have hc := hinv.locked.1 begun rfl
  rw [hbank] at hnew ⊢
  by_cases hjzero : j.val = 0
  · have hj : j =
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ := Fin.ext hjzero
    have hfirst := ((hcmp.2
      (⟨0, by have hb := bankTrialCmpWidth q; omega⟩ :
        Fin (compileAdvice q).b)).1 rfl)
    have hrawNew :
        (GrantBankReference.bankLocalReferenceInternalPair q B
          ⟨0, by have hb := bankTrialCmpWidth q; omega⟩).2.tok = .CR0 := by
      rw [hj] at hnew
      rw [hfirst.2] at hnew
      exact hnew
    have hhead :
        ((GrantBankReference.bankLocalReferenceCell B
          ⟨0, by have hb := bankTrialCmpWidth q; omega⟩).mode = .ARMED ∨
         (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by have hb := bankTrialCmpWidth q; omega⟩).mode = .CSTART) →
        (GrantBankReference.bankLocalReferenceCell B
          ⟨1, by have hb := bankTrialCmpWidth q; omega⟩).tok = .E := by
      intro hm
      exact hc.headClear
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ hm
    have hiwait :
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by have hb := bankTrialCmpWidth q; omega⟩).mode = .IWAIT →
        (GrantBankReference.bankLocalReferenceCell B
          ⟨1, by have hb := bankTrialCmpWidth q; omega⟩).tok = .E ∨
        (GrantBankReference.bankLocalReferenceCell B
          ⟨1, by have hb := bankTrialCmpWidth q; omega⟩).tok = .IR ∨
        (GrantBankReference.bankLocalReferenceCell B
          ⟨1, by have hb := bankTrialCmpWidth q; omega⟩).tok = .AL := by
      intro hm
      exact hc.iwaitTokens
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ hm
    have hcwait :
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by have hb := bankTrialCmpWidth q; omega⟩).mode = .CWAIT →
        (GrantBankReference.bankLocalReferenceCell B
          ⟨1, by have hb := bankTrialCmpWidth q; omega⟩).tok = .E ∨
        (GrantBankReference.bankLocalReferenceCell B
          ⟨1, by have hb := bankTrialCmpWidth q; omega⟩).tok = .CR0 ∨
        (GrantBankReference.bankLocalReferenceCell B
          ⟨1, by have hb := bankTrialCmpWidth q; omega⟩).tok = .CR1 ∨
        (GrantBankReference.bankLocalReferenceCell B
          ⟨1, by have hb := bankTrialCmpWidth q; omega⟩).tok = .CL0 ∨
        (GrantBankReference.bankLocalReferenceCell B
          ⟨1, by have hb := bankTrialCmpWidth q; omega⟩).tok = .CL1 := by
      intro hm
      rcases hc.cwaitTokens
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ hm with he | ht
      · exact Or.inl he
      · exact Or.inr ht
    have horigin := bankTrialDurationOrphanRawRootCRZeroOrigins
      (compileAdvice q).b (compileAdvice q).theta
      (GrantBankReference.bankLocalReferenceCell B
        ⟨0, by have hb := bankTrialCmpWidth q; omega⟩)
      (GrantBankReference.bankLocalReferenceCell B
        ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
      (by have hb := bankTrialCmpWidth q; omega)
      rfl rfl rfl
      (hinv.locked.2 begun rfl)
      (hinv.noLiveResetWait begun rfl)
      hhead hiwait hcwait hrawNew
    rcases horigin with hlaunch | hold
    · have hlaunchRaw := bankTrialCmpRawLaunch
        (compileAdvice q).b (compileAdvice q).theta
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by have hb := bankTrialCmpWidth q; omega⟩)
        (GrantBankReference.bankLocalReferenceCell B
          ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
        (by have hb := bankTrialCmpWidth q; omega)
        rfl rfl rfl hlaunch.1 hlaunch.2.1
      have hfirstBit :
          bankTrialLiveWaveBit
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B root)
            ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ =
          bankTrialLiveWaveBit B
            ⟨0, by have hb := bankTrialCmpWidth q; omega⟩ :=
        hfirst.1.trans hlaunchRaw.2.2
      refine ⟨⟨0, by have hb := bankTrialCmpWidth q; omega⟩,
        (by change 0 ≤ j.val; omega), ?_⟩
      rw [hfirstBit]
      exact hlaunch.2.2
    · have holdToken : bankTrialLiveWaveToken B j = .CR0 := by
        rw [hj]
        exact hold.2
      obtain ⟨k, hk, hbad⟩ :=
        hinv.zeroOutMismatch begun rfl j holdToken
      have hbits := bankTrialDurationOrphanCWaitRootBitFrame
        ring root hw B hf hold.1
      refine ⟨k, hk, ?_⟩
      rw [hbits k]
      exact hbad
  · have hframe := (hcmp.2 j).2 hjzero
    have hold : bankTrialLiveWaveToken B j = .CR0 := by
      rw [hframe.2] at hnew
      exact hnew
    obtain ⟨k, hk, hbad⟩ :=
      hinv.zeroOutMismatch begun rfl j hold
    have hm := bankTrialDurationOrphanCRZeroRequiresCWait B hc
      (hinv.locked.2 begun rfl) (hinv.noLiveResetWait begun rfl) j hold
    refine ⟨k, hk, ?_⟩
    rw [bankTrialDurationOrphanCWaitRootBitFrame ring root hw B hf hm k]
    exact hbad

/-- A locked selected interior pair has at most one old worker. -/
private theorem bankTrialDurationOrphanInteriorOldPairSolo {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val) :
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by have hb := j.isLt; omega⟩).tok = .E ∨
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by have hb := j.isLt; omega⟩).tok = .E := by
  have hleft : j.val - 1 < (compileAdvice q).b := by
    have hb := j.isLt
    omega
  have hidx :
      (⟨j.val - 1 + 1, by have hb := j.isLt; omega⟩ :
        Fin ((compileAdvice q).b + 1)) =
      ⟨j.val, by have hb := j.isLt; omega⟩ :=
    Fin.ext (show j.val - 1 + 1 = j.val by omega)
  by_cases hx : bankTrialLiveWaveToken B
      ⟨j.val - 1, hleft⟩ = .E
  · left
    change (B.fields ⟨j.val - 1 + 1, by omega⟩).2.2.1 = .E at hx
    rw [hidx] at hx
    exact hx
  · by_cases hy : bankTrialLiveWaveToken B j = .E
    · exact Or.inr hy
    · have h := hc.uniqueWorker ⟨j.val - 1, hleft⟩ j hx hy
      have hv := congrArg Fin.val h
      change j.val - 1 = j.val at hv
      omega

/-- A one-worker interior pair cannot erase its only worker except
for top IR, which is excluded separately by carryBound. -/
private theorem bankTrialDurationOrphanRawInteriorWorkerSurvives
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hsolo : x.tok = .E ∨ y.tok = .E)
    (hpresent : x.tok ≠ .E ∨ y.tok ≠ .E)
    (hnoTopIR : y.role = b → y.tok ≠ .IR) :
    (bankPair x y y.role b theta).1.tok ≠ .E ∨
    (bankPair x y y.role b theta).2.tok ≠ .E := by
  have hxn : x.role ≠ 0 := by omega
  have hxTop : x.role ≠ b := by omega
  have hyn : y.role ≠ 0 := by omega
  have hyPos : 1 ≤ y.role := by omega
  have hyLe : y.role ≤ b := by omega
  have hxLe : x.role ≤ b := by omega
  rcases hsolo with hxempty | hyempty
  · by_cases htop : y.role = b
    · have hnir := hnoTopIR htop
      cases ht : y.tok <;>
        simp [bankPair, hx, hlt, hy, hxn, hxTop,
          hyn, hyPos, hyLe, hxLe, hxempty, ht, htop,
          Id.run_pure, Id.run_bind] at hpresent hnir ⊢ <;>
        (repeat' split) <;> (try simp) <;> omega
    · cases ht : y.tok <;>
        simp [bankPair, hx, hlt, hy, hxn, hxTop,
          hyn, hyPos, hyLe, hxLe, hxempty, ht, htop,
          Id.run_pure, Id.run_bind] at hpresent ⊢ <;>
        (repeat' split) <;> (try simp) <;> omega
  · cases ht : x.tok <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, hyempty, ht,
        Id.run_pure, Id.run_bind] at hpresent ⊢ <;>
      (repeat' split) <;> simp

/-- Proper-interior preservation of the explicit non-orphan field. -/
theorem bankTrialDurationOrphanInteriorWorkerField {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun nextBegun : Bool)
    (hinv : BankTrialDurationOrphanInv q
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q)
      (Counter.site ring root j.val)).phase = .live nextBegun)
    (hmode : bankTrialLiveWaveRootMode
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)).bank = .IWAIT ∨
      bankTrialLiveWaveRootMode
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)).bank = .CWAIT) :
    ∃ k : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q)
          (Counter.site ring root j.val)).bank k ≠ .E := by
  have hmodeFrame := bankTrialDurationOrphanInteriorRootModeFrame
    ring root hw j hj B begun nextBegun hnext
  have holdMode : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT := by
    rcases hmode with hm | hm
    · exact Or.inl (hmodeFrame.symm.trans hm)
    · exact Or.inr (hmodeFrame.symm.trans hm)
  obtain ⟨w, hwtoken⟩ := hinv.workerPresent begun rfl holdMode
  have hf := bankTrialWindowLiveOldNotLatched ring root
    (Counter.site ring root j.val) B begun nextBegun hnext
  have hbank := bankTrialLocalNextLiveBank ring root
    (Counter.site ring root j.val) B begun
  have hcmp := bankTrialCmpInterior ring root hw B hf
    j.val hj j.isLt
  have hc := hinv.locked.1 begun rfl
  have hsolo := bankTrialDurationOrphanInteriorOldPairSolo B hc j hj
  by_cases hs : w.val + 1 = j.val
  · have hleft : j.val - 1 < (compileAdvice q).b := by
      have hb := j.isLt
      omega
    have hwEq : w = ⟨j.val - 1, hleft⟩ := by
      apply Fin.ext
      change w.val = j.val - 1
      omega
    have hxne :
        (GrantBankReference.bankLocalReferenceCell B
          ⟨j.val, by have hb := j.isLt; omega⟩).tok ≠ .E := by
      have hidx : (⟨j.val, by have hb := j.isLt; omega⟩ :
          Fin ((compileAdvice q).b + 1)) =
          ⟨w.val + 1, by have hb := w.isLt; omega⟩ :=
        Fin.ext hs.symm
      rw [hidx]
      exact hwtoken
    have hpresent :
        (GrantBankReference.bankLocalReferenceCell B
          ⟨j.val, by have hb := j.isLt; omega⟩).tok ≠ .E ∨
        (GrantBankReference.bankLocalReferenceCell B
          ⟨j.val + 1, by have hb := j.isLt; omega⟩).tok ≠ .E :=
      Or.inl hxne
    have hnoTopIR :
        (GrantBankReference.bankLocalReferenceCell B
          ⟨j.val + 1, by have hb := j.isLt; omega⟩).role =
            (compileAdvice q).b →
        (GrantBankReference.bankLocalReferenceCell B
          ⟨j.val + 1, by have hb := j.isLt; omega⟩).tok ≠ .IR := by
      intro htop hIR
      have hjtop : j = bankTrialDurationTopDigit q := by
        apply Fin.ext
        unfold bankTrialDurationTopDigit
        change j.val = (compileAdvice q).b - 1
        change j.val + 1 = (compileAdvice q).b at htop
        omega
      have ht : bankTrialLiveWaveToken B j = .IR := hIR
      rw [hjtop] at ht
      exact bankTrialDurationOrphanInvNoTopIR
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        hinv hK begun rfl ht
    have hraw := bankTrialDurationOrphanRawInteriorWorkerSurvives
      (compileAdvice q).b (compileAdvice q).theta
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hb := j.isLt; omega⟩)
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val + 1, by have hb := j.isLt; omega⟩)
      (by change 1 ≤ j.val; omega) j.isLt rfl
      hsolo hpresent hnoTopIR
    rw [hbank]
    rcases hraw with hleftNew | hrightNew
    · refine ⟨⟨j.val - 1, hleft⟩, ?_⟩
      rw [((hcmp.2.2
        (⟨j.val - 1, hleft⟩ : Fin (compileAdvice q).b)).1
          (by change j.val - 1 + 1 = j.val; omega)).2]
      exact hleftNew
    · refine ⟨j, ?_⟩
      rw [((hcmp.2.2 j).2.1 rfl).2]
      exact hrightNew
  · by_cases ht : w.val = j.val
    · have hwEq : w = j := Fin.ext ht
      have hyne :
          (GrantBankReference.bankLocalReferenceCell B
            ⟨j.val + 1, by have hb := j.isLt; omega⟩).tok ≠ .E := by
        change bankTrialLiveWaveToken B j ≠ .E
        rw [← hwEq]
        exact hwtoken
      have hpresent :
          (GrantBankReference.bankLocalReferenceCell B
            ⟨j.val, by have hb := j.isLt; omega⟩).tok ≠ .E ∨
          (GrantBankReference.bankLocalReferenceCell B
            ⟨j.val + 1, by have hb := j.isLt; omega⟩).tok ≠ .E :=
        Or.inr hyne
      have hnoTopIR :
          (GrantBankReference.bankLocalReferenceCell B
            ⟨j.val + 1, by have hb := j.isLt; omega⟩).role =
              (compileAdvice q).b →
          (GrantBankReference.bankLocalReferenceCell B
            ⟨j.val + 1, by have hb := j.isLt; omega⟩).tok ≠ .IR := by
        intro htop hIR
        have hjtop : j = bankTrialDurationTopDigit q := by
          apply Fin.ext
          unfold bankTrialDurationTopDigit
          change j.val = (compileAdvice q).b - 1
          change j.val + 1 = (compileAdvice q).b at htop
          omega
        have htok : bankTrialLiveWaveToken B j = .IR := hIR
        rw [hjtop] at htok
        exact bankTrialDurationOrphanInvNoTopIR
          (⟨B, .live begun⟩ : BankTrialLocalState q)
          hinv hK begun rfl htok
      have hraw := bankTrialDurationOrphanRawInteriorWorkerSurvives
        (compileAdvice q).b (compileAdvice q).theta
        (GrantBankReference.bankLocalReferenceCell B
          ⟨j.val, by have hb := j.isLt; omega⟩)
        (GrantBankReference.bankLocalReferenceCell B
          ⟨j.val + 1, by have hb := j.isLt; omega⟩)
        (by change 1 ≤ j.val; omega) j.isLt rfl
        hsolo hpresent hnoTopIR
      rw [hbank]
      rcases hraw with hleftNew | hrightNew
      · refine ⟨⟨j.val - 1, by have hb := j.isLt; omega⟩, ?_⟩
        rw [((hcmp.2.2
          (⟨j.val - 1, by have hb := j.isLt; omega⟩ :
            Fin (compileAdvice q).b)).1
            (by change j.val - 1 + 1 = j.val; omega)).2]
        exact hleftNew
      · refine ⟨j, ?_⟩
        rw [((hcmp.2.2 j).2.1 rfl).2]
        exact hrightNew
    · refine ⟨w, ?_⟩
      rw [hbank]
      exact fun h => hwtoken ((((hcmp.2.2 w).2.2 hs ht).2).symm.trans h)

/-- CWAIT permits only E and comparison tokens. -/
private theorem bankTrialDurationOrphanCWaitTokenCases {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .CWAIT)
    (k : Fin (compileAdvice q).b) :
    bankTrialLiveWaveToken B k = .E ∨
    bankTrialLiveWaveToken B k = .CR0 ∨
    bankTrialLiveWaveToken B k = .CR1 ∨
    bankTrialLiveWaveToken B k = .CL0 ∨
    bankTrialLiveWaveToken B k = .CL1 := by
  rcases hc.cwaitTokens k hm with h | h
  · exact Or.inl h
  · rcases h with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- Every protected bit is framed by a selected interior CWAIT pair. -/
private theorem bankTrialDurationOrphanInteriorCWaitBitFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .CWAIT) :
    ∀ k : Fin (compileAdvice q).b,
      bankTrialLiveWaveBit
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) k =
        bankTrialLiveWaveBit B k := by
  have hleft : j.val - 1 < (compileAdvice q).b := by
    have hb := j.isLt
    omega
  have hleftIdx :
      (⟨j.val - 1 + 1, by have hb := j.isLt; omega⟩ :
        Fin ((compileAdvice q).b + 1)) =
      ⟨j.val, by have hb := j.isLt; omega⟩ :=
    Fin.ext (show j.val - 1 + 1 = j.val by omega)
  have hxs :
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hb := j.isLt; omega⟩).tok = .E ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hb := j.isLt; omega⟩).tok = .CR0 ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hb := j.isLt; omega⟩).tok = .CR1 ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hb := j.isLt; omega⟩).tok = .CL0 ∨
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hb := j.isLt; omega⟩).tok = .CL1 := by
    have h := bankTrialDurationOrphanCWaitTokenCases B hc hm
      ⟨j.val - 1, hleft⟩
    change
      (B.fields ⟨j.val - 1 + 1, by omega⟩).2.2.1 = .E ∨
      (B.fields ⟨j.val - 1 + 1, by omega⟩).2.2.1 = .CR0 ∨
      (B.fields ⟨j.val - 1 + 1, by omega⟩).2.2.1 = .CR1 ∨
      (B.fields ⟨j.val - 1 + 1, by omega⟩).2.2.1 = .CL0 ∨
      (B.fields ⟨j.val - 1 + 1, by omega⟩).2.2.1 = .CL1 at h
    rw [hleftIdx] at h
    exact h
  have hys := bankTrialDurationOrphanCWaitTokenCases B hc hm j
  have hsolo := bankTrialDurationOrphanInteriorOldPairSolo B hc j hj
  have hraw := bankTrialInteriorRawComparisonBits
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by have hb := j.isLt; omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by have hb := j.isLt; omega⟩)
    (by change 1 ≤ j.val; omega) j.isLt rfl hxs hys hsolo
  have hcmp := bankTrialCmpInterior ring root hw B hf
    j.val hj j.isLt
  intro k
  by_cases hs : k.val + 1 = j.val
  · calc
      bankTrialLiveWaveBit
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j.val)) k =
        (GrantBankReference.bankLocalReferenceInternalPair q B j).1.bit :=
        ((hcmp.2.2 k).1 hs).1
      _ = (B.fields
          ⟨j.val, by have hb := j.isLt; omega⟩).2.1 := hraw.1
      _ = bankTrialLiveWaveBit B k := by
        have hindex :
            (⟨j.val, by have hb := j.isLt; omega⟩ :
              Fin ((compileAdvice q).b + 1)) =
            ⟨k.val + 1, by have hb := k.isLt; omega⟩ :=
          Fin.ext (show j.val = k.val + 1 by omega)
        change (B.fields
          ⟨j.val, by have hb := j.isLt; omega⟩).2.1 =
          (B.fields
            ⟨k.val + 1, by have hb := k.isLt; omega⟩).2.1
        rw [hindex]
  · by_cases ht : k.val = j.val
    · calc
        bankTrialLiveWaveBit
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B (Counter.site ring root j.val)) k =
          (GrantBankReference.bankLocalReferenceInternalPair q B j).2.bit :=
          ((hcmp.2.2 k).2.1 ht).1
        _ = (B.fields
            ⟨j.val + 1, by have hb := j.isLt; omega⟩).2.1 := hraw.2
        _ = bankTrialLiveWaveBit B k := by
          have hindex :
              (⟨j.val + 1, by have hb := j.isLt; omega⟩ :
                Fin ((compileAdvice q).b + 1)) =
              ⟨k.val + 1, by have hb := k.isLt; omega⟩ :=
            Fin.ext (show j.val + 1 = k.val + 1 by omega)
          change (B.fields
            ⟨j.val + 1, by have hb := j.isLt; omega⟩).2.1 =
            (B.fields
              ⟨k.val + 1, by have hb := k.isLt; omega⟩).2.1
          rw [hindex]
    · exact ((hcmp.2.2 k).2.2 hs ht).1

/-- No selected interior pair with one old worker creates CR0 on the left. -/
private theorem bankTrialDurationOrphanRawInteriorLeftNoCRZero
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hsolo : x.tok = .E ∨ y.tok = .E) :
    (bankPair x y y.role b theta).1.tok ≠ .CR0 := by
  have hxn : x.role ≠ 0 := by omega
  have hxTop : x.role ≠ b := by omega
  have hyn : y.role ≠ 0 := by omega
  have hyPos : 1 ≤ y.role := by omega
  have hyLe : y.role ≤ b := by omega
  have hxLe : x.role ≤ b := by omega
  rcases hsolo with he | he
  · cases ht : y.tok <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] <;>
      (repeat' split) <;> simp
  · cases ht : x.tok <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] <;>
      (repeat' split) <;> simp

/-- No selected interior pair with one old worker creates CL0 on the right. -/
private theorem bankTrialDurationOrphanRawInteriorRightNoCLZero
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hsolo : x.tok = .E ∨ y.tok = .E) :
    (bankPair x y y.role b theta).2.tok ≠ .CL0 := by
  have hxn : x.role ≠ 0 := by omega
  have hxTop : x.role ≠ b := by omega
  have hyn : y.role ≠ 0 := by omega
  have hyPos : 1 ≤ y.role := by omega
  have hyLe : y.role ≤ b := by omega
  have hxLe : x.role ≤ b := by omega
  rcases hsolo with he | he
  · cases ht : y.tok <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] <;>
      (repeat' split) <;> simp
  · cases ht : x.tok <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] <;>
      (repeat' split) <;> simp

/-- Raw ancestors of an interior right CR0. -/
private theorem bankTrialDurationOrphanRawInteriorRightCRZeroAncestors
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hsolo : x.tok = .E ∨ y.tok = .E)
    (hnew : (bankPair x y y.role b theta).2.tok = .CR0) :
    x.tok = .CR0 ∨ y.tok = .CR0 ∨ x.tok = .CR1 := by
  have hxn : x.role ≠ 0 := by omega
  have hxTop : x.role ≠ b := by omega
  have hyn : y.role ≠ 0 := by omega
  have hyPos : 1 ≤ y.role := by omega
  have hyLe : y.role ≤ b := by omega
  have hxLe : x.role ≤ b := by omega
  rcases hsolo with he | he
  · cases ht : y.tok <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] at hnew ⊢ <;>
      (repeat' split at hnew) <;> simp [*] at hnew ⊢
  · cases ht : x.tok <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] at hnew ⊢ <;>
      (repeat' split at hnew) <;> simp [*] at hnew ⊢

/-- Raw ancestors of an interior left CL0. -/
private theorem bankTrialDurationOrphanRawInteriorLeftCLZeroAncestors
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hsolo : x.tok = .E ∨ y.tok = .E)
    (hnew : (bankPair x y y.role b theta).1.tok = .CL0) :
    x.tok = .CL0 ∨ y.tok = .CL0 ∨
      (y.tok = .CR0 ∧ y.role = b) := by
  have hxn : x.role ≠ 0 := by omega
  have hxTop : x.role ≠ b := by omega
  have hyn : y.role ≠ 0 := by omega
  have hyPos : 1 ≤ y.role := by omega
  have hyLe : y.role ≤ b := by omega
  have hxLe : x.role ≤ b := by omega
  rcases hsolo with he | he
  · cases ht : y.tok <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] at hnew ⊢ <;>
      (repeat' split at hnew) <;> simp [*] at hnew ⊢
  · cases ht : x.tok <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] at hnew ⊢ <;>
      (repeat' split at hnew) <;> simp [*] at hnew ⊢

/-- Proper-interior CR0 provenance. -/
theorem bankTrialDurationOrphanInteriorCRZeroField {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun nextBegun : Bool)
    (hinv : BankTrialDurationOrphanInv q
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q)
      (Counter.site ring root j.val)).phase = .live nextBegun)
    (k : Fin (compileAdvice q).b)
    (hnew : bankTrialLiveWaveToken
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)).bank k = .CR0) :
    ∃ i : Fin (compileAdvice q).b,
      i.val ≤ k.val ∧
      bankTrialLiveWaveBit
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q)
          (Counter.site ring root j.val)).bank i ≠
        (compileAdvice q).theta i.val := by
  have hf := bankTrialWindowLiveOldNotLatched ring root
    (Counter.site ring root j.val) B begun nextBegun hnext
  have hbank := bankTrialLocalNextLiveBank ring root
    (Counter.site ring root j.val) B begun
  have hc := hinv.locked.1 begun rfl
  have hcmp := bankTrialCmpInterior ring root hw B hf j.val hj j.isLt
  have hsolo := bankTrialDurationOrphanInteriorOldPairSolo B hc j hj
  have htransport :
      bankTrialLiveWaveRootMode B = .CWAIT →
      ∀ i : Fin (compileAdvice q).b,
        bankTrialLiveWaveBit
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j.val)) i =
        bankTrialLiveWaveBit B i := by
    intro hm
    exact bankTrialDurationOrphanInteriorCWaitBitFrame
      ring root hw B hf j hj hc hm
  rw [hbank] at hnew ⊢
  by_cases hs : k.val + 1 = j.val
  · have hraw :
        (GrantBankReference.bankLocalReferenceInternalPair q B j).1.tok =
          .CR0 := by
      rw [((hcmp.2.2 k).1 hs).2] at hnew
      exact hnew
    exact False.elim (bankTrialDurationOrphanRawInteriorLeftNoCRZero
      (compileAdvice q).b (compileAdvice q).theta
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hb := j.isLt; omega⟩)
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val + 1, by have hb := j.isLt; omega⟩)
      (by change 1 ≤ j.val; omega) j.isLt rfl hsolo hraw)
  · by_cases ht : k.val = j.val
    · have hraw :
          (GrantBankReference.bankLocalReferenceInternalPair q B j).2.tok =
            .CR0 := by
        rw [((hcmp.2.2 k).2.1 ht).2] at hnew
        exact hnew
      have horigin := bankTrialDurationOrphanRawInteriorRightCRZeroAncestors
        (compileAdvice q).b (compileAdvice q).theta
        (GrantBankReference.bankLocalReferenceCell B
          ⟨j.val, by have hb := j.isLt; omega⟩)
        (GrantBankReference.bankLocalReferenceCell B
          ⟨j.val + 1, by have hb := j.isLt; omega⟩)
        (by change 1 ≤ j.val; omega) j.isLt rfl hsolo hraw
      rcases horigin with hleft | hright | hleftGood
      · have hsourceIdx :
            (⟨j.val - 1 + 1, by have hb := j.isLt; omega⟩ :
              Fin ((compileAdvice q).b + 1)) =
            ⟨j.val, by have hb := j.isLt; omega⟩ :=
          Fin.ext (show j.val - 1 + 1 = j.val by omega)
        have hsource : bankTrialLiveWaveToken B
            ⟨j.val - 1, by have hb := j.isLt; omega⟩ = .CR0 := by
          change (B.fields
            ⟨j.val - 1 + 1, by have hb := j.isLt; omega⟩).2.2.1 = .CR0
          rw [hsourceIdx]
          exact hleft
        have hm := bankTrialDurationOrphanCRZeroRequiresCWait B hc
          (hinv.locked.2 begun rfl)
          (hinv.noLiveResetWait begun rfl)
          ⟨j.val - 1, by have hb := j.isLt; omega⟩ hsource
        obtain ⟨i, hi, hbad⟩ :=
          hinv.zeroOutMismatch begun rfl
            ⟨j.val - 1, by have hb := j.isLt; omega⟩ hsource
        change i.val ≤ j.val - 1 at hi
        refine ⟨i, (by omega), ?_⟩
        rw [htransport hm i]
        exact hbad
      · have hsource : bankTrialLiveWaveToken B j = .CR0 := hright
        have hm := bankTrialDurationOrphanCRZeroRequiresCWait B hc
          (hinv.locked.2 begun rfl)
          (hinv.noLiveResetWait begun rfl) j hsource
        obtain ⟨i, hi, hbad⟩ :=
          hinv.zeroOutMismatch begun rfl j hsource
        refine ⟨i, (by omega), ?_⟩
        rw [htransport hm i]
        exact hbad
      · have hsourceIdx :
            (⟨j.val - 1 + 1, by have hb := j.isLt; omega⟩ :
              Fin ((compileAdvice q).b + 1)) =
            ⟨j.val, by have hb := j.isLt; omega⟩ :=
          Fin.ext (show j.val - 1 + 1 = j.val by omega)
        have hsource : bankTrialLiveWaveToken B
            ⟨j.val - 1, by have hb := j.isLt; omega⟩ = .CR1 := by
          change (B.fields
            ⟨j.val - 1 + 1, by have hb := j.isLt; omega⟩).2.2.1 = .CR1
          rw [hsourceIdx]
          exact hleftGood
        have hm := hc.comparisonMode
          ⟨j.val - 1, by have hb := j.isLt; omega⟩ (Or.inl hsource)
        have hrightE :
            (GrantBankReference.bankLocalReferenceCell B
              ⟨j.val + 1, by have hb := j.isLt; omega⟩).tok = .E := by
          rcases hsolo with hxE | hyE
          · rw [hxE] at hleftGood
            cases hleftGood
          · exact hyE
        have hforward := bankTrialCmpRawCRForward
          (compileAdvice q).b (compileAdvice q).theta
          (GrantBankReference.bankLocalReferenceCell B
            ⟨j.val, by have hb := j.isLt; omega⟩)
          (GrantBankReference.bankLocalReferenceCell B
            ⟨j.val + 1, by have hb := j.isLt; omega⟩)
          (by change 1 ≤ j.val; omega) j.isLt rfl true
          (by simpa using hleftGood) hrightE
        have hbad :
            (GrantBankReference.bankLocalReferenceCell B
              ⟨j.val + 1, by have hb := j.isLt; omega⟩).bit ≠
            (compileAdvice q).theta
              ((GrantBankReference.bankLocalReferenceCell B
                ⟨j.val + 1, by have hb := j.isLt; omega⟩).role - 1) := by
          intro heq
          have hbool :
              (true && ((GrantBankReference.bankLocalReferenceCell B
                ⟨j.val + 1, by have hb := j.isLt; omega⟩).bit ==
                (compileAdvice q).theta
                  ((GrantBankReference.bankLocalReferenceCell B
                    ⟨j.val + 1, by have hb := j.isLt; omega⟩).role - 1))) =
                true := by simp [heq]
          have htest := hforward.2.2.1
          rw [hbool] at htest
          have hcontr : (BTok.CR1 : BTok) = .CR0 :=
            htest.symm.trans hraw
          cases hcontr
        refine ⟨j, (by omega), ?_⟩
        rw [htransport hm j]
        have hnum : j.val + 1 - 1 = j.val := by omega
        change (B.fields
          ⟨j.val + 1, by have hb := j.isLt; omega⟩).2.1 ≠
          (compileAdvice q).theta (j.val + 1 - 1) at hbad
        rw [hnum] at hbad
        exact hbad
    · have hframe := ((hcmp.2.2 k).2.2 hs ht)
      have hold : bankTrialLiveWaveToken B k = .CR0 := by
        rw [hframe.2] at hnew
        exact hnew
      have hm := bankTrialDurationOrphanCRZeroRequiresCWait B hc
        (hinv.locked.2 begun rfl)
        (hinv.noLiveResetWait begun rfl) k hold
      obtain ⟨i, hi, hbad⟩ :=
        hinv.zeroOutMismatch begun rfl k hold
      refine ⟨i, hi, ?_⟩
      rw [htransport hm i]
      exact hbad

/-- Proper-interior CL0 provenance. -/
theorem bankTrialDurationOrphanInteriorCLZeroField {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun nextBegun : Bool)
    (hinv : BankTrialDurationOrphanInv q
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q)
      (Counter.site ring root j.val)).phase = .live nextBegun)
    (k : Fin (compileAdvice q).b)
    (hnew : bankTrialLiveWaveToken
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)).bank k = .CL0) :
    ∃ i : Fin (compileAdvice q).b,
      bankTrialLiveWaveBit
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q)
          (Counter.site ring root j.val)).bank i ≠
        (compileAdvice q).theta i.val := by
  have hf := bankTrialWindowLiveOldNotLatched ring root
    (Counter.site ring root j.val) B begun nextBegun hnext
  have hbank := bankTrialLocalNextLiveBank ring root
    (Counter.site ring root j.val) B begun
  have hc := hinv.locked.1 begun rfl
  have hcmp := bankTrialCmpInterior ring root hw B hf j.val hj j.isLt
  have hsolo := bankTrialDurationOrphanInteriorOldPairSolo B hc j hj
  have htransport :
      bankTrialLiveWaveRootMode B = .CWAIT →
      (∃ i : Fin (compileAdvice q).b,
        bankTrialLiveWaveBit B i ≠ (compileAdvice q).theta i.val) →
      ∃ i : Fin (compileAdvice q).b,
        bankTrialLiveWaveBit
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j.val)) i ≠
          (compileAdvice q).theta i.val := by
    intro hm hold
    obtain ⟨i, hbad⟩ := hold
    refine ⟨i, ?_⟩
    rw [bankTrialDurationOrphanInteriorCWaitBitFrame
      ring root hw B hf j hj hc hm i]
    exact hbad
  rw [hbank] at hnew ⊢
  by_cases hs : k.val + 1 = j.val
  · have hraw :
        (GrantBankReference.bankLocalReferenceInternalPair q B j).1.tok =
          .CL0 := by
      rw [((hcmp.2.2 k).1 hs).2] at hnew
      exact hnew
    have horigin := bankTrialDurationOrphanRawInteriorLeftCLZeroAncestors
      (compileAdvice q).b (compileAdvice q).theta
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by have hb := j.isLt; omega⟩)
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val + 1, by have hb := j.isLt; omega⟩)
      (by change 1 ≤ j.val; omega) j.isLt rfl hsolo hraw
    rcases horigin with hleft | hright | ⟨htopCR, htop⟩
    · have hsourceIdx :
          (⟨k.val + 1, by have hb := k.isLt; omega⟩ :
            Fin ((compileAdvice q).b + 1)) =
          ⟨j.val, by have hb := j.isLt; omega⟩ := Fin.ext hs
      have hold : bankTrialLiveWaveToken B k = .CL0 := by
        change (B.fields
          ⟨k.val + 1, by have hb := k.isLt; omega⟩).2.2.1 = .CL0
        rw [hsourceIdx]
        exact hleft
      have hm := bankTrialDurationOrphanCLZeroRequiresCWait B hc
        (hinv.locked.2 begun rfl)
        (hinv.noLiveResetWait begun rfl) k hold
      exact htransport hm (hinv.zeroBackMismatch begun rfl k hold)
    · have hold : bankTrialLiveWaveToken B j = .CL0 := hright
      have hm := bankTrialDurationOrphanCLZeroRequiresCWait B hc
        (hinv.locked.2 begun rfl)
        (hinv.noLiveResetWait begun rfl) j hold
      exact htransport hm (hinv.zeroBackMismatch begun rfl j hold)
    · have hold : bankTrialLiveWaveToken B j = .CR0 := htopCR
      have hm := bankTrialDurationOrphanCRZeroRequiresCWait B hc
        (hinv.locked.2 begun rfl)
        (hinv.noLiveResetWait begun rfl) j hold
      obtain ⟨i, hi, hbad⟩ :=
        hinv.zeroOutMismatch begun rfl j hold
      exact htransport hm ⟨i, hbad⟩
  · by_cases ht : k.val = j.val
    · have hraw :
          (GrantBankReference.bankLocalReferenceInternalPair q B j).2.tok =
            .CL0 := by
        rw [((hcmp.2.2 k).2.1 ht).2] at hnew
        exact hnew
      exact False.elim (bankTrialDurationOrphanRawInteriorRightNoCLZero
        (compileAdvice q).b (compileAdvice q).theta
        (GrantBankReference.bankLocalReferenceCell B
          ⟨j.val, by have hb := j.isLt; omega⟩)
        (GrantBankReference.bankLocalReferenceCell B
          ⟨j.val + 1, by have hb := j.isLt; omega⟩)
        (by change 1 ≤ j.val; omega) j.isLt rfl hsolo hraw)
    · have hframe := ((hcmp.2.2 k).2.2 hs ht)
      have hold : bankTrialLiveWaveToken B k = .CL0 := by
        rw [hframe.2] at hnew
        exact hnew
      have hm := bankTrialDurationOrphanCLZeroRequiresCWait B hc
        (hinv.locked.2 begun rfl)
        (hinv.noLiveResetWait begun rfl) k hold
      exact htransport hm (hinv.zeroBackMismatch begun rfl k hold)

/-- Complete outgoing-root preservation. -/
theorem bankTrialDurationOrphanRootRow {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    BankTrialDurationOrphanInvEdge (q := q) ring root root := by
  intro z hinv
  refine {
    locked := bankTrialDurationOrphanLockedNext ring root root hw z hinv,
    noLiveResetWait := ?_,
    carryBound := ?_,
    armedBeforeThreshold := ?_,
    workerPresent := ?_,
    zeroOutMismatch := ?_,
    zeroBackMismatch := ?_
  }
  · intro nextBegun hnext
    obtain ⟨begun, hprev⟩ :=
      bankTrialDurationNextLiveOrigin ring root root z nextBegun hnext
    have hz := bankTrialCmpStateEta z begun hprev
    have hcanon : BankTrialDurationOrphanInv q
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
      have h := hinv
      rw [hz] at h
      exact h
    have hnextCanon := hnext
    rw [hz] at hnextCanon
    rw [hz]
    exact bankTrialDurationOrphanRootNoWaitField
      ring root hw z.bank begun nextBegun hcanon hnextCanon
  · intro nextBegun hnext
    obtain ⟨begun, hprev⟩ :=
      bankTrialDurationNextLiveOrigin ring root root z nextBegun hnext
    have hz := bankTrialCmpStateEta z begun hprev
    have hcanon : BankTrialDurationOrphanInv q
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
      have h := hinv
      rw [hz] at h
      exact h
    have hnextCanon := hnext
    rw [hz] at hnextCanon
    rw [hz]
    exact bankTrialDurationOrphanRootCarryField
      ring root hw z.bank begun nextBegun hcanon hnextCanon
  · intro nextBegun hnext harmed
    obtain ⟨begun, hprev⟩ :=
      bankTrialDurationNextLiveOrigin ring root root z nextBegun hnext
    have hz := bankTrialCmpStateEta z begun hprev
    have hcanon : BankTrialDurationOrphanInv q
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
      have h := hinv
      rw [hz] at h
      exact h
    have hnextCanon := hnext
    have harmedCanon := harmed
    rw [hz] at hnextCanon harmedCanon
    rw [hz]
    exact bankTrialDurationOrphanRootArmedField
      ring root hw hK z.bank begun nextBegun hcanon hnextCanon harmedCanon
  · intro nextBegun hnext hmode
    obtain ⟨begun, hprev⟩ :=
      bankTrialDurationNextLiveOrigin ring root root z nextBegun hnext
    have hz := bankTrialCmpStateEta z begun hprev
    have hcanon : BankTrialDurationOrphanInv q
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
      have h := hinv
      rw [hz] at h
      exact h
    have hnextCanon := hnext
    have hmodeCanon := hmode
    rw [hz] at hnextCanon hmodeCanon
    rw [hz]
    exact bankTrialDurationOrphanRootWorkerField
      ring root hw z.bank begun nextBegun hcanon hnextCanon hmodeCanon
  · intro nextBegun hnext j htok
    obtain ⟨begun, hprev⟩ :=
      bankTrialDurationNextLiveOrigin ring root root z nextBegun hnext
    have hz := bankTrialCmpStateEta z begun hprev
    have hcanon : BankTrialDurationOrphanInv q
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
      have h := hinv
      rw [hz] at h
      exact h
    have hnextCanon := hnext
    have htokCanon := htok
    rw [hz] at hnextCanon htokCanon
    rw [hz]
    exact bankTrialDurationOrphanRootCRZeroField
      ring root hw z.bank begun nextBegun hcanon hnextCanon j htokCanon
  · intro nextBegun hnext j htok
    obtain ⟨begun, hprev⟩ :=
      bankTrialDurationNextLiveOrigin ring root root z nextBegun hnext
    have hz := bankTrialCmpStateEta z begun hprev
    have hcanon : BankTrialDurationOrphanInv q
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
      have h := hinv
      rw [hz] at h
      exact h
    have hnextCanon := hnext
    have htokCanon := htok
    rw [hz] at hnextCanon htokCanon
    rw [hz]
    exact bankTrialDurationOrphanRootCLZeroField
      ring root hw z.bank begun nextBegun hcanon hnextCanon j htokCanon

/-- Complete proper-interior preservation. -/
theorem bankTrialDurationOrphanInteriorRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    ∀ j : Fin (compileAdvice q).b, 0 < j.val →
      BankTrialDurationOrphanInvEdge (q := q)
        ring root (Counter.site ring root j.val) := by
  intro j hj z hinv
  refine {
    locked := bankTrialDurationOrphanLockedNext
      ring root (Counter.site ring root j.val) hw z hinv,
    noLiveResetWait := ?_,
    carryBound := ?_,
    armedBeforeThreshold := ?_,
    workerPresent := ?_,
    zeroOutMismatch := ?_,
    zeroBackMismatch := ?_
  }
  · intro nextBegun hnext
    obtain ⟨begun, hprev⟩ := bankTrialDurationNextLiveOrigin
      ring root (Counter.site ring root j.val) z nextBegun hnext
    have hz := bankTrialCmpStateEta z begun hprev
    have hcanon : BankTrialDurationOrphanInv q
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
      have h := hinv
      rw [hz] at h
      exact h
    have hnextCanon := hnext
    rw [hz] at hnextCanon
    rw [hz]
    exact bankTrialDurationOrphanInteriorNoWaitField
      ring root hw j hj z.bank begun nextBegun hcanon hnextCanon
  · intro nextBegun hnext
    obtain ⟨begun, hprev⟩ := bankTrialDurationNextLiveOrigin
      ring root (Counter.site ring root j.val) z nextBegun hnext
    have hz := bankTrialCmpStateEta z begun hprev
    have hcanon : BankTrialDurationOrphanInv q
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
      have h := hinv
      rw [hz] at h
      exact h
    have hnextCanon := hnext
    rw [hz] at hnextCanon
    rw [hz]
    exact bankTrialDurationOrphanInteriorCarryField
      ring root hw j hj z.bank begun nextBegun hcanon hnextCanon
  · intro nextBegun hnext harmed
    obtain ⟨begun, hprev⟩ := bankTrialDurationNextLiveOrigin
      ring root (Counter.site ring root j.val) z nextBegun hnext
    have hz := bankTrialCmpStateEta z begun hprev
    have hcanon : BankTrialDurationOrphanInv q
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
      have h := hinv
      rw [hz] at h
      exact h
    have hnextCanon := hnext
    have harmedCanon := harmed
    rw [hz] at hnextCanon harmedCanon
    rw [hz]
    exact bankTrialDurationOrphanInteriorArmedField
      ring root hw j hj z.bank begun nextBegun
      hcanon hnextCanon harmedCanon
  · intro nextBegun hnext hmode
    obtain ⟨begun, hprev⟩ := bankTrialDurationNextLiveOrigin
      ring root (Counter.site ring root j.val) z nextBegun hnext
    have hz := bankTrialCmpStateEta z begun hprev
    have hcanon : BankTrialDurationOrphanInv q
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
      have h := hinv
      rw [hz] at h
      exact h
    have hnextCanon := hnext
    have hmodeCanon := hmode
    rw [hz] at hnextCanon hmodeCanon
    rw [hz]
    exact bankTrialDurationOrphanInteriorWorkerField
      ring root hw hK j hj z.bank begun nextBegun
      hcanon hnextCanon hmodeCanon
  · intro nextBegun hnext k htok
    obtain ⟨begun, hprev⟩ := bankTrialDurationNextLiveOrigin
      ring root (Counter.site ring root j.val) z nextBegun hnext
    have hz := bankTrialCmpStateEta z begun hprev
    have hcanon : BankTrialDurationOrphanInv q
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
      have h := hinv
      rw [hz] at h
      exact h
    have hnextCanon := hnext
    have htokCanon := htok
    rw [hz] at hnextCanon htokCanon
    rw [hz]
    exact bankTrialDurationOrphanInteriorCRZeroField
      ring root hw j hj z.bank begun nextBegun
      hcanon hnextCanon k htokCanon
  · intro nextBegun hnext k htok
    obtain ⟨begun, hprev⟩ := bankTrialDurationNextLiveOrigin
      ring root (Counter.site ring root j.val) z nextBegun hnext
    have hz := bankTrialCmpStateEta z begun hprev
    have hcanon : BankTrialDurationOrphanInv q
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
      have h := hinv
      rw [hz] at h
      exact h
    have hnextCanon := hnext
    have htokCanon := htok
    rw [hz] at hnextCanon htokCanon
    rw [hz]
    exact bankTrialDurationOrphanInteriorCLZeroField
      ring root hw j hj z.bank begun nextBegun
      hcanon hnextCanon k htokCanon

/-- All four supported source classes preserve the invariant. -/
theorem bankTrialDurationOrphanRowsHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    BankTrialDurationOrphanRows (q := q) ring root :=
  bankTrialDurationOrphanRowsOfRootInterior
    ring root hw hK
    (bankTrialDurationOrphanRootRow ring root hw hK)
    (bankTrialDurationOrphanInteriorRows ring root hw hK)

/-- The requested no-reachable-orphan theorem. -/
theorem bankTrialDurationNoReachableOrphanHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    BankTrialDurationNoReachableOrphan (q := q) ring root := by
  exact bankTrialDurationNoReachableOrphanHoldsOfRows
    ring root hsmall hw hpositive hK
    (bankTrialDurationOrphanRowsHolds ring root hw hK)

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- A live RESET reference has no worker-lease fallback; its
lease-aware charge is bounded by its protected-token maximum. -/
theorem bankTrialDurationReferenceResetLeMaximum {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool)
    (hm : bankTrialLiveWaveRootMode B = .RESET) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) ≤
      bankTrialDurationWorkerTokenMaximum B := by
  have hna : bankTrialLiveWaveRootMode B ≠ .ARMED := by
    intro h
    rw [hm] at h
    cases h
  have hnc : bankTrialLiveWaveRootMode B ≠ .CSTART := by
    intro h
    rw [hm] at h
    cases h
  have hfallback : bankTrialDurationWorkerLeaseFallback B = 0 := by
    unfold bankTrialDurationWorkerLeaseFallback
    rw [hm]
    simp
  have hraw :
      bankTrialDurationWorkerRemaining
        (⟨B, .live begun⟩ : BankTrialLocalState q) ≤
      bankTrialDurationWorkerTokenMaximum B := by
    unfold bankTrialDurationWorkerRemaining
    rw [if_neg hna, if_neg hnc, hfallback]
    simpa only [Nat.max_zero] using
      (Nat.min_le_right (bankTrialDurationWorkerLimit q)
        (bankTrialDurationWorkerTokenMaximum B))
  unfold bankTrialDurationLeaseAwareWorkerRemaining
  split
  · exact Nat.zero_le _
  · exact hraw

/-- Uniform reference-level wait row. Unlike the existing
NextWeakOfMaximum lemma, this keeps the successor provisionally
LIVE even when the actual next phase enters RECOVERY. -/
theorem bankTrialDurationReferenceWaitWeakOfMaximum {q : Nat}
    (A B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool)
    (hm : bankTrialLiveWaveRootMode A = .IWAIT ∨
      bankTrialLiveWaveRootMode A = .CWAIT)
    (hp : 0 < bankTrialDurationWorkerTokenMaximum A)
    (hmax : bankTrialDurationWorkerTokenMaximum B ≤
      bankTrialDurationWorkerTokenMaximum A)
    (hmode : bankTrialLiveWaveRootMode B =
        bankTrialLiveWaveRootMode A ∨
      bankTrialLiveWaveRootMode B = .RESET) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨A, .live begun⟩ : BankTrialLocalState q) := by
  rw [bankTrialDurationLeaseAwareWaitWorkerExact A begun hm hp]
  rcases hmode with hsame | hreset
  · have hmnew : bankTrialLiveWaveRootMode B = .IWAIT ∨
        bankTrialLiveWaveRootMode B = .CWAIT := by
      rw [hsame]
      exact hm
    exact Nat.le_trans
      (bankTrialDurationLeaseAwareWaitWorkerLeMaximum
        B begun hmnew) hmax
  · exact Nat.le_trans
      (bankTrialDurationReferenceResetLeMaximum B begun hreset)
      hmax

/-- A truly unsupported edge satisfies the stronger reference
weak row without any reachability or mode hypothesis. -/
theorem bankTrialDurationReferenceOutsideWeak {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool)
    (hout : ¬ Counter.Support q ring root e) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B e, .live begun⟩ : BankTrialLocalState q) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  rw [bankTrialLiveCarryUnsupportedRawFrame
    ring root e B hout]
  exact Nat.le_refl _

/-- The top-boundary wait row is weak at the clamped reference,
not merely after the observer's phase transition. -/
theorem bankTrialDurationReferenceTopWaitWeak {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hp : 0 < bankTrialDurationWorkerTokenMaximum B) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root (compileAdvice q).b),
        .live begun⟩ : BankTrialLocalState q) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  exact bankTrialDurationReferenceWaitWeakOfMaximum
    B (GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root (compileAdvice q).b))
    begun hm hp
    (bankTrialDurationTopMaximumWeak ring root hw B hf)
    (Or.inl (bankTrialDurationTopRootModeFrame
      ring root hw B hf))

/-- The incoming-root wait row is weak at the raw reference,
including the transition that changes its root mode to RESET. -/
theorem bankTrialDurationReferenceIncomingWaitWeak {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hin : ring.rightNeighbor e = root)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hp : 0 < bankTrialDurationWorkerTokenMaximum B) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B e, .live begun⟩ : BankTrialLocalState q) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  have hframe := bankTrialDurationIncomingMaximumFrame
    ring root e hw hin B hf
  have hmax :
      bankTrialDurationWorkerTokenMaximum
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) ≤
        bankTrialDurationWorkerTokenMaximum B := by
    rw [hframe]
    exact Nat.le_refl _
  exact bankTrialDurationReferenceWaitWeakOfMaximum
    B (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e) begun hm hp hmax
    (bankTrialDurationIncomingWaitModeCases
      ring root e hw hin B hf hm)

/-- When the first protected token is empty, an outgoing-root
wait is also reference-weak, including watchdog RESET. -/
theorem bankTrialDurationReferenceRootEmptyWaitWeak {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hp : 0 < bankTrialDurationWorkerTokenMaximum B)
    (hfirst : bankTrialLiveWaveToken B
      ⟨0, bankTrialWindowWidthPos q⟩ = .E) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B root, .live begun⟩ : BankTrialLocalState q) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  have hframe := bankTrialDurationRootWaitEmptyMaximumFrame
    ring root hw B hf hm hfirst
  have hmax :
      bankTrialDurationWorkerTokenMaximum
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) ≤
        bankTrialDurationWorkerTokenMaximum B := by
    rw [hframe]
    exact Nat.le_refl _
  exact bankTrialDurationReferenceWaitWeakOfMaximum
    B (GrantBankReference.bankLocalReferenceStepClamped
      ring root B root) begun hm hp hmax
    (bankTrialDurationRootWaitEmptyModeCases
      ring root hw B hf hm hfirst)

/-- Extract the entire proved strengthened LIVE invariant at
an actual reachable state; no synthetic reachable token is used. -/
theorem bankTrialDurationReachableOrphanInv {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (S : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (z : BankTrialLocalState q)
    (hreach : BankTrialDurationReachable ring root S z) :
    BankTrialDurationOrphanInv q z := by
  obtain ⟨word, hword⟩ := hreach
  have hinv := bankTrialDurationOrphanInvRunOfRows
    ring root (bankTrialDurationOrphanRowsHolds ring root hw hK)
    word (bankTrialLocalStart S)
    (bankTrialDurationOrphanInvClean S hclean hpositive)
  rw [hword] at hinv
  exact hinv

/-- The no-RWAIT field of the proved strengthened invariant
removes the third alternative in the earlier class-one trichotomy. -/
theorem bankTrialDurationReachableClassOneCStartOrWait {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (S : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool)
    (hreach : BankTrialDurationReachable ring root S
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hclass : bankTrialDurationLeaseAwareClass
      (⟨B, .live begun⟩ : BankTrialLocalState q) = 1) :
    bankTrialLiveWaveRootMode B = .CSTART ∨
    ((bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT) ∧
      0 < bankTrialDurationWorkerTokenMaximum B) := by
  have hinv := bankTrialDurationReachableOrphanInv
    ring root hw hpositive hK S hclean
    (⟨B, .live begun⟩ : BankTrialLocalState q) hreach
  rcases bankTrialDurationClassOneReachableModeCases
      ring root hw S hclean B begun hreach hclass with
    hs | hr | hwait
  · exact Or.inl hs
  · exact False.elim (hinv.noLiveResetWait begun rfl hr)
  · exact Or.inr hwait

/-- Final C.6 composition, with the two *unproved* class-one
obligations still explicitly supplied as hypotheses. This is
not the requested unconditional WorkerBudgetHolds. -/
theorem bankTrialDurationWorkerBudgetOfTwoClassOneGates {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hweak : BankTrialDurationClassOneReferenceWeakRows
      (q := q) ring root)
    (hcover : BankTrialDurationClassOneServiceCoverage
      (q := q) ring root) :
    BankTrialDurationWorkerBudget (q := q) ring root := by
  have hn : 2 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    omega
  exact bankTrialDurationWorkerBudgetOfLeaseAwareNoOrphan
    ring hn root
    (bankTrialDurationNoReachableOrphanHolds
      ring root hsmall hw hpositive hK)
    (bankTrialDurationLeaseAwareRowsOfWeakAndServiceCoverage
      ring root hw hweak hcover)

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Exact fold maximum when every protected token except one is empty. -/
theorem bankTrialDurationMaximumOfSingleToken {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (chosen : Fin (compileAdvice q).b)
    (hother : ∀ i : Fin (compileAdvice q).b, i ≠ chosen →
      bankTrialLiveWaveToken B i = .E) :
    bankTrialDurationWorkerTokenMaximum B =
      bankTrialDurationWorkerTokenRank (compileAdvice q).b
        (chosen.val + 1) (bankTrialLiveWaveToken B chosen) := by
  unfold bankTrialDurationWorkerTokenMaximum
  apply bankTrialDurationOfFnFoldMaxSpike
  intro i hi
  rw [hother i hi]
  rfl

/-- The CSTART class has exactly its reserved comparison-launch rank. -/
theorem bankTrialDurationCStartReferenceExact {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool)
    (hm : bankTrialLiveWaveRootMode B = .CSTART) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) =
        2 * (compileAdvice q).b + 2 := by
  have hna : bankTrialLiveWaveRootMode B ≠ .ARMED := by
    intro h
    rw [hm] at h
    cases h
  have hno :
      ¬ ((bankTrialLiveWaveRootMode B = .IWAIT ∨
          bankTrialLiveWaveRootMode B = .CWAIT) ∧
        bankTrialDurationWorkerTokenMaximum B = 0) := by
    intro h
    rcases h.1 with hi | hc
    · rw [hm] at hi
      cases hi
    · rw [hm] at hc
      cases hc
  have hclass : bankTrialDurationLeaseAwareClass
      (⟨B, .live begun⟩ : BankTrialLocalState q) = 1 := by
    change
      (if bankTrialLiveWaveRootMode B = .ARMED then 0
       else if
         ((bankTrialLiveWaveRootMode B = .IWAIT ∨
           bankTrialLiveWaveRootMode B = .CWAIT) ∧
          bankTrialDurationWorkerTokenMaximum B = 0)
       then 2 else 1) = 1
    rw [if_neg hna, if_neg hno]
  unfold bankTrialDurationLeaseAwareWorkerRemaining
  rw [hclass]
  change bankTrialDurationWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) =
        2 * (compileAdvice q).b + 2
  unfold bankTrialDurationWorkerRemaining
  rw [if_neg hna, if_pos hm]
  change Nat.min (2 * (2 * (compileAdvice q).b + 2) + 1)
    (2 * (compileAdvice q).b + 2) =
      2 * (compileAdvice q).b + 2
  exact Nat.min_eq_right (by omega)

/-- A mode-preserving CSTART service is reference weak even if
the reference has arbitrary irrelevant scratch fields. -/
theorem bankTrialDurationReferenceCStartModeWeak {q : Nat}
    (A B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool)
    (ha : bankTrialLiveWaveRootMode A = .CSTART)
    (hb : bankTrialLiveWaveRootMode B = .CSTART) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨A, .live begun⟩ : BankTrialLocalState q) := by
  rw [bankTrialDurationCStartReferenceExact A begun ha,
    bankTrialDurationCStartReferenceExact B begun hb]
  exact Nat.le_refl _

/-- CSTART has a genuine strict outgoing root service.
The comparator-launch stage authenticates both the
new CWAIT mode and its unique first-digit CR0/CR1 token. -/
theorem bankTrialDurationCStartRootStrict {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .CSTART) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) root) + 1 ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  have hstage := bankTrialCmpLaunch ring root hw
    (⟨B, .live begun⟩ : BankTrialLocalState q)
    ⟨begun, rfl⟩ hf hm (fun k => hc.headClear k (Or.inr hm))
  obtain ⟨_, _, hnewMode, _, _, htokens⟩ := hstage
  have hbank := bankTrialLocalNextLiveBank ring root root B begun
  have hrmode :
      bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) = .CWAIT := by
    rw [← hbank]
    exact hnewMode
  have hrtokens : ∀ k : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) k =
        if k.val = 0 then
          (if bankTrialCmpValue B 0 then .CR1 else .CR0)
        else .E := by
    intro k
    rw [← hbank]
    exact htokens k
  have hother : ∀ k : Fin (compileAdvice q).b,
      k ≠ ⟨0, bankTrialWindowWidthPos q⟩ →
      bankTrialLiveWaveToken
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) k = .E := by
    intro k hk
    have hne : k.val ≠ 0 := by
      intro he
      exact hk (Fin.ext he)
    rw [hrtokens k, if_neg hne]
  have hmax :
      bankTrialDurationWorkerTokenMaximum
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) + 1 ≤
        2 * (compileAdvice q).b + 2 := by
    rw [bankTrialDurationMaximumOfSingleToken
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root)
      ⟨0, bankTrialWindowWidthPos q⟩ hother,
      hrtokens ⟨0, bankTrialWindowWidthPos q⟩]
    change
      bankTrialDurationWorkerTokenRank (compileAdvice q).b 1
        (if bankTrialCmpValue B 0 then .CR1 else .CR0) + 1 ≤
      2 * (compileAdvice q).b + 2
    cases hb : bankTrialCmpValue B 0 <;>
      simp [hb, bankTrialDurationWorkerTokenRank] <;> omega
  have hnext := bankTrialDurationLeaseAwareNextLeLiveReference
    ring root root B begun
  have href := bankTrialDurationLeaseAwareWaitWorkerLeMaximum
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B root) begun (Or.inr hrmode)
  have hold := bankTrialDurationCStartReferenceExact B begun hm
  omega

theorem bankTrialDurationCStartRootNominated {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .CSTART) :
    BankTrialDurationOtherNominatedEdge ring root B begun := by
  refine ⟨root, Or.inl rfl, ?_⟩
  exact bankTrialDurationCStartRootStrict ring root hw B begun hf hc hm

/-- CWAIT/CL1 at the first digit wins on the literal outgoing
root edge. Its old single-worker rank is exactly one. -/
theorem bankTrialDurationCWaitFirstCLTrueNominated {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .CWAIT)
    (ht : bankTrialLiveWaveToken B
      ⟨0, bankTrialWindowWidthPos q⟩ = .CL1) :
    BankTrialDurationOtherNominatedEdge ring root B begun := by
  have hnot : bankTrialLiveWaveToken B
      ⟨0, bankTrialWindowWidthPos q⟩ ≠ .E := by
    rw [ht]
    intro h
    cases h
  have hother : ∀ i : Fin (compileAdvice q).b,
      i ≠ ⟨0, bankTrialWindowWidthPos q⟩ →
      bankTrialLiveWaveToken B i = .E := by
    intro i hi
    exact bankTrialInteriorOldWorkerOthersEmpty B hc
      ⟨0, bankTrialWindowWidthPos q⟩ i hnot hi
  have hmax : bankTrialDurationWorkerTokenMaximum B = 1 := by
    rw [bankTrialDurationMaximumOfSingleToken B
      ⟨0, bankTrialWindowWidthPos q⟩ hother, ht]
    rfl
  have hpos : 0 < bankTrialDurationWorkerTokenMaximum B := by
    omega
  have hcurrent :
      bankTrialDurationLeaseAwareWorkerRemaining
        (⟨B, .live begun⟩ : BankTrialLocalState q) = 1 := by
    rw [bankTrialDurationLeaseAwareWaitWorkerExact
      B begun (Or.inr hm) hpos, hmax]
  have hphase := bankTrialProbabilityLiveReturnWon
    ring root B begun hf hm
    (show (B.fields ⟨1, by have := bankTrialCmpWidth q; omega⟩).2.2.1 = .CL1 from ht)
  have hzero :
      bankTrialDurationLeaseAwareWorkerRemaining
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) root) = 0 := by
    cases hnext : bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) root with
    | mk C phase =>
        rw [hnext] at hphase
        cases phase with
        | live nextBegun => cases hphase
        | recovery => cases hphase
        | won => rfl
        | lost => cases hphase
  refine ⟨root, Or.inl rfl, ?_⟩
  rw [hzero, hcurrent]
  exact Nat.le_refl _

/-- For a first-digit CL0, the real root pair enters ARMED
and destroys the only worker. -/
theorem bankTrialDurationCWaitFirstCLFalseNominated {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .CWAIT)
    (ht : bankTrialLiveWaveToken B
      ⟨0, bankTrialWindowWidthPos q⟩ = .CL0) :
    BankTrialDurationOtherNominatedEdge ring root B begun := by
  have hnot : bankTrialLiveWaveToken B
      ⟨0, bankTrialWindowWidthPos q⟩ ≠ .E := by
    rw [ht]
    intro h
    cases h
  have hother : ∀ i : Fin (compileAdvice q).b,
      i ≠ ⟨0, bankTrialWindowWidthPos q⟩ →
      bankTrialLiveWaveToken B i = .E := by
    intro i hi
    exact bankTrialInteriorOldWorkerOthersEmpty B hc
      ⟨0, bankTrialWindowWidthPos q⟩ i hnot hi
  have hmax : bankTrialDurationWorkerTokenMaximum B = 1 := by
    rw [bankTrialDurationMaximumOfSingleToken B
      ⟨0, bankTrialWindowWidthPos q⟩ hother, ht]
    rfl
  have hpos : 0 < bankTrialDurationWorkerTokenMaximum B := by
    omega
  have hcurrent :
      bankTrialDurationLeaseAwareWorkerRemaining
        (⟨B, .live begun⟩ : BankTrialLocalState q) = 1 := by
    rw [bankTrialDurationLeaseAwareWaitWorkerExact
      B begun (Or.inr hm) hpos, hmax]
  have hraw := bankTrialCmpRawCLZeroRootReturn
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B ⟨0, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B ⟨1, by have := bankTrialCmpWidth q; omega⟩)
    (by have := bankTrialCmpWidth q; omega) rfl rfl rfl hm
    (show (B.fields ⟨1, by have := bankTrialCmpWidth q; omega⟩).2.2.1 = .CL0 from ht)
  have hmnew :
      bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) = .ARMED :=
    (bankTrialCmpRoot ring root hw B hf).1.trans hraw.1
  have hrefzero := bankTrialDurationLeaseAwareArmedRankZero
    (⟨GrantBankReference.bankLocalReferenceStepClamped
      ring root B root, .live begun⟩ : BankTrialLocalState q) hmnew
  have hnext := bankTrialDurationLeaseAwareNextLeLiveReference
    ring root root B begun
  have hzero : bankTrialDurationLeaseAwareWorkerRemaining
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) root) ≤ 0 := by
    rw [hrefzero] at hnext
    exact hnext
  refine ⟨root, Or.inl rfl, ?_⟩
  rw [hcurrent]
  omega

/-- A first-digit AL returns to CSTART. It pays at least one
unit against the larger old AL rank. -/
theorem bankTrialDurationRawALRootReturn
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 < b)
    (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false) (hm : x.mode = .IWAIT)
    (ht : y.tok = .AL) :
    (bankPair x y 1 b theta).1.mode = .CSTART ∧
    (bankPair x y 1 b theta).2.tok = .E := by
  have hbpos : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  simp [bankPair, hx, hy, hg, hm, ht, hbpos, hbne,
    isRetTok, isWaitMode, Id.run_pure, Id.run_bind]

theorem bankTrialDurationIWaitFirstALNominated {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT)
    (ht : bankTrialLiveWaveToken B
      ⟨0, bankTrialWindowWidthPos q⟩ = .AL) :
    BankTrialDurationOtherNominatedEdge ring root B begun := by
  have hnot : bankTrialLiveWaveToken B
      ⟨0, bankTrialWindowWidthPos q⟩ ≠ .E := by
    rw [ht]
    intro h
    cases h
  have hother : ∀ i : Fin (compileAdvice q).b,
      i ≠ ⟨0, bankTrialWindowWidthPos q⟩ →
      bankTrialLiveWaveToken B i = .E := by
    intro i hi
    exact bankTrialInteriorOldWorkerOthersEmpty B hc
      ⟨0, bankTrialWindowWidthPos q⟩ i hnot hi
  have hmax :
      bankTrialDurationWorkerTokenMaximum B =
        2 * (compileAdvice q).b + 4 := by
    rw [bankTrialDurationMaximumOfSingleToken B
      ⟨0, bankTrialWindowWidthPos q⟩ hother, ht]
    change 2 * (compileAdvice q).b + 3 + 1 =
      2 * (compileAdvice q).b + 4
    omega
  have hpos : 0 < bankTrialDurationWorkerTokenMaximum B := by
    omega
  have hcurrent :
      bankTrialDurationLeaseAwareWorkerRemaining
        (⟨B, .live begun⟩ : BankTrialLocalState q) =
          2 * (compileAdvice q).b + 4 := by
    rw [bankTrialDurationLeaseAwareWaitWorkerExact
      B begun (Or.inl hm) hpos, hmax]
  have hraw := bankTrialDurationRawALRootReturn
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B ⟨0, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B ⟨1, by have := bankTrialCmpWidth q; omega⟩)
    (by change 1 < (compileAdvice q).s + 11; omega)
    rfl rfl rfl hm
    (show (B.fields ⟨1, by have := bankTrialCmpWidth q; omega⟩).2.2.1 = .AL from ht)
  have hmnew :
      bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) = .CSTART :=
    (bankTrialCmpRoot ring root hw B hf).1.trans hraw.1
  have href := bankTrialDurationCStartReferenceExact
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B root) begun hmnew
  have hnext := bankTrialDurationLeaseAwareNextLeLiveReference
    ring root root B begun
  refine ⟨root, Or.inl rfl, ?_⟩
  rw [hcurrent]
  omega

/-- A selected internal E/E pair cannot create a token; it is
a full protected-token maximum frame, not just a source-bit frame. -/
theorem bankTrialDurationInteriorEmptyPairMaximumFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .E)
    (hdst : (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .E) :
    bankTrialDurationWorkerTokenMaximum
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val)) =
      bankTrialDurationWorkerTokenMaximum B := by
  have hraw := bankTrialInteriorRawEmptyPair
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by omega⟩)
    (by change 1 ≤ j.val; omega) j.isLt rfl hsrc hdst
  apply bankTrialDurationMaximumTokenCongr
  intro k
  change
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
      ⟨k.val + 1, by omega⟩).2.2.1 =
    (B.fields ⟨k.val + 1, by omega⟩).2.2.1
  by_cases hs : k.val + 1 = j.val
  · have heq :
        (⟨k.val + 1, by omega⟩ :
          Fin ((compileAdvice q).b + 1)) =
        ⟨j.val, by omega⟩ := Fin.ext hs
    rw [heq, bankTrialWindowInteriorSource ring root B hf j]
    rw [(bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).1)).2]
    exact hraw.1.trans hsrc.symm
  · by_cases ht : k.val + 1 = j.val + 1
    · have heq :
          (⟨k.val + 1, by omega⟩ :
            Fin ((compileAdvice q).b + 1)) =
          ⟨j.val + 1, by omega⟩ := Fin.ext ht
      rw [heq, bankTrialWindowInteriorResponder ring root hw B hf j]
      rw [(bankTrialLiveClampBitToken q
        ((GrantBankReference.bankLocalReferenceInternalPair q B j).2)).2]
      exact hraw.2.1.trans hdst.symm
    · rw [bankTrialWindowInteriorFrame ring root hw B hf
        j hj ⟨k.val + 1, by omega⟩ hs ht]

/-- A zero-token selected interior pair is a weak reference edge,
regardless of where the unique old worker is positioned. -/
theorem bankTrialDurationReferenceInteriorEmptyPairWeak {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hp : 0 < bankTrialDurationWorkerTokenMaximum B)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .E)
    (hdst : (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .E) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val), .live begun⟩ :
        BankTrialLocalState q) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  have hmax := bankTrialDurationInteriorEmptyPairMaximumFrame
    ring root hw B hf j hj hsrc hdst
  have hle :
      bankTrialDurationWorkerTokenMaximum
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) ≤
        bankTrialDurationWorkerTokenMaximum B := by
    rw [hmax]
    exact Nat.le_refl _
  exact bankTrialDurationReferenceWaitWeakOfMaximum
    B (GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val))
    begun hm hp hle
    (Or.inl (bankTrialWindowInteriorRootModeFrame
      ring root hw B hf j hj))

/-- The four existing strict maximum-drop owner rows imply
reference weakness on every selected IR/AL/CR/CL interior service. -/
theorem bankTrialDurationReferenceSelectedInteriorWeak {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hselected : BankTrialDurationSelectedInteriorCondition B j) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val), .live begun⟩ :
        BankTrialLocalState q) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  have hmode := bankTrialWindowInteriorRootModeFrame
    ring root hw B hf j hj
  have hdrop : bankTrialDurationWorkerTokenMaximum
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val)) + 1 ≤
      bankTrialDurationWorkerTokenMaximum B := by
    unfold BankTrialDurationSelectedInteriorCondition at hselected
    rcases hselected with hi | hcwait
    · obtain ⟨hm, hcases⟩ := hi
      rcases hcases with ⟨hs, hd⟩ | ⟨hs, hd⟩
      · exact bankTrialDurationSelectedIRMaximumDrop
          ring root hw B hf hc j hj hs hd
      · exact bankTrialDurationSelectedALMaximumDrop
          ring root hw B hf hc j hj hs hd
    · obtain ⟨hm, hcases⟩ := hcwait
      rcases hcases with ⟨hs, hd⟩ | ⟨hs, hd⟩
      · exact bankTrialDurationSelectedCRMaximumDrop
          ring root hw B hf hc j hj hs hd
      · exact bankTrialDurationSelectedCLMaximumDrop
          ring root hw B hf hc j hj hs hd
  have hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT := by
    unfold BankTrialDurationSelectedInteriorCondition at hselected
    rcases hselected with hi | hcwait
    · exact Or.inl hi.1
    · exact Or.inr hcwait.1
  have hp : 0 < bankTrialDurationWorkerTokenMaximum B := by omega
  have hle :
      bankTrialDurationWorkerTokenMaximum
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) ≤
        bankTrialDurationWorkerTokenMaximum B := by omega
  exact bankTrialDurationReferenceWaitWeakOfMaximum
    B (GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val))
    begun hm hp hle (Or.inl hmode)

/-- A CSTART top service, and likewise any genuine protected
interior service, is reference weak because neither changes
the CSTART root mode. -/
theorem bankTrialDurationReferenceCStartTopWeak {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hm : bankTrialLiveWaveRootMode B = .CSTART) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root (compileAdvice q).b),
        .live begun⟩ : BankTrialLocalState q) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  exact bankTrialDurationReferenceCStartModeWeak
    B (GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root (compileAdvice q).b))
    begun hm
    ((bankTrialDurationTopRootModeFrame ring root hw B hf).trans hm)

/-- A CSTART interior service is mode-preserving; unlike the
root-edge launch it cannot create a new CWAIT occupation. -/
theorem bankTrialDurationReferenceCStartInteriorWeak {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hm : bankTrialLiveWaveRootMode B = .CSTART)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val), .live begun⟩ :
        BankTrialLocalState q) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  exact bankTrialDurationReferenceCStartModeWeak
    B (GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val))
    begun hm
    ((bankTrialWindowInteriorRootModeFrame
      ring root hw B hf j hj).trans hm)

/-- Incoming at CSTART is its exceptional mode-preserving boundary row. -/
theorem bankTrialDurationReferenceCStartIncomingWeak {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hm : bankTrialLiveWaveRootMode B = .CSTART)
    (hne : e ≠ root) (hin : ring.rightNeighbor e = root) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B e, .live begun⟩ : BankTrialLocalState q) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  exact bankTrialDurationReferenceCStartModeWeak
    B (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e) begun hm
    (bankTrialProbabilityIncomingCStartMode
      ring root e B hf hm hne hin)

end L3

namespace L3


open Classical
open FiniteUniformStoppingTree


set_option autoImplicit false
set_option Elab.async false


/-- The physical source digit j is wave position j-1. -/
theorem bankTrialDurationInteriorSourceWaveToken {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val) :
    (B.fields ⟨j.val, by omega⟩).2.2.1 =
      bankTrialLiveWaveToken B
        ⟨j.val - 1, by have h := j.isLt; omega⟩ := by
  change
    (B.fields ⟨j.val, by omega⟩).2.2.1 =
    (B.fields ⟨j.val - 1 + 1, by omega⟩).2.2.1
  have heq : (⟨j.val, by omega⟩ :
      Fin ((compileAdvice q).b + 1)) =
      ⟨j.val - 1 + 1, by omega⟩ :=
    Fin.ext (show j.val = j.val - 1 + 1 by omega)
  rw [heq]


/-- Unique worker at the left position forces the right empty. -/
theorem bankTrialDurationInteriorRightEmptyOfLeft {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hleft : bankTrialLiveWaveToken B
        ⟨j.val - 1, by have h := j.isLt; omega⟩ ≠ .E) :
    bankTrialLiveWaveToken B j = .E := by
  by_cases he : bankTrialLiveWaveToken B j = .E
  · exact he
  · have hsame := hc.uniqueWorker
      ⟨j.val - 1, by have h := j.isLt; omega⟩ j hleft he
    have hv := congrArg Fin.val hsame
    change j.val - 1 = j.val at hv
    omega


/-- Unique worker at the right position forces the left empty. -/
theorem bankTrialDurationInteriorLeftEmptyOfRight {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hright : bankTrialLiveWaveToken B j ≠ .E) :
    bankTrialLiveWaveToken B
      ⟨j.val - 1, by have h := j.isLt; omega⟩ = .E := by
  by_cases he : bankTrialLiveWaveToken B
      ⟨j.val - 1, by have h := j.isLt; omega⟩ = .E
  · exact he
  · have hsame := hc.uniqueWorker
      ⟨j.val - 1, by have h := j.isLt; omega⟩ j he hright
    have hv := congrArg Fin.val hsame
    change j.val - 1 = j.val at hv
    omega


/-- A forward IR/CR worker below the top has a selected service. -/
theorem bankTrialDurationForwardWorkerCovered {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (w : Fin (compileAdvice q).b)
    (hworker : bankTrialLiveWaveToken B w ≠ .E)
    (hspace : w.val + 1 < (compileAdvice q).b)
    (hkind :
      (bankTrialLiveWaveRootMode B = .IWAIT ∧
        bankTrialLiveWaveToken B w = .IR) ∨
      (bankTrialLiveWaveRootMode B = .CWAIT ∧
        (bankTrialLiveWaveToken B w = .CR0 ∨
         bankTrialLiveWaveToken B w = .CR1))) :
    ∃ j : Fin (compileAdvice q).b,
      0 < j.val ∧ BankTrialDurationSelectedInteriorCondition B j := by
  have hne : (⟨w.val + 1, hspace⟩ :
      Fin (compileAdvice q).b) ≠ w := by
    intro he
    have hv := congrArg Fin.val he
    change w.val + 1 = w.val at hv
    omega
  have hright := bankTrialInteriorOldWorkerOthersEmpty
    B hc w ⟨w.val + 1, hspace⟩ hworker hne
  refine ⟨⟨w.val + 1, hspace⟩, (show 0 < w.val + 1 by omega), ?_⟩
  unfold BankTrialDurationSelectedInteriorCondition
  rcases hkind with hi | hcomp
  · exact Or.inl ⟨hi.1, Or.inl ⟨hi.2, hright⟩⟩
  · exact Or.inr ⟨hcomp.1, Or.inl ⟨hcomp.2, hright⟩⟩


/-- A returning AL/CL worker away from digit one has a selected
interior service; the immediately preceding wave slot is empty. -/
theorem bankTrialDurationReturnWorkerCovered {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (w : Fin (compileAdvice q).b)
    (hworker : bankTrialLiveWaveToken B w ≠ .E)
    (hwpos : 0 < w.val)
    (hkind :
      (bankTrialLiveWaveRootMode B = .IWAIT ∧
        bankTrialLiveWaveToken B w = .AL) ∨
      (bankTrialLiveWaveRootMode B = .CWAIT ∧
        (bankTrialLiveWaveToken B w = .CL0 ∨
         bankTrialLiveWaveToken B w = .CL1))) :
    ∃ j : Fin (compileAdvice q).b,
      0 < j.val ∧ BankTrialDurationSelectedInteriorCondition B j := by
  have hne : (⟨w.val - 1, by have h := w.isLt; omega⟩ :
      Fin (compileAdvice q).b) ≠ w := by
    intro he
    have hv := congrArg Fin.val he
    change w.val - 1 = w.val at hv
    omega
  have hprevious := bankTrialInteriorOldWorkerOthersEmpty
    B hc w ⟨w.val - 1, by have h := w.isLt; omega⟩ hworker hne
  have hsrc : (B.fields ⟨w.val, by omega⟩).2.2.1 = .E := by
    rw [bankTrialDurationInteriorSourceWaveToken B w hwpos]
    exact hprevious
  refine ⟨w, hwpos, ?_⟩
  unfold BankTrialDurationSelectedInteriorCondition
  rcases hkind with hi | hcomp
  · exact Or.inl ⟨hi.1, Or.inr ⟨hsrc, hi.2⟩⟩
  · exact Or.inr ⟨hcomp.1, Or.inr ⟨hsrc, hcomp.2⟩⟩


/-- A CR0/CR1 top worker uses the last interior source edge. -/
theorem bankTrialDurationTopComparisonCovered {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .CWAIT)
    (w : Fin (compileAdvice q).b)
    (hworker : bankTrialLiveWaveToken B w ≠ .E)
    (htop : w.val + 1 = (compileAdvice q).b)
    (hcr : bankTrialLiveWaveToken B w = .CR0 ∨
      bankTrialLiveWaveToken B w = .CR1) :
    BankTrialDurationOtherNominatedEdge ring root B begun := by
  have hb : 2 ≤ (compileAdvice q).b := by
    have hwidth := bankTrialCmpWidth q
    omega
  have hwpos : 0 < w.val := by omega
  have hne : (⟨w.val - 1, by have h := w.isLt; omega⟩ :
      Fin (compileAdvice q).b) ≠ w := by
    intro he
    have hv := congrArg Fin.val he
    change w.val - 1 = w.val at hv
    omega
  have hprevious := bankTrialInteriorOldWorkerOthersEmpty
    B hc w ⟨w.val - 1, by have h := w.isLt; omega⟩ hworker hne
  have hsrcAtW : (B.fields ⟨w.val, by omega⟩).2.2.1 = .E := by
    rw [bankTrialDurationInteriorSourceWaveToken B w hwpos]
    exact hprevious
  have hsrc :
      (B.fields ⟨(compileAdvice q).b - 1, by omega⟩).2.2.1 =
        .E := by
    have hindex : (⟨w.val, by omega⟩ :
        Fin ((compileAdvice q).b + 1)) =
        ⟨(compileAdvice q).b - 1, by omega⟩ :=
      Fin.ext (show w.val = (compileAdvice q).b - 1 by omega)
    rw [← hindex]
    exact hsrcAtW
  have hdst :
      (B.fields ⟨(compileAdvice q).b, by omega⟩).2.2.1 =
        .CR0 ∨
      (B.fields ⟨(compileAdvice q).b, by omega⟩).2.2.1 =
        .CR1 := by
    simpa only [bankTrialLiveWaveToken, htop] using hcr
  exact bankTrialDurationCWaitTopTurnNominated
    ring root hw B begun hf hc hm hsrc hdst


/-- Reachable waiting-wave coverage by token kind and position. -/
theorem bankTrialDurationReachableWaitServiceCoverage {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hinv : BankTrialDurationOrphanInv q
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT) :
    (∃ j : Fin (compileAdvice q).b,
      0 < j.val ∧ BankTrialDurationSelectedInteriorCondition B j) ∨
      BankTrialDurationOtherNominatedEdge ring root B begun := by
  have hc : BankTrialLiveWaveCertificate q B :=
    hinv.locked.1 begun rfl
  obtain ⟨w, hworker⟩ := hinv.workerPresent begun rfl hm
  rcases hm with hi | hcomp
  · rcases hc.iwaitTokens w hi with he | hir | hal
    · exact False.elim (hworker he)
    · by_cases htop : w.val + 1 = (compileAdvice q).b
      · have hwtop : w = bankTrialDurationTopDigit q := by
          apply Fin.ext
          change w.val = (compileAdvice q).b - 1
          omega
        have hno := bankTrialDurationOrphanInvNoTopIR
          (⟨B, .live begun⟩ : BankTrialLocalState q)
          hinv hK begun rfl
        exact False.elim (hno (by rw [← hwtop]; exact hir))
      · have hspace : w.val + 1 < (compileAdvice q).b := by
          have hwlt := w.isLt
          omega
        exact Or.inl (bankTrialDurationForwardWorkerCovered
          B hc w hworker hspace (Or.inl ⟨hi, hir⟩))
    · by_cases hz : w.val = 0
      · have hindex : w = ⟨0, bankTrialWindowWidthPos q⟩ :=
          Fin.ext hz
        have hfirst : bankTrialLiveWaveToken B
            ⟨0, bankTrialWindowWidthPos q⟩ = .AL := by
          rw [← hindex]
          exact hal
        exact Or.inr (bankTrialDurationIWaitFirstALNominated
          ring root hw B begun hf hc hi hfirst)
      · have hwpos : 0 < w.val := by omega
        exact Or.inl (bankTrialDurationReturnWorkerCovered
          B hc w hworker hwpos (Or.inl ⟨hi, hal⟩))
  · rcases hc.cwaitTokens w hcomp with he | ht
    · exact False.elim (hworker he)
    · have hkind :
        (bankTrialLiveWaveToken B w = .CR0 ∨
          bankTrialLiveWaveToken B w = .CR1) ∨
        (bankTrialLiveWaveToken B w = .CL0 ∨
          bankTrialLiveWaveToken B w = .CL1) := by
        unfold BankTrialLiveComparisonToken at ht
        rcases ht with hzero | hone | hbackZero | hbackOne
        · exact Or.inl (Or.inl hzero)
        · exact Or.inl (Or.inr hone)
        · exact Or.inr (Or.inl hbackZero)
        · exact Or.inr (Or.inr hbackOne)
      rcases hkind with hcr | hcl
      · by_cases htop : w.val + 1 = (compileAdvice q).b
        · exact Or.inr (bankTrialDurationTopComparisonCovered
            ring root hw B begun hf hc hcomp w hworker htop hcr)
        · have hspace : w.val + 1 < (compileAdvice q).b := by
            have hwlt := w.isLt
            omega
          exact Or.inl (bankTrialDurationForwardWorkerCovered
            B hc w hworker hspace (Or.inr ⟨hcomp, hcr⟩))
      · by_cases hz : w.val = 0
        · have hindex : w = ⟨0, bankTrialWindowWidthPos q⟩ :=
            Fin.ext hz
          have hfirst :
              bankTrialLiveWaveToken B
                ⟨0, bankTrialWindowWidthPos q⟩ = .CL0 ∨
              bankTrialLiveWaveToken B
                ⟨0, bankTrialWindowWidthPos q⟩ = .CL1 := by
            rw [← hindex]
            exact hcl
          rcases hfirst with hzero | hone
          · exact Or.inr (bankTrialDurationCWaitFirstCLFalseNominated
              ring root hw B begun hf hc hcomp hzero)
          · exact Or.inr (bankTrialDurationCWaitFirstCLTrueNominated
              ring root B begun hf hc hcomp hone)
        · have hwpos : 0 < w.val := by omega
          exact Or.inl (bankTrialDurationReturnWorkerCovered
            B hc w hworker hwpos (Or.inr ⟨hcomp, hcl⟩))


/-- The service coverage gate follows from the reachable invariant. -/
theorem bankTrialDurationClassOneServiceCoverageHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    BankTrialDurationClassOneServiceCoverage (q := q) ring root := by
  intro S hclean B begun hreach hclass
  have hinv := bankTrialDurationReachableOrphanInv
    ring root hw hpositive hK S hclean
    (⟨B, .live begun⟩ : BankTrialLocalState q) hreach
  obtain ⟨word, hword⟩ := id hreach
  have hf := bankTrialProbabilityCleanLiveUnlatched
    ring root S hclean word B begun hword
  have hc : BankTrialLiveWaveCertificate q B :=
    hinv.locked.1 begun rfl
  rcases bankTrialDurationReachableClassOneCStartOrWait
    ring root hw hpositive hK S hclean B begun hreach hclass with
    hstart | hwait
  · exact Or.inr (bankTrialDurationCStartRootNominated
      ring root hw B begun hf hc hstart)
  · exact bankTrialDurationReachableWaitServiceCoverage
      ring root hw hK B begun hf hinv hwait.1


end L3

namespace L3

open Classical
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- A returning AL/CL at an interior SOURCE, with an empty
responder, is held. The old pair has no reverse-return guard. -/
theorem bankTrialDurationRawHeldSourceTokens
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hsrc : x.tok = .AL ∨ x.tok = .CL0 ∨ x.tok = .CL1)
    (hdst : y.tok = .E) :
    (bankPair x y y.role b theta).1.tok = x.tok ∧
    (bankPair x y y.role b theta).2.tok = y.tok := by
  have hxn : x.role ≠ 0 := by omega
  have hxTop : x.role ≠ b := by omega
  have hyn : y.role ≠ 0 := by omega
  have hyPos : 1 ≤ y.role := by omega
  have hyLe : y.role ≤ b := by omega
  have hxLe : x.role ≤ b := by omega
  have hboundary : ¬ b < x.role + 1 := by omega
  rcases hsrc with ha | hc0 | hc1
  · simp [bankPair, hx, hlt, hy, hxn, hxTop, hyn,
      hyPos, hyLe, hxLe, hboundary, ha, hdst,
      isRetTok, isWaitMode, Id.run_pure, Id.run_bind]
  · simp [bankPair, hx, hlt, hy, hxn, hxTop, hyn,
      hyPos, hyLe, hxLe, hboundary, hc0, hdst,
      isRetTok, isWaitMode, Id.run_pure, Id.run_bind]
  · simp [bankPair, hx, hlt, hy, hxn, hxTop, hyn,
      hyPos, hyLe, hxLe, hboundary, hc1, hdst,
      isRetTok, isWaitMode, Id.run_pure, Id.run_bind]

/-- An IR/CR on a non-top interior RESPONDER, with an empty
source, is held until its own forward source edge is served. -/
theorem bankTrialDurationRawHeldTargetTokens
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1) (hbelow : y.role < b)
    (hsrc : x.tok = .E)
    (hdst : y.tok = .IR ∨ y.tok = .CR0 ∨ y.tok = .CR1) :
    (bankPair x y y.role b theta).1.tok = x.tok ∧
    (bankPair x y y.role b theta).2.tok = y.tok := by
  have hxn : x.role ≠ 0 := by omega
  have hxTop : x.role ≠ b := by omega
  have hyn : y.role ≠ 0 := by omega
  have hyPos : 1 ≤ y.role := by omega
  have hyLe : y.role ≤ b := by omega
  have hxLe : x.role ≤ b := by omega
  have hboundary : ¬ b < x.role + 1 := by omega
  have hnotTop : y.role ≠ b := by omega
  have hxb1 : x.role + 1 ≠ b := by omega
  rcases hdst with hir | hc0 | hc1
  · simp [bankPair, hx, hlt, hy, hbelow, hnotTop,
      hxn, hxTop, hyn, hyPos, hyLe, hxLe,
      hboundary, hxb1, hsrc, hir, isRetTok, isWaitMode,
      Id.run_pure, Id.run_bind]
  · simp [bankPair, hx, hlt, hy, hbelow, hnotTop,
      hxn, hxTop, hyn, hyPos, hyLe, hxLe,
      hboundary, hxb1, hsrc, hc0, isRetTok, isWaitMode,
      Id.run_pure, Id.run_bind]
  · simp [bankPair, hx, hlt, hy, hbelow, hnotTop,
      hxn, hxTop, hyn, hyPos, hyLe, hxLe,
      hboundary, hxb1, hsrc, hc1, isRetTok, isWaitMode,
      Id.run_pure, Id.run_bind]

/-- If both pair-owner output tokens are unchanged, every
protected rank is unchanged on the original physical edge. -/
theorem bankTrialDurationInteriorHeldMaximumFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hpair :
      (GrantBankReference.bankLocalReferenceInternalPair q B j).1.tok =
        (GrantBankReference.bankLocalReferenceCell B
          ⟨j.val, by omega⟩).tok ∧
      (GrantBankReference.bankLocalReferenceInternalPair q B j).2.tok =
        (GrantBankReference.bankLocalReferenceCell B
          ⟨j.val + 1, by omega⟩).tok) :
    bankTrialDurationWorkerTokenMaximum
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val)) =
      bankTrialDurationWorkerTokenMaximum B := by
  apply bankTrialDurationMaximumTokenCongr
  intro k
  change
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨k.val + 1, by omega⟩).2.2.1 =
      (B.fields ⟨k.val + 1, by omega⟩).2.2.1
  by_cases hs : k.val + 1 = j.val
  · have heq :
        (⟨k.val + 1, by omega⟩ :
          Fin ((compileAdvice q).b + 1)) =
        ⟨j.val, by omega⟩ := Fin.ext hs
    rw [heq, bankTrialWindowInteriorSource ring root B hf j]
    rw [(bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).1)).2]
    exact hpair.1
  · by_cases ht : k.val + 1 = j.val + 1
    · have heq :
          (⟨k.val + 1, by omega⟩ :
            Fin ((compileAdvice q).b + 1)) =
          ⟨j.val + 1, by omega⟩ := Fin.ext ht
      rw [heq, bankTrialWindowInteriorResponder ring root hw B hf j]
      rw [(bankTrialLiveClampBitToken q
        ((GrantBankReference.bankLocalReferenceInternalPair q B j).2)).2]
      exact hpair.2
    · rw [bankTrialWindowInteriorFrame ring root hw B hf
        j hj ⟨k.val + 1, by omega⟩ hs ht]

/-- A held interior pair is weak in the provisional LIVE
reference, even if the actual observer changes phase. -/
theorem bankTrialDurationReferenceInteriorHeldWeak {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hp : 0 < bankTrialDurationWorkerTokenMaximum B)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hpair :
      (GrantBankReference.bankLocalReferenceInternalPair q B j).1.tok =
        (GrantBankReference.bankLocalReferenceCell B
          ⟨j.val, by omega⟩).tok ∧
      (GrantBankReference.bankLocalReferenceInternalPair q B j).2.tok =
        (GrantBankReference.bankLocalReferenceCell B
          ⟨j.val + 1, by omega⟩).tok) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val), .live begun⟩ :
        BankTrialLocalState q) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  have hframe := bankTrialDurationInteriorHeldMaximumFrame
    ring root hw B hf j hj hpair
  have hmax :
      bankTrialDurationWorkerTokenMaximum
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) ≤
      bankTrialDurationWorkerTokenMaximum B := by
    rw [hframe]
    exact Nat.le_refl _
  exact bankTrialDurationReferenceWaitWeakOfMaximum
    B (GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val))
    begun hm hp hmax
    (Or.inl (bankTrialWindowInteriorRootModeFrame
      ring root hw B hf j hj))

/-- A held AL/CL source, on the genuine interior edge. -/
theorem bankTrialDurationReferenceInteriorHeldSourceWeak {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hp : 0 < bankTrialDurationWorkerTokenMaximum B)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc :
      (B.fields ⟨j.val, by omega⟩).2.2.1 = .AL ∨
      (B.fields ⟨j.val, by omega⟩).2.2.1 = .CL0 ∨
      (B.fields ⟨j.val, by omega⟩).2.2.1 = .CL1)
    (hdst : (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .E) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val), .live begun⟩ :
        BankTrialLocalState q) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  apply bankTrialDurationReferenceInteriorHeldWeak
    ring root hw B begun hf hm hp j hj
  change
    (bankPair
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by omega⟩)
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val + 1, by omega⟩)
      (j.val + 1) (compileAdvice q).b (compileAdvice q).theta).1.tok =
        (GrantBankReference.bankLocalReferenceCell B
          ⟨j.val, by omega⟩).tok ∧
    (bankPair
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by omega⟩)
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val + 1, by omega⟩)
      (j.val + 1) (compileAdvice q).b (compileAdvice q).theta).2.tok =
        (GrantBankReference.bankLocalReferenceCell B
          ⟨j.val + 1, by omega⟩).tok
  exact bankTrialDurationRawHeldSourceTokens
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by omega⟩)
    (by change 1 ≤ j.val; omega) j.isLt rfl hsrc hdst

/-- A held IR/CR responder, strictly below the top turn. -/
theorem bankTrialDurationReferenceInteriorHeldTargetWeak {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hp : 0 < bankTrialDurationWorkerTokenMaximum B)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hbelow : j.val + 1 < (compileAdvice q).b)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .E)
    (hdst :
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .IR ∨
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .CR0 ∨
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .CR1) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val), .live begun⟩ :
        BankTrialLocalState q) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  apply bankTrialDurationReferenceInteriorHeldWeak
    ring root hw B begun hf hm hp j hj
  change
    (bankPair
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by omega⟩)
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val + 1, by omega⟩)
      (j.val + 1) (compileAdvice q).b (compileAdvice q).theta).1.tok =
        (GrantBankReference.bankLocalReferenceCell B
          ⟨j.val, by omega⟩).tok ∧
    (bankPair
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val, by omega⟩)
      (GrantBankReference.bankLocalReferenceCell B
        ⟨j.val + 1, by omega⟩)
      (j.val + 1) (compileAdvice q).b (compileAdvice q).theta).2.tok =
        (GrantBankReference.bankLocalReferenceCell B
          ⟨j.val + 1, by omega⟩).tok
  exact bankTrialDurationRawHeldTargetTokens
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by omega⟩)
    (by change 1 ≤ j.val; omega) j.isLt rfl
    hbelow hsrc hdst

/-- Last-interior IR/CR top turns use the certified strict
token-maximum drop, rather than a false non-top frame. -/
theorem bankTrialDurationReferenceInteriorTopTurnWeak {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (htop : j.val + 1 = (compileAdvice q).b)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .E)
    (hdst :
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .IR ∨
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .CR0 ∨
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .CR1) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val), .live begun⟩ :
        BankTrialLocalState q) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  have hdrop := bankTrialDurationTopTurnMaximumDrop
    ring root hw B hf hc j hj htop hsrc hdst
  have hp : 0 < bankTrialDurationWorkerTokenMaximum B := by
    omega
  have hmax :
      bankTrialDurationWorkerTokenMaximum
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) ≤
      bankTrialDurationWorkerTokenMaximum B := by
    omega
  exact bankTrialDurationReferenceWaitWeakOfMaximum
    B (GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val))
    begun hm hp hmax
    (Or.inl (bankTrialWindowInteriorRootModeFrame
      ring root hw B hf j hj))

/-- All interior waiting-wave pairs: E/E, selected forward and
return, held forward responder, held return source, and top turn.
Only the original two selected BANK tokens are case-split. -/
theorem bankTrialDurationReferenceInteriorWaitWeak {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hp : 0 < bankTrialDurationWorkerTokenMaximum B)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val), .live begun⟩ :
        BankTrialLocalState q) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  have hsource := bankTrialDurationInteriorSourceWaveToken B j hj
  rcases hm with hi | hcomp
  · rcases hc.iwaitTokens
      ⟨j.val - 1, by have h := j.isLt; omega⟩ hi with
      hleftE | hleftIR | hleftAL
    · have hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .E := by
        rw [hsource]
        exact hleftE
      rcases hc.iwaitTokens j hi with
        hrightE | hrightIR | hrightAL
      · exact bankTrialDurationReferenceInteriorEmptyPairWeak
          ring root hw B begun hf (Or.inl hi) hp j hj hsrc hrightE
      · by_cases htop : j.val + 1 = (compileAdvice q).b
        · exact bankTrialDurationReferenceInteriorTopTurnWeak
            ring root hw B begun hf hc (Or.inl hi)
            j hj htop hsrc (Or.inl hrightIR)
        · have hbelow : j.val + 1 < (compileAdvice q).b := by
            have hlt := j.isLt
            omega
          exact bankTrialDurationReferenceInteriorHeldTargetWeak
            ring root hw B begun hf (Or.inl hi) hp
            j hj hbelow hsrc (Or.inl hrightIR)
      · apply bankTrialDurationReferenceSelectedInteriorWeak
          ring root hw B begun hf hc j hj
        unfold BankTrialDurationSelectedInteriorCondition
        exact Or.inl ⟨hi, Or.inr ⟨hsrc, hrightAL⟩⟩
    · have hleftNot : bankTrialLiveWaveToken B
          ⟨j.val - 1, by have h := j.isLt; omega⟩ ≠ .E := by
        rw [hleftIR]
        intro he
        cases he
      have hrightE := bankTrialDurationInteriorRightEmptyOfLeft
        B hc j hj hleftNot
      have hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .IR := by
        rw [hsource]
        exact hleftIR
      apply bankTrialDurationReferenceSelectedInteriorWeak
        ring root hw B begun hf hc j hj
      unfold BankTrialDurationSelectedInteriorCondition
      exact Or.inl ⟨hi, Or.inl ⟨hsrc, hrightE⟩⟩
    · have hleftNot : bankTrialLiveWaveToken B
          ⟨j.val - 1, by have h := j.isLt; omega⟩ ≠ .E := by
        rw [hleftAL]
        intro he
        cases he
      have hrightE := bankTrialDurationInteriorRightEmptyOfLeft
        B hc j hj hleftNot
      have hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .AL := by
        rw [hsource]
        exact hleftAL
      exact bankTrialDurationReferenceInteriorHeldSourceWeak
        ring root hw B begun hf (Or.inl hi) hp
        j hj (Or.inl hsrc) hrightE
  · rcases hc.cwaitTokens
      ⟨j.val - 1, by have h := j.isLt; omega⟩ hcomp with
      hleftE | hleftComp
    · have hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .E := by
        rw [hsource]
        exact hleftE
      rcases hc.cwaitTokens j hcomp with hrightE | hrightComp
      · exact bankTrialDurationReferenceInteriorEmptyPairWeak
          ring root hw B begun hf (Or.inr hcomp) hp j hj
          hsrc hrightE
      · have hkind :
            (bankTrialLiveWaveToken B j = .CR0 ∨
              bankTrialLiveWaveToken B j = .CR1) ∨
            (bankTrialLiveWaveToken B j = .CL0 ∨
              bankTrialLiveWaveToken B j = .CL1) := by
          unfold BankTrialLiveComparisonToken at hrightComp
          rcases hrightComp with hz | ho | hc0 | hc1
          · exact Or.inl (Or.inl hz)
          · exact Or.inl (Or.inr ho)
          · exact Or.inr (Or.inl hc0)
          · exact Or.inr (Or.inr hc1)
        rcases hkind with hrightCR | hrightCL
        · by_cases htop : j.val + 1 = (compileAdvice q).b
          · exact bankTrialDurationReferenceInteriorTopTurnWeak
              ring root hw B begun hf hc (Or.inr hcomp)
              j hj htop hsrc (Or.inr hrightCR)
          · have hbelow : j.val + 1 < (compileAdvice q).b := by
              have hlt := j.isLt
              omega
            exact bankTrialDurationReferenceInteriorHeldTargetWeak
              ring root hw B begun hf (Or.inr hcomp) hp
              j hj hbelow hsrc (Or.inr hrightCR)
        · apply bankTrialDurationReferenceSelectedInteriorWeak
            ring root hw B begun hf hc j hj
          unfold BankTrialDurationSelectedInteriorCondition
          exact Or.inr ⟨hcomp, Or.inr ⟨hsrc, hrightCL⟩⟩
    · have hkind :
          (bankTrialLiveWaveToken B
              ⟨j.val - 1, by have h := j.isLt; omega⟩ = .CR0 ∨
           bankTrialLiveWaveToken B
              ⟨j.val - 1, by have h := j.isLt; omega⟩ = .CR1) ∨
          (bankTrialLiveWaveToken B
              ⟨j.val - 1, by have h := j.isLt; omega⟩ = .CL0 ∨
           bankTrialLiveWaveToken B
              ⟨j.val - 1, by have h := j.isLt; omega⟩ = .CL1) := by
        unfold BankTrialLiveComparisonToken at hleftComp
        rcases hleftComp with hz | ho | hc0 | hc1
        · exact Or.inl (Or.inl hz)
        · exact Or.inl (Or.inr ho)
        · exact Or.inr (Or.inl hc0)
        · exact Or.inr (Or.inr hc1)
      have hleftNot : bankTrialLiveWaveToken B
          ⟨j.val - 1, by have h := j.isLt; omega⟩ ≠ .E := by
        rcases hkind with hcr | hcl
        · rcases hcr with hz | ho
          · rw [hz]; intro he; cases he
          · rw [ho]; intro he; cases he
        · rcases hcl with hz | ho
          · rw [hz]; intro he; cases he
          · rw [ho]; intro he; cases he
      have hrightE := bankTrialDurationInteriorRightEmptyOfLeft
        B hc j hj hleftNot
      rcases hkind with hleftCR | hleftCL
      · have hsrc :
            (B.fields ⟨j.val, by omega⟩).2.2.1 = .CR0 ∨
            (B.fields ⟨j.val, by omega⟩).2.2.1 = .CR1 := by
          rw [hsource]
          exact hleftCR
        apply bankTrialDurationReferenceSelectedInteriorWeak
          ring root hw B begun hf hc j hj
        unfold BankTrialDurationSelectedInteriorCondition
        exact Or.inr ⟨hcomp, Or.inl ⟨hsrc, hrightE⟩⟩
      · have hsrc :
            (B.fields ⟨j.val, by omega⟩).2.2.1 = .CL0 ∨
            (B.fields ⟨j.val, by omega⟩).2.2.1 = .CL1 := by
          rw [hsource]
          exact hleftCL
        exact bankTrialDurationReferenceInteriorHeldSourceWeak
          ring root hw B begun hf (Or.inr hcomp) hp
          j hj (Or.inr hsrc) hrightE

/-- Nonreturning IWAIT/IR and CWAIT/CR0/CR1 at first digit:
the token is held on root-outgoing; the wait mode is either
unchanged or RESET after lease expiry. -/
theorem bankTrialDurationRawRootNonreturn
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 < b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false)
    (hm : x.mode = .IWAIT ∨ x.mode = .CWAIT)
    (ht : y.tok = .IR ∨ y.tok = .CR0 ∨ y.tok = .CR1) :
    (bankPair x y 1 b theta).2.tok = y.tok ∧
    ((bankPair x y 1 b theta).1.mode = x.mode ∨
      (bankPair x y 1 b theta).1.mode = .RESET) := by
  have hbpos : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  rcases hm with hm | hm
  all_goals rcases ht with ht | ht | ht
  all_goals by_cases hl : 1 < x.lease
  all_goals simp [bankPair, hx, hy, hg, hm, ht,
    hbpos, hbne, hl, isRetTok, isWaitMode,
    Id.run_pure, Id.run_bind]

/-- Nonreturning first-digit IR/CR is weak at the reference,
not merely when the actual next observer remains LIVE. -/
theorem bankTrialDurationReferenceRootNonreturnWeak {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hp : 0 < bankTrialDurationWorkerTokenMaximum B)
    (ht : bankTrialLiveWaveToken B
      ⟨0, bankTrialWindowWidthPos q⟩ = .IR ∨
      bankTrialLiveWaveToken B
      ⟨0, bankTrialWindowWidthPos q⟩ = .CR0 ∨
      bankTrialLiveWaveToken B
      ⟨0, bankTrialWindowWidthPos q⟩ = .CR1) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B root, .live begun⟩ : BankTrialLocalState q) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  have hroot := bankTrialCmpRoot ring root hw B hf
  have hraw := bankTrialDurationRawRootNonreturn
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B ⟨0, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B ⟨1, by have := bankTrialCmpWidth q; omega⟩)
    (by have hwidth := bankTrialCmpWidth q; omega)
    rfl rfl rfl hm ht
  have hframe :
      bankTrialDurationWorkerTokenMaximum
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) =
      bankTrialDurationWorkerTokenMaximum B := by
    apply bankTrialDurationMaximumTokenCongr
    intro k
    by_cases hk : k.val = 0
    · have hindex : k = ⟨0, bankTrialWindowWidthPos q⟩ :=
        Fin.ext hk
      rw [hindex]
      exact ((hroot.2 ⟨0, bankTrialWindowWidthPos q⟩).1 rfl).2.trans
        hraw.1
    · exact ((hroot.2 k).2 hk).2
  have hmode :
      bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) = bankTrialLiveWaveRootMode B ∨
      bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) = .RESET := by
    rcases hraw.2 with hsame | hreset
    · exact Or.inl (hroot.1.trans hsame)
    · exact Or.inr (hroot.1.trans hreset)
  have hmax :
      bankTrialDurationWorkerTokenMaximum
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) ≤
      bankTrialDurationWorkerTokenMaximum B := by
    rw [hframe]
    exact Nat.le_refl _
  exact bankTrialDurationReferenceWaitWeakOfMaximum
    B (GrantBankReference.bankLocalReferenceStepClamped
      ring root B root) begun hm hp hmax hmode

/-- CL1 consumes the comparison return and puts root in RESET
at the old BANK pair, even though actual next observer wins. -/
theorem bankTrialDurationRawRootCLTrueReturn
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 ≤ b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false) (hm : x.mode = .CWAIT)
    (ht : y.tok = .CL1) :
    (bankPair x y 1 b theta).1.mode = .RESET ∧
    (bankPair x y 1 b theta).2.tok = .E := by
  simp [bankPair, hx, hy, hg, hm, ht, hb,
    isRetTok, isWaitMode, Id.run_pure, Id.run_bind]

/-- The IWAIT/AL root return changes to CSTART, whose fixed
rank is strictly below the old first-digit AL token rank. -/
theorem bankTrialDurationReferenceRootALWeak {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT)
    (ht : bankTrialLiveWaveToken B
      ⟨0, bankTrialWindowWidthPos q⟩ = .AL) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B root, .live begun⟩ : BankTrialLocalState q) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  have hnot : bankTrialLiveWaveToken B
      ⟨0, bankTrialWindowWidthPos q⟩ ≠ .E := by
    rw [ht]
    intro h
    cases h
  have hother : ∀ k : Fin (compileAdvice q).b,
      k ≠ ⟨0, bankTrialWindowWidthPos q⟩ →
      bankTrialLiveWaveToken B k = .E := by
    intro k hk
    exact bankTrialInteriorOldWorkerOthersEmpty B hc
      ⟨0, bankTrialWindowWidthPos q⟩ k hnot hk
  have hmax : bankTrialDurationWorkerTokenMaximum B =
      2 * (compileAdvice q).b + 4 := by
    rw [bankTrialDurationMaximumOfSingleToken B
      ⟨0, bankTrialWindowWidthPos q⟩ hother, ht]
    change 2 * (compileAdvice q).b + 3 + 1 =
      2 * (compileAdvice q).b + 4
    omega
  have hpos : 0 < bankTrialDurationWorkerTokenMaximum B := by
    omega
  have hraw := bankTrialDurationRawALRootReturn
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B ⟨0, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B ⟨1, by have := bankTrialCmpWidth q; omega⟩)
    (by have hwidth := bankTrialCmpWidth q; omega)
    rfl rfl rfl hm
    (show (B.fields ⟨1, by have := bankTrialCmpWidth q; omega⟩).2.2.1 = .AL from ht)
  have hmnew :
      bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) = .CSTART :=
    (bankTrialCmpRoot ring root hw B hf).1.trans hraw.1
  have hnew := bankTrialDurationCStartReferenceExact
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B root) begun hmnew
  have hold := bankTrialDurationLeaseAwareWaitWorkerExact
    B begun (Or.inl hm) hpos
  rw [hmax] at hold
  rw [hnew, hold]
  omega

/-- The first-digit CL0 return enters ARMED in the clamped
reference and carries zero lease-aware worker rank. -/
theorem bankTrialDurationReferenceRootCLZeroWeak {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hm : bankTrialLiveWaveRootMode B = .CWAIT)
    (ht : bankTrialLiveWaveToken B
      ⟨0, bankTrialWindowWidthPos q⟩ = .CL0) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B root, .live begun⟩ : BankTrialLocalState q) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  have hraw := bankTrialCmpRawCLZeroRootReturn
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B ⟨0, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B ⟨1, by have := bankTrialCmpWidth q; omega⟩)
    (by have hwidth := bankTrialCmpWidth q; omega)
    rfl rfl rfl hm
    (show (B.fields ⟨1, by have := bankTrialCmpWidth q; omega⟩).2.2.1 = .CL0 from ht)
  have hmnew :
      bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) = .ARMED :=
    (bankTrialCmpRoot ring root hw B hf).1.trans hraw.1
  have hzero := bankTrialDurationLeaseAwareArmedRankZero
    (⟨GrantBankReference.bankLocalReferenceStepClamped
      ring root B root, .live begun⟩ : BankTrialLocalState q) hmnew
  rw [hzero]
  exact Nat.zero_le _

/-- First-digit CL1 has a positive old success event. The
clamped reference has RESET and no protected worker token. -/
theorem bankTrialDurationReferenceRootCLOneWeak {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .CWAIT)
    (ht : bankTrialLiveWaveToken B
      ⟨0, bankTrialWindowWidthPos q⟩ = .CL1) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B root, .live begun⟩ : BankTrialLocalState q) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  have hnot : bankTrialLiveWaveToken B
      ⟨0, bankTrialWindowWidthPos q⟩ ≠ .E := by
    rw [ht]
    intro h
    cases h
  have hraw := bankTrialDurationRawRootCLTrueReturn
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B ⟨0, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B ⟨1, by have := bankTrialCmpWidth q; omega⟩)
    (by have hwidth := bankTrialCmpWidth q; omega)
    rfl rfl rfl hm
    (show (B.fields ⟨1, by have := bankTrialCmpWidth q; omega⟩).2.2.1 = .CL1 from ht)
  have hroot := bankTrialCmpRoot ring root hw B hf
  have hmnew :
      bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) = .RESET :=
    hroot.1.trans hraw.1
  have hnewEmpty : ∀ k : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) k = .E := by
    intro k
    by_cases hk : k.val = 0
    · exact ((hroot.2 k).1 hk).2.trans hraw.2
    · have hne : k ≠ ⟨0, bankTrialWindowWidthPos q⟩ := by
        intro he
        have hv := congrArg Fin.val he
        exact hk hv
      have hprior := bankTrialInteriorOldWorkerOthersEmpty B hc
        ⟨0, bankTrialWindowWidthPos q⟩ k hnot hne
      exact ((hroot.2 k).2 hk).2.trans hprior
  have hzero := bankTrialDurationWorkerMaximumEmptyTokens
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B root) hnewEmpty
  have hbound := bankTrialDurationReferenceResetLeMaximum
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B root) begun hmnew
  rw [hzero] at hbound
  exact Nat.le_trans hbound (Nat.zero_le _)

/-- Root-outgoing weak reference for all IWAIT/CWAIT first
digit cases, including nonreturns and both CL decisions. -/
theorem bankTrialDurationReferenceRootWaitWeak {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT ∨
      bankTrialLiveWaveRootMode B = .CWAIT)
    (hp : 0 < bankTrialDurationWorkerTokenMaximum B) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B root, .live begun⟩ : BankTrialLocalState q) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  rcases hm with hi | hcomp
  · rcases hc.iwaitTokens ⟨0, bankTrialWindowWidthPos q⟩ hi with
      he | hir | hal
    · exact bankTrialDurationReferenceRootEmptyWaitWeak
        ring root hw B begun hf (Or.inl hi) hp he
    · exact bankTrialDurationReferenceRootNonreturnWeak
        ring root hw B begun hf (Or.inl hi) hp (Or.inl hir)
    · exact bankTrialDurationReferenceRootALWeak
        ring root hw B begun hf hc hi hal
  · rcases hc.cwaitTokens ⟨0, bankTrialWindowWidthPos q⟩ hcomp with
      he | ht
    · exact bankTrialDurationReferenceRootEmptyWaitWeak
        ring root hw B begun hf (Or.inr hcomp) hp he
    · unfold BankTrialLiveComparisonToken at ht
      rcases ht with hc0 | hc1 | hcl0 | hcl1
      · exact bankTrialDurationReferenceRootNonreturnWeak
          ring root hw B begun hf (Or.inr hcomp) hp
          (Or.inr (Or.inl hc0))
      · exact bankTrialDurationReferenceRootNonreturnWeak
          ring root hw B begun hf (Or.inr hcomp) hp
          (Or.inr (Or.inr hc1))
      · exact bankTrialDurationReferenceRootCLZeroWeak
          ring root hw B begun hf hcomp hcl0
      · exact bankTrialDurationReferenceRootCLOneWeak
          ring root hw B begun hf hc hcomp hcl1

/-- The CSTART source-root service is reference weak, using
the same authenticated launch as the strict service,
but retaining provisional LIVE on the target reference. -/
theorem bankTrialDurationReferenceCStartRootWeak {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .CSTART) :
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B root, .live begun⟩ : BankTrialLocalState q) ≤
    bankTrialDurationLeaseAwareWorkerRemaining
      (⟨B, .live begun⟩ : BankTrialLocalState q) := by
  have hstage := bankTrialCmpLaunch ring root hw
    (⟨B, .live begun⟩ : BankTrialLocalState q)
    ⟨begun, rfl⟩ hf hm (fun k => hc.headClear k (Or.inr hm))
  obtain ⟨_, _, hnewMode, _, _, htokens⟩ := hstage
  have hbank := bankTrialLocalNextLiveBank ring root root B begun
  have hrmode :
      bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) = .CWAIT := by
    rw [← hbank]
    exact hnewMode
  have hrtokens : ∀ k : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) k =
        if k.val = 0 then
          (if bankTrialCmpValue B 0 then .CR1 else .CR0)
        else .E := by
    intro k
    rw [← hbank]
    exact htokens k
  have hother : ∀ k : Fin (compileAdvice q).b,
      k ≠ ⟨0, bankTrialWindowWidthPos q⟩ →
      bankTrialLiveWaveToken
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) k = .E := by
    intro k hk
    have hne : k.val ≠ 0 := by
      intro he
      exact hk (Fin.ext he)
    rw [hrtokens k, if_neg hne]
  have hmax :
      bankTrialDurationWorkerTokenMaximum
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) + 1 ≤
        2 * (compileAdvice q).b + 2 := by
    rw [bankTrialDurationMaximumOfSingleToken
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root)
      ⟨0, bankTrialWindowWidthPos q⟩ hother,
      hrtokens ⟨0, bankTrialWindowWidthPos q⟩]
    change
      bankTrialDurationWorkerTokenRank (compileAdvice q).b 1
        (if bankTrialCmpValue B 0 then .CR1 else .CR0) + 1 ≤
      2 * (compileAdvice q).b + 2
    cases hb : bankTrialCmpValue B 0 <;>
      simp [hb, bankTrialDurationWorkerTokenRank] <;> omega
  have href := bankTrialDurationLeaseAwareWaitWorkerLeMaximum
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B root) begun (Or.inr hrmode)
  have hold := bankTrialDurationCStartReferenceExact B begun hm
  omega

/-- Exhaust the original physical scheduler alphabet with the
proved source/top/incoming/outside geometry partition. -/
theorem bankTrialDurationClassOneReferenceWeakRowsHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    BankTrialDurationClassOneReferenceWeakRows (q := q) ring root := by
  intro S hclean B begun hreach hclass e
  obtain ⟨word, hword⟩ := id hreach
  have hf := bankTrialProbabilityCleanLiveUnlatched
    ring root S hclean word B begun hword
  have hinv := bankTrialDurationReachableOrphanInv
    ring root hw hpositive hK S hclean
    (⟨B, .live begun⟩ : BankTrialLocalState q) hreach
  have hc : BankTrialLiveWaveCertificate q B :=
    hinv.locked.1 begun rfl
  have hcases := bankTrialDurationReachableClassOneCStartOrWait
    ring root hw hpositive hK S hclean B begun hreach hclass
  rcases Counter.resetTrialEdgeGeometry (q := q)
      ring root e with hsource | hin | hout
  · obtain ⟨j, hj, he⟩ := hsource
    by_cases htop : j = (compileAdvice q).b
    · subst j
      rw [he]
      rcases hcases with hstart | hwait
      · exact bankTrialDurationReferenceCStartTopWeak
          ring root hw B begun hf hstart
      · exact bankTrialDurationReferenceTopWaitWeak
          ring root hw B begun hf hwait.1 hwait.2
    · by_cases hzero : j = 0
      · subst j
        have heRoot : e = root := by
          simpa only [Counter.site] using he
        rw [heRoot]
        rcases hcases with hstart | hwait
        · exact bankTrialDurationReferenceCStartRootWeak
            ring root hw B begun hf hc hstart
        · exact bankTrialDurationReferenceRootWaitWeak
            ring root hw B begun hf hc hwait.1 hwait.2
      · have hjfin : j < (compileAdvice q).b := by omega
        have hjpos : 0 < j := by omega
        rw [he]
        rcases hcases with hstart | hwait
        · exact bankTrialDurationReferenceCStartInteriorWeak
            ring root hw B begun hf hstart
            ⟨j, hjfin⟩ hjpos
        · exact bankTrialDurationReferenceInteriorWaitWeak
            ring root hw B begun hf hc hwait.1 hwait.2
            ⟨j, hjfin⟩ hjpos
  · have hne : e ≠ root := by
      intro he
      have hself : ring.rightNeighbor root = root := by
        simpa only [he] using hin
      have hs : Counter.site ring root 1 =
          Counter.site ring root 0 := by
        change ring.rightNeighbor root = root
        exact hself
      have hv := bankTrialWindowSitesDistinct ring root hw
        1 0
        (by have hb := bankTrialCmpWidth q; omega)
        (by omega) hs
      omega
    rcases hcases with hstart | hwait
    · exact bankTrialDurationReferenceCStartIncomingWeak
        ring root e hw B begun hf hstart hne hin
    · exact bankTrialDurationReferenceIncomingWaitWeak
        ring root e hw hin B begun hf hwait.1 hwait.2
  · have houtside : ¬ Counter.Support q ring root e := by
      intro hs
      rcases hs with hinc | ⟨j, hj, he⟩
      · exact (hout 0 (by omega)).2 hinc
      · exact (hout j hj).1 he
    exact bankTrialDurationReferenceOutsideWeak
      ring root e B begun houtside

/-- The C.6 worker budget is the existing conditional assembly
applied to the now-established class-one coverage theorem
and the all-edge reference weakness proof. -/
theorem bankTrialDurationWorkerBudgetHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    BankTrialDurationWorkerBudget (q := q) ring root := by
  exact bankTrialDurationWorkerBudgetOfTwoClassOneGates
    ring root hsmall hw hpositive hK
    (bankTrialDurationClassOneReferenceWeakRowsHolds
      ring root hw hpositive hK)
    (bankTrialDurationClassOneServiceCoverageHolds
      ring root hw hpositive hK)

end L3

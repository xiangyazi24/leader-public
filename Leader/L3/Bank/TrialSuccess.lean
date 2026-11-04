import Leader.L3.Bank.TrialCompletedHeadRows
import Leader.L3.Bank.TrialRecovery

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
Original-clock Markov from unconditional C.6, plus the
precise inclusion prerequisite for a GLOBAL final-horizon pending
mask. There is no asserted K-round assembly.

Pending at an intermediate prefix and pending at the FINAL horizon
are different events: the former may subsequently finish in WON.
The recursive first-origin scanner may also report none at a
terminal cut when it is incorrectly invoked as a new stage.
-/

/-- Original n-edge schedule sums commute with multiplication
by a fixed, opaque natural number. -/
theorem bankTrialSuccessScheduleSumScale (n T c : Nat)
    (f : List (Fin n) → Nat) :
    Prob.scheduleSum n T (fun w => c * f w) =
      c * Prob.scheduleSum n T f := by
  induction T generalizing f with
  | zero =>
      rw [bankTrialProbabilityScheduleSumZero,
        bankTrialProbabilityScheduleSumZero]
  | succ t ih =>
      rw [bankTrialProbabilityScheduleSumFirst,
        bankTrialProbabilityScheduleSumFirst]
      rw [← ofFn_sum_mul_left]
      apply ofFn_sum_eq
      intro e
      exact ih (fun w => f (e :: w))

/-- The scheduleSum alphabet counts only words of exact length T.
This is proved directly by induction on the first letter. -/
theorem bankTrialSuccessScheduleSumLength (n T : Nat)
    (f : List (Fin n) → Nat) :
    Prob.scheduleSum n T (fun w => w.length * f w) =
      T * Prob.scheduleSum n T f := by
  induction T generalizing f with
  | zero =>
      rw [bankTrialProbabilityScheduleSumZero,
        bankTrialProbabilityScheduleSumZero]
      simp
  | succ t ih =>
      rw [bankTrialProbabilityScheduleSumFirst,
        bankTrialProbabilityScheduleSumFirst]
      rw [← ofFn_sum_mul_left]
      apply ofFn_sum_eq
      intro e
      calc
        Prob.scheduleSum n t
            (fun w => (e :: w).length * f (e :: w)) =
          Prob.scheduleSum n t
            (fun w => w.length * f (e :: w) + f (e :: w)) := by
              apply congrArg (Prob.scheduleSum n t)
              funext w
              simp only [List.length_cons, Nat.succ_eq_add_one,
                Nat.add_mul, Nat.one_mul]
        _ = Prob.scheduleSum n t
              (fun w => w.length * f (e :: w)) +
            Prob.scheduleSum n t (fun w => f (e :: w)) :=
          bankTrialC5ScheduleSumAdd t _ _
        _ = t * Prob.scheduleSum n t (fun w => f (e :: w)) +
            Prob.scheduleSum n t (fun w => f (e :: w)) := by
              rw [ih (fun w => f (e :: w))]
        _ = (t + 1) *
            Prob.scheduleSum n t (fun w => f (e :: w)) := by
              rw [Nat.add_mul, Nat.one_mul]

/-- If the endpoint is nonterminal, every earlier state is
nonterminal, since WON and LOST are absorbing. The stopped cost
therefore charges every physical scheduler letter. -/
theorem bankTrialSuccessActiveWordCost
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (w : List (Fin n)) (x : BankTrialLocalState q),
      ¬ bankTrialLocalTerminal
        (bankTrialLocalRun ring root w x) →
      w.length ≤ costWord (bankTrialLocalNext ring root)
        bankTrialLocalTerminal x w := by
  intro w
  induction w with
  | nil =>
      intro x _
      change 0 ≤ costWord (bankTrialLocalNext ring root)
        bankTrialLocalTerminal x []
      exact Nat.zero_le _
  | cons e tail ih =>
      intro x hactive
      have hnot : ¬ bankTrialLocalTerminal x := by
        intro ht
        have heq := bankTrialLocalRunTerminalAbsorbs
          ring root (e :: tail) x ht
        apply hactive
        rw [heq]
        exact ht
      have htail :
          ¬ bankTrialLocalTerminal
            (bankTrialLocalRun ring root tail
              (bankTrialLocalNext ring root x e)) := hactive
      have hcost :
          costWord (bankTrialLocalNext ring root)
              bankTrialLocalTerminal x (e :: tail) =
            1 + costWord (bankTrialLocalNext ring root)
              bankTrialLocalTerminal
              (bankTrialLocalNext ring root x e) tail := by
                simp only [costWord,
                  K2FiniteSafeEliminationExpected.rawCost,
                  if_neg hnot]
      have hle := ih (bankTrialLocalNext ring root x e) htail
      rw [hcost]
      simp only [List.length_cons]
      omega

/-- Raw original-clock Markov inequality, for every T (including
T=0), before applying the C.6 bound. -/
theorem bankTrialSuccessMarkovFromCost
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) :
    T * bankTrialDurationActiveMass ring root S T ≤
      costNumerator (bankTrialLocalNext ring root)
        bankTrialLocalTerminal (bankTrialLocalStart S) T := by
  have hword (w : List (Fin n)) :
      w.length *
          (if bankTrialLocalTerminal
            (bankTrialLocalRun ring root w (bankTrialLocalStart S))
           then 0 else 1) ≤
        costWord (bankTrialLocalNext ring root)
          bankTrialLocalTerminal (bankTrialLocalStart S) w := by
    by_cases ht :
        bankTrialLocalTerminal
          (bankTrialLocalRun ring root w (bankTrialLocalStart S))
    · simp only [if_pos ht, Nat.mul_zero]
      exact Nat.zero_le _
    · simp only [if_neg ht, Nat.mul_one]
      exact bankTrialSuccessActiveWordCost
        ring root w (bankTrialLocalStart S) ht
  have hsum :
      Prob.scheduleSum n T (fun w =>
        w.length *
          (if bankTrialLocalTerminal
            (bankTrialLocalRun ring root w (bankTrialLocalStart S))
           then 0 else 1)) ≤
        costNumerator (bankTrialLocalNext ring root)
          bankTrialLocalTerminal (bankTrialLocalStart S) T := by
    change Prob.scheduleSum n T (fun w =>
        w.length *
          (if bankTrialLocalTerminal
            (bankTrialLocalRun ring root w (bankTrialLocalStart S))
           then 0 else 1)) ≤
      Prob.scheduleSum n T
        (costWord (bankTrialLocalNext ring root)
          bankTrialLocalTerminal (bankTrialLocalStart S))
    exact bankTrialProbabilityScheduleSumMono n T _ _ hword
  rw [bankTrialSuccessScheduleSumLength] at hsum
  change T * bankTrialDurationActiveMass ring root S T ≤
    costNumerator (bankTrialLocalNext ring root)
      bankTrialLocalTerminal (bankTrialLocalStart S) T at hsum
  exact hsum

/-- C.6 gives B = (8b+12)n, with no additional stage charge. -/
theorem bankTrialSuccessMarkovOfDurationBound
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) (T : Nat) :
    T * bankTrialDurationActiveMass ring root S T ≤
      n ^ T * ((8 * (compileAdvice q).b + 12) * n) := by
  exact Nat.le_trans
    (bankTrialSuccessMarkovFromCost ring root S T)
    (bankTrialDurationC6Holds ring root hn hsmall hw
      hpositive hwidth S hclean T)

/-- Exact global pending-event inclusion needed before C.6 can be
charged. This lemma does not assert that the local stage scanner
satisfies that inclusion. -/
theorem bankTrialSuccessPendingMaskLeActive
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (T : Nat) (pending : List (Fin n) → Bool)
    (hfinal : ∀ w, pending w = true →
      ¬ bankTrialLocalTerminal
        (bankTrialLocalRun ring root w (bankTrialLocalStart S))) :
    Prob.scheduleSum n T (fun w => Prob.indicator (pending w)) ≤
      bankTrialDurationActiveMass ring root S T := by
  change Prob.scheduleSum n T
      (fun w => Prob.indicator (pending w)) ≤
    Prob.scheduleSum n T (fun w =>
      if bankTrialLocalTerminal
        (bankTrialLocalRun ring root w (bankTrialLocalStart S))
      then 0 else 1)
  apply bankTrialProbabilityScheduleSumMono n T
  intro w
  cases hp : pending w with
  | false =>
      simp [Prob.indicator, hp]
  | true =>
      have ha := hfinal w hp
      simp [Prob.indicator, hp, ha]

/-- The single global ACTIVE set is enough once a given FINAL
pending mask is shown to lie in it. It does not bound the sum of
unrelated stage-local pending masses without an additional
stopped-prefix disjointness theorem. -/
theorem bankTrialSuccessPendingMaskMarkov
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (T : Nat) (pending : List (Fin n) → Bool)
    (hfinal : ∀ w, pending w = true →
      ¬ bankTrialLocalTerminal
        (bankTrialLocalRun ring root w (bankTrialLocalStart S))) :
    T * Prob.scheduleSum n T (fun w =>
        Prob.indicator (pending w)) ≤
      n ^ T * ((8 * (compileAdvice q).b + 12) * n) := by
  calc
    T * Prob.scheduleSum n T (fun w =>
        Prob.indicator (pending w)) ≤
      T * bankTrialDurationActiveMass ring root S T :=
        Nat.mul_le_mul_left T
          (bankTrialSuccessPendingMaskLeActive
            ring root S T pending hfinal)
    _ ≤ n ^ T * ((8 * (compileAdvice q).b + 12) * n) :=
      bankTrialSuccessMarkovOfDurationBound
        ring root hn hsmall hw hpositive hwidth S hclean T

/-- On an EMPTY suffix the first-origin CSTART scanner returns none
for every state, including a terminal state. The scanner alone does
not certify any still-live stage. -/
theorem bankTrialSuccessEmptyCStartScannerPending
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) :
    bankTrialC5CStartPendingBool ring root S x [] = true := by
  simp [bankTrialC5CStartPendingBool,
    bankTrialC5PostHeadFirstExit]

/-- Literal CLEAN-origin winning scheduler:
  pre = [], the first ARMED stage is pending at that instant;
  full = bankTrialC5Rounds ring root b bankTrialC5Trailing K,
  and its END state is WON.

Thus "pending at SOME intermediate prefix" cannot be bounded by
the single set of nonterminal states at full horizon T.
This does not refute a correctly defined FINAL-horizon pending event.
-/
theorem bankTrialSuccessIntermediatePendingCanFinishWon
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsmall : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S) :
    bankTrialC5PendingBeforeBool ring root S
      (bankTrialLocalStart S) [] = true ∧
    (bankTrialLocalRun ring root
      (bankTrialC5Rounds ring root (compileAdvice q).b
        bankTrialC5Trailing (compileAdvice q).K)
      (bankTrialLocalStart S)).phase = .won := by
  have hstart :
      bankTrialC5PendingBeforeBool ring root S
        (bankTrialLocalStart S) [] = true := by
    simp [bankTrialC5PendingBeforeBool,
      bankTrialProbabilityFirstIncidentOrientation,
      bankTrialC5StageClassBool, bankTrialC5StageClass,
      bankTrialC5PreHeadFirstExit]
  have hwon :
      (bankTrialC5CleanRun ring root S
        (bankTrialC5Rounds ring root (compileAdvice q).b
          bankTrialC5Trailing (compileAdvice q).K)).phase = .won :=
    (bankTrialProbabilityC5DesignatedCompletion
      ring root S hsmall hlarge hclean).2
  exact ⟨hstart, hwon⟩

/-- Literal CLEAN-reachable terminal example for the UNRESTRICTED
scanner: at the designated WON state, its empty suffix [] is still
reported pending. It is NOT a valid LIVE/CSTART stage start.
-/
theorem bankTrialSuccessReachableWonScannerPending
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsmall : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S) :
    ∃ pre : List (Fin n),
      (bankTrialLocalRun ring root pre
        (bankTrialLocalStart S)).phase = .won ∧
      bankTrialC5CStartPendingBool ring root S
        (bankTrialLocalRun ring root pre
          (bankTrialLocalStart S)) [] = true := by
  refine ⟨bankTrialC5Rounds ring root (compileAdvice q).b
    bankTrialC5Trailing (compileAdvice q).K, ?_, ?_⟩
  · exact (bankTrialProbabilityC5DesignatedCompletion
      ring root S hsmall hlarge hclean).2
  · exact bankTrialSuccessEmptyCStartScannerPending ring root S _

end L3

namespace L3

open Classical

/-- A FINAL-horizon mask: the entire scheduler word ends in a
nonterminal local state. No intermediate-prefix scanner is used. -/
noncomputable def bankTrialSuccessFinalNonterminalBool
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (w : List (Fin n)) : Bool :=
  decide (¬ bankTrialLocalTerminal
    (bankTrialLocalRun ring root w (bankTrialLocalStart S)))

/-- Part (i): the final-horizon nonterminal event is charged ONCE
to the original-clock C.6 stopped cost, for every horizon T.
The hfinal premise of the existing pending-mask lemma is true
by definition, not by an intermediate-stage scanner argument. -/
theorem bankTrialSuccessFinalNonterminalMarkov
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) (T : Nat) :
    T * Prob.scheduleSum n T (fun w =>
      Prob.indicator
        (bankTrialSuccessFinalNonterminalBool ring root S w)) ≤
      n ^ T * ((8 * (compileAdvice q).b + 12) * n) := by
  have hfinal : ∀ w : List (Fin n),
      bankTrialSuccessFinalNonterminalBool ring root S w = true →
      ¬ bankTrialLocalTerminal
        (bankTrialLocalRun ring root w (bankTrialLocalStart S)) := by
    intro w hp
    change decide (¬ bankTrialLocalTerminal
      (bankTrialLocalRun ring root w (bankTrialLocalStart S))) =
        true at hp
    exact of_decide_eq_true hp
  exact bankTrialSuccessPendingMaskMarkov
    ring root hn hsmall hw hpositive hwidth S hclean T
    (bankTrialSuccessFinalNonterminalBool ring root S) hfinal

/-- Exact requested UNION INCLUSION at the endpoint of w.
The second event is terminal at the SAME final horizon, but fails
the literal completed-head word predicate. These alternatives are
disjoint; no assertion about their respective masses is made here. -/
theorem bankTrialSuccessFinalComplementUnion
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (w : List (Fin n))
    (hbad : ¬ bankTrialProbabilityC5CompletedHeadWord
      ring root S w) :
    (¬ bankTrialLocalTerminal
      (bankTrialLocalRun ring root w (bankTrialLocalStart S))) ∨
    (bankTrialLocalTerminal
      (bankTrialLocalRun ring root w (bankTrialLocalStart S)) ∧
      ¬ bankTrialProbabilityC5CompletedHeadWord ring root S w) := by
  by_cases ht : bankTrialLocalTerminal
      (bankTrialLocalRun ring root w (bankTrialLocalStart S))
  · exact Or.inr ⟨ht, hbad⟩
  · exact Or.inl ht

/-- Pointwise indicator form of the union inclusion. This is
an inequality (not an unconditional equality): the completed-head
predicate may include a LIVE ARMED endpoint without soundness. -/
theorem bankTrialSuccessFinalComplementIndicatorLe
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (w : List (Fin n)) :
    (if bankTrialProbabilityC5CompletedHeadWord ring root S w
      then 0 else 1) ≤
      Prob.indicator
        (bankTrialSuccessFinalNonterminalBool ring root S w) +
      (if bankTrialLocalTerminal
          (bankTrialLocalRun ring root w (bankTrialLocalStart S)) ∧
          ¬ bankTrialProbabilityC5CompletedHeadWord ring root S w
        then 1 else 0) := by
  by_cases hc : bankTrialProbabilityC5CompletedHeadWord ring root S w
  · simp only [if_pos hc]
    exact Nat.zero_le _
  · by_cases ht : bankTrialLocalTerminal
        (bankTrialLocalRun ring root w (bankTrialLocalStart S))
    · simp [bankTrialSuccessFinalNonterminalBool,
        Prob.indicator, hc, ht]
    · simp [bankTrialSuccessFinalNonterminalBool,
        Prob.indicator, hc, ht]

/-- The exact event split, lifted to numerator masses on the ONE
original length-T scheduler alphabet. The terminal-failure mass
is deliberately left for the separate C.5 stage argument. -/
theorem bankTrialSuccessFinalComplementMassSplit
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) :
    Prob.scheduleSum n T (fun w =>
      if bankTrialProbabilityC5CompletedHeadWord ring root S w
      then 0 else 1) ≤
      Prob.scheduleSum n T (fun w =>
        Prob.indicator
          (bankTrialSuccessFinalNonterminalBool ring root S w)) +
      Prob.scheduleSum n T (fun w =>
        if bankTrialLocalTerminal
            (bankTrialLocalRun ring root w (bankTrialLocalStart S)) ∧
            ¬ bankTrialProbabilityC5CompletedHeadWord ring root S w
        then 1 else 0) := by
  calc
    Prob.scheduleSum n T (fun w =>
        if bankTrialProbabilityC5CompletedHeadWord ring root S w
        then 0 else 1) ≤
      Prob.scheduleSum n T (fun w =>
        Prob.indicator
          (bankTrialSuccessFinalNonterminalBool ring root S w) +
        (if bankTrialLocalTerminal
            (bankTrialLocalRun ring root w (bankTrialLocalStart S)) ∧
            ¬ bankTrialProbabilityC5CompletedHeadWord ring root S w
          then 1 else 0)) :=
        bankTrialProbabilityScheduleSumMono n T _ _
          (bankTrialSuccessFinalComplementIndicatorLe ring root S)
    _ = _ := bankTrialC5ScheduleSumAdd T _ _

/-- C.6 pays only the final nonterminal part. The remaining
terminal-and-incomplete term is explicitly exposed and UNBOUNDED;
in particular this theorem does not claim the full hforward estimate.
No worker-kernel field is consumed by this split. -/
theorem bankTrialSuccessFinalComplementMarkovSplit
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) (T : Nat) :
    T * Prob.scheduleSum n T (fun w =>
      if bankTrialProbabilityC5CompletedHeadWord ring root S w
      then 0 else 1) ≤
      n ^ T * ((8 * (compileAdvice q).b + 12) * n) +
      T * Prob.scheduleSum n T (fun w =>
        if bankTrialLocalTerminal
            (bankTrialLocalRun ring root w (bankTrialLocalStart S)) ∧
            ¬ bankTrialProbabilityC5CompletedHeadWord ring root S w
        then 1 else 0) := by
  calc
    T * Prob.scheduleSum n T (fun w =>
        if bankTrialProbabilityC5CompletedHeadWord ring root S w
        then 0 else 1) ≤
      T * (Prob.scheduleSum n T (fun w =>
        Prob.indicator
          (bankTrialSuccessFinalNonterminalBool ring root S w)) +
        Prob.scheduleSum n T (fun w =>
          if bankTrialLocalTerminal
              (bankTrialLocalRun ring root w (bankTrialLocalStart S)) ∧
              ¬ bankTrialProbabilityC5CompletedHeadWord ring root S w
          then 1 else 0)) :=
        Nat.mul_le_mul_left T
          (bankTrialSuccessFinalComplementMassSplit ring root S T)
    _ = T * Prob.scheduleSum n T (fun w =>
          Prob.indicator
            (bankTrialSuccessFinalNonterminalBool ring root S w)) +
        T * Prob.scheduleSum n T (fun w =>
          if bankTrialLocalTerminal
              (bankTrialLocalRun ring root w (bankTrialLocalStart S)) ∧
              ¬ bankTrialProbabilityC5CompletedHeadWord ring root S w
          then 1 else 0) := by
            rw [Nat.mul_add]
    _ ≤ n ^ T * ((8 * (compileAdvice q).b + 12) * n) +
        T * Prob.scheduleSum n T (fun w =>
          if bankTrialLocalTerminal
              (bankTrialLocalRun ring root w (bankTrialLocalStart S)) ∧
              ¬ bankTrialProbabilityC5CompletedHeadWord ring root S w
          then 1 else 0) :=
        Nat.add_le_add_right
          (bankTrialSuccessFinalNonterminalMarkov
            ring root hn hsmall hw hpositive hwidth S hclean T) _

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-!
Fixed-horizon, stage-indexed pending accounting.

These are ORIGINAL n-edge masses. A raw stage cut is evaluated on
the WHOLE residual suffix by Prob.firstStoppedSuffixWord, not at
the instant of the cut. The required connection of the actual
stage-j cuts to the live endpoint and its stage ordinal is exposed
as an explicit bridge, never inferred from scanner = none.
-/

/-- A core-only finite sum over ordinal positions 0,...,K-1. -/
def bankTrialSuccessStageIndexSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => bankTrialSuccessStageIndexSum f k + f k

theorem bankTrialSuccessStageIndexSumMono
    (f g : Nat → Nat) (h : ∀ j, f j ≤ g j) :
    ∀ K, bankTrialSuccessStageIndexSum f K ≤
      bankTrialSuccessStageIndexSum g K := by
  intro K
  induction K with
  | zero => exact Nat.le_refl _
  | succ k ih =>
      change bankTrialSuccessStageIndexSum f k + f k ≤
        bankTrialSuccessStageIndexSum g k + g k
      exact Nat.add_le_add ih (h k)

theorem bankTrialSuccessStageIndexSumZero (K : Nat) :
    bankTrialSuccessStageIndexSum (fun _ => 0) K = 0 := by
  induction K with
  | zero => rfl
  | succ k ih =>
      change bankTrialSuccessStageIndexSum (fun _ => 0) k + 0 = 0
      rw [ih]

/-- No Finset: a fixed natural index occurs at most once among
the K successive natural stage indices. -/
theorem bankTrialSuccessStageIndexSumDelta (z : Nat) :
    ∀ K, bankTrialSuccessStageIndexSum
      (fun j => if j = z then 1 else 0) K =
      (if z < K then 1 else 0) := by
  intro K
  induction K with
  | zero =>
      simp [bankTrialSuccessStageIndexSum]
  | succ k ih =>
      change bankTrialSuccessStageIndexSum
          (fun j => if j = z then 1 else 0) k +
          (if k = z then 1 else 0) =
        (if z < k + 1 then 1 else 0)
      rw [ih]
      by_cases hlt : z < k
      · have hne : k ≠ z := by omega
        have hs : z < k + 1 := by omega
        simp [hlt, hne, hs]
      · by_cases heq : k = z
        · have hs : z < k + 1 := by omega
          simp [hlt, heq, hs]
        · have hs : ¬ z < k + 1 := by omega
          simp [hlt, heq, hs]

/-- Pure Boolean endpoint-accounting lemma. If every marked stage
has a single common final ordinal and is final-active, the sum of
the marks is bounded by the ONE final-active indicator. -/
theorem bankTrialSuccessStageIndexSumIndicatorBound
    (active : Bool) (ordinal K : Nat)
    (stage : Nat → Bool)
    (hstage : ∀ j, stage j = true →
      active = true ∧ j = ordinal) :
    bankTrialSuccessStageIndexSum
        (fun j => Prob.indicator (stage j)) K ≤
      Prob.indicator active := by
  cases ha : active with
  | false =>
      have hfalse (j : Nat) : stage j = false := by
        cases hj : stage j with
        | false => rfl
        | true =>
            have hh := (hstage j hj).1
            rw [ha] at hh
            cases hh
      have hp (j : Nat) :
          Prob.indicator (stage j) ≤ 0 := by
        rw [hfalse j]
        exact Nat.zero_le _
      have hs := bankTrialSuccessStageIndexSumMono
        (fun j => Prob.indicator (stage j))
        (fun _ => 0) hp K
      rw [bankTrialSuccessStageIndexSumZero] at hs
      change bankTrialSuccessStageIndexSum
        (fun j => Prob.indicator (stage j)) K ≤ 0
      exact hs
  | true =>
      have hp (j : Nat) :
          Prob.indicator (stage j) ≤
            (if j = ordinal then 1 else 0) := by
        by_cases hj : j = ordinal
        · rw [if_pos hj]
          cases he : stage j <;> simp [Prob.indicator, he]
        · have hf : stage j = false := by
            cases he : stage j with
            | false => rfl
            | true => exact False.elim (hj (hstage j he).2)
          rw [if_neg hj, hf]
          exact Nat.zero_le _
      have hs := bankTrialSuccessStageIndexSumMono
        (fun j => Prob.indicator (stage j))
        (fun j => if j = ordinal then 1 else 0) hp K
      rw [bankTrialSuccessStageIndexSumDelta] at hs
      have hb : (if ordinal < K then 1 else 0) ≤ 1 := by
        split <;> omega
      change bankTrialSuccessStageIndexSum
        (fun j => Prob.indicator (stage j)) K ≤ 1
      exact Nat.le_trans hs hb

/-- Interchange the finite stage-index sum and the original n-edge
schedule sum. This is a finite algebraic identity, not independence. -/
theorem bankTrialSuccessStageIndexSumSchedule
    (n T K : Nat) (f : Nat → List (Fin n) → Nat) :
    bankTrialSuccessStageIndexSum
      (fun j => Prob.scheduleSum n T (f j)) K =
    Prob.scheduleSum n T (fun w =>
      bankTrialSuccessStageIndexSum (fun j => f j w) K) := by
  induction K with
  | zero =>
      change 0 = Prob.scheduleSum n T (fun _ => 0)
      simpa only [Nat.mul_zero] using
        (bankTrialProbabilityScheduleSumConst n T 0).symm
  | succ k ih =>
      change bankTrialSuccessStageIndexSum
          (fun j => Prob.scheduleSum n T (f j)) k +
          Prob.scheduleSum n T (f k) =
        Prob.scheduleSum n T (fun w =>
          bankTrialSuccessStageIndexSum (fun j => f j w) k +
            f k w)
      rw [bankTrialC5ScheduleSumAdd, ih]

/-- A candidate endpoint ordinal for consecutive ARMED stages:
at ARMED the next HEAD has not happened, and at non-ARMED it has.
The assertion that every actual cut has this ordinal is NOT proved
by the existing first-return scanner. -/
noncomputable def bankTrialSuccessPendingOrdinal
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (w : List (Fin n)) : Nat :=
  if bankTrialLiveWaveRootMode
      (bankTrialLocalRun ring root w (bankTrialLocalStart S)).bank =
        .ARMED then
    bankTrialLiveHeadCount ring root w (bankTrialLocalStart S)
  else
    bankTrialLiveHeadCount ring root w (bankTrialLocalStart S) - 1

/-- The RAW stage-j pending event from an actual first stopping cut.
The cuts argument must eventually be supplied by the concrete
chronological stage-j first-return construction.
For CSTART use its first-origin pending scanner; otherwise take
the two disjoint ARMED pending classes BEFORE and AFTER first HEAD.
These are exactly the Boolean integrands of the installed stage
masses, evaluated on the residual ORIGINAL scheduler suffix. -/
noncomputable def bankTrialSuccessActualCutPendingRawBool
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (cuts : Nat → List (Fin n) → BankTrialLocalState q → Bool)
    (cstart : Nat → Bool) (j T : Nat) (w : List (Fin n)) : Bool :=
  Prob.firstStoppedSuffixWord (bankTrialLocalNext ring root)
    (cuts j)
    (fun x _ suffix =>
      if cstart j = true then
        bankTrialC5CStartPendingBool ring root S x suffix
      else
        bankTrialC5PendingBeforeBool ring root S x suffix ||
        bankTrialC5PendingAfterBool ring root S x suffix)
    T [] (bankTrialLocalStart S) w

/-- This guarded event is unambiguously FINAL-horizon pending.
The final-active and ordinal guards are explicit. Removing them
requires a separately proved actual-cut scanner bridge. -/
noncomputable def bankTrialSuccessActualCutPendingFinalBool
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (cuts : Nat → List (Fin n) → BankTrialLocalState q → Bool)
    (cstart : Nat → Bool) (j T : Nat) (w : List (Fin n)) : Bool :=
  if bankTrialSuccessFinalNonterminalBool ring root S w = true then
    if bankTrialSuccessPendingOrdinal ring root S w = j then
      bankTrialSuccessActualCutPendingRawBool
        ring root S cuts cstart j T w
    else false
  else false

theorem bankTrialSuccessActualCutPendingFinalSound
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (cuts : Nat → List (Fin n) → BankTrialLocalState q → Bool)
    (cstart : Nat → Bool) (j T : Nat) (w : List (Fin n))
    (hp : bankTrialSuccessActualCutPendingFinalBool
      ring root S cuts cstart j T w = true) :
    bankTrialSuccessFinalNonterminalBool ring root S w = true ∧
      j = bankTrialSuccessPendingOrdinal ring root S w := by
  by_cases ha :
      bankTrialSuccessFinalNonterminalBool ring root S w = true
  · by_cases hj :
        bankTrialSuccessPendingOrdinal ring root S w = j
    · exact ⟨ha, hj.symm⟩
    · have hf : bankTrialSuccessActualCutPendingFinalBool
          ring root S cuts cstart j T w = false := by
        simp only [bankTrialSuccessActualCutPendingFinalBool,
          if_pos ha, if_neg hj]
      rw [hf] at hp
      cases hp
  · have hf : bankTrialSuccessActualCutPendingFinalBool
        ring root S cuts cstart j T w = false := by
      simp only [bankTrialSuccessActualCutPendingFinalBool,
        if_neg ha]
    rw [hf] at hp
    cases hp

/-- Distinct stage indices cannot be pending simultaneously at
the final cut. No worker-kernel field is needed for this guarded
endpoint claim. -/
theorem bankTrialSuccessActualCutPendingFinalDisjoint
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (cuts : Nat → List (Fin n) → BankTrialLocalState q → Bool)
    (cstart : Nat → Bool) (i j T : Nat) (w : List (Fin n))
    (hne : i ≠ j)
    (hi : bankTrialSuccessActualCutPendingFinalBool
      ring root S cuts cstart i T w = true)
    (hj : bankTrialSuccessActualCutPendingFinalBool
      ring root S cuts cstart j T w = true) : False := by
  have he := (bankTrialSuccessActualCutPendingFinalSound
    ring root S cuts cstart i T w hi).2
  have hf := (bankTrialSuccessActualCutPendingFinalSound
    ring root S cuts cstart j T w hj).2
  exact hne (he.trans hf.symm)

/-- Key finite-horizon mass lemma: any stage family whose TRUE
events imply final nonterminal and one unambiguous final ordinal
has total mass at most the one final nonterminal mass. The bridge
is a *hypothesis* here, not a consequence of a scanner returning
none. -/
theorem bankTrialSuccessIndexedPendingMassBoundOfBridge
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (T K : Nat)
    (stage : Nat → List (Fin n) → Bool)
    (ordinal : List (Fin n) → Nat)
    (hbridge : ∀ j w, stage j w = true →
      bankTrialSuccessFinalNonterminalBool ring root S w = true ∧
        j = ordinal w) :
    bankTrialSuccessStageIndexSum
        (fun j => Prob.scheduleSum n T (fun w =>
          Prob.indicator (stage j w))) K ≤
      bankTrialDurationActiveMass ring root S T := by
  have hfinal : ∀ w : List (Fin n),
      bankTrialSuccessFinalNonterminalBool ring root S w = true →
      ¬ bankTrialLocalTerminal
        (bankTrialLocalRun ring root w (bankTrialLocalStart S)) := by
    intro w hp
    change decide (¬ bankTrialLocalTerminal
      (bankTrialLocalRun ring root w (bankTrialLocalStart S))) =
        true at hp
    exact of_decide_eq_true hp
  have hword (w : List (Fin n)) :
      bankTrialSuccessStageIndexSum
          (fun j => Prob.indicator (stage j w)) K ≤
        Prob.indicator
          (bankTrialSuccessFinalNonterminalBool ring root S w) :=
    bankTrialSuccessStageIndexSumIndicatorBound
      (bankTrialSuccessFinalNonterminalBool ring root S w)
      (ordinal w) K (fun j => stage j w)
      (fun j hp => hbridge j w hp)
  calc
    bankTrialSuccessStageIndexSum
        (fun j => Prob.scheduleSum n T (fun w =>
          Prob.indicator (stage j w))) K =
      Prob.scheduleSum n T (fun w =>
        bankTrialSuccessStageIndexSum
          (fun j => Prob.indicator (stage j w)) K) :=
        bankTrialSuccessStageIndexSumSchedule n T K
          (fun j w => Prob.indicator (stage j w))
    _ ≤ Prob.scheduleSum n T (fun w =>
          Prob.indicator
            (bankTrialSuccessFinalNonterminalBool ring root S w)) :=
        bankTrialProbabilityScheduleSumMono n T _ _ hword
    _ ≤ bankTrialDurationActiveMass ring root S T :=
        bankTrialSuccessPendingMaskLeActive
          ring root S T
          (bankTrialSuccessFinalNonterminalBool ring root S)
          hfinal

/-- The unconditionally valid disjoint-sum result for the EXPLICITLY
FINAL-guarded cuts. No claim that raw stage-mass remainders equal
these smaller guarded masses is hidden in this theorem. -/
theorem bankTrialSuccessActualCutPendingFinalMassBound
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (cuts : Nat → List (Fin n) → BankTrialLocalState q → Bool)
    (cstart : Nat → Bool) (T K : Nat) :
    bankTrialSuccessStageIndexSum
        (fun j => Prob.scheduleSum n T (fun w =>
          Prob.indicator (bankTrialSuccessActualCutPendingFinalBool
            ring root S cuts cstart j T w))) K ≤
      bankTrialDurationActiveMass ring root S T := by
  exact bankTrialSuccessIndexedPendingMassBoundOfBridge
    ring root S T K
    (fun j w => bankTrialSuccessActualCutPendingFinalBool
      ring root S cuts cstart j T w)
    (bankTrialSuccessPendingOrdinal ring root S)
    (fun j w hp => bankTrialSuccessActualCutPendingFinalSound
      ring root S cuts cstart j T w hp)

/-- C.6 pays the sum of the explicitly final-stage pending masses
ONCE, rather than K times. -/
theorem bankTrialSuccessActualCutPendingFinalMarkov
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (cuts : Nat → List (Fin n) → BankTrialLocalState q → Bool)
    (cstart : Nat → Bool) (T K : Nat) :
    T * bankTrialSuccessStageIndexSum
        (fun j => Prob.scheduleSum n T (fun w =>
          Prob.indicator (bankTrialSuccessActualCutPendingFinalBool
            ring root S cuts cstart j T w))) K ≤
      n ^ T * ((8 * (compileAdvice q).b + 12) * n) := by
  calc
    T * bankTrialSuccessStageIndexSum
        (fun j => Prob.scheduleSum n T (fun w =>
          Prob.indicator (bankTrialSuccessActualCutPendingFinalBool
            ring root S cuts cstart j T w))) K ≤
      T * bankTrialDurationActiveMass ring root S T :=
        Nat.mul_le_mul_left T
          (bankTrialSuccessActualCutPendingFinalMassBound
            ring root S cuts cstart T K)
    _ ≤ n ^ T * ((8 * (compileAdvice q).b + 12) * n) :=
      bankTrialSuccessMarkovOfDurationBound ring root
        hn hsmall hw hpositive hwidth S hclean T

/-- Precisely the missing unguarded, raw actual-cut bridge.
Once the chronological cuts are instantiated and THIS premise is
proved for their residual scanners, the same single C.6 charge
applies to the *raw* pending masses used in stage iteration. -/
theorem bankTrialSuccessActualCutPendingRawMarkovOfBridge
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (cuts : Nat → List (Fin n) → BankTrialLocalState q → Bool)
    (cstart : Nat → Bool) (T K : Nat)
    (hbridge : ∀ j w,
      bankTrialSuccessActualCutPendingRawBool
        ring root S cuts cstart j T w = true →
      bankTrialSuccessFinalNonterminalBool ring root S w = true ∧
        j = bankTrialSuccessPendingOrdinal ring root S w) :
    T * bankTrialSuccessStageIndexSum
        (fun j => Prob.scheduleSum n T (fun w =>
          Prob.indicator (bankTrialSuccessActualCutPendingRawBool
            ring root S cuts cstart j T w))) K ≤
      n ^ T * ((8 * (compileAdvice q).b + 12) * n) := by
  have hm := bankTrialSuccessIndexedPendingMassBoundOfBridge
    ring root S T K
    (fun j w => bankTrialSuccessActualCutPendingRawBool
      ring root S cuts cstart j T w)
    (bankTrialSuccessPendingOrdinal ring root S) hbridge
  calc
    T * bankTrialSuccessStageIndexSum
        (fun j => Prob.scheduleSum n T (fun w =>
          Prob.indicator (bankTrialSuccessActualCutPendingRawBool
            ring root S cuts cstart j T w))) K ≤
      T * bankTrialDurationActiveMass ring root S T :=
        Nat.mul_le_mul_left T hm
    _ ≤ n ^ T * ((8 * (compileAdvice q).b + 12) * n) :=
      bankTrialSuccessMarkovOfDurationBound ring root
        hn hsmall hw hpositive hwidth S hclean T

/-- A LITERAL scheduler word and a REAL reachable initial ARMED
stage. At the initial cut, its zero-length local suffix is
PENDING BEFORE HEAD; the full scheduler word below ends WON.
This refutes charging INTERMEDIATE-CUT pending to the final-active
mask. It does NOT refute the properly suffix-evaluated
firstStoppedSuffixWord event. -/
theorem bankTrialSuccessIntermediateCutNotFinalWitness
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsmall : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S) :
    bankTrialC5PendingBeforeBool ring root S
        (bankTrialLocalStart S) [] = true ∧
    bankTrialSuccessFinalNonterminalBool ring root S
      (bankTrialC5Rounds ring root (compileAdvice q).b
        bankTrialC5Trailing (compileAdvice q).K) = false := by
  have h := bankTrialSuccessIntermediatePendingCanFinishWon
    ring root S hsmall hlarge hclean
  refine ⟨h.1, ?_⟩
  have ht : bankTrialLocalTerminal
      (bankTrialLocalRun ring root
        (bankTrialC5Rounds ring root (compileAdvice q).b
          bankTrialC5Trailing (compileAdvice q).K)
        (bankTrialLocalStart S)) := Or.inl h.2
  simp [bankTrialSuccessFinalNonterminalBool, ht]

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-!
Chronological good-return cuts on ONE scheduler tape.

An actual good return can be an increment-worker return to CSTART
or a comparator-worker return to ARMED. Those are distinct from HEAD
decisions. The scanner below uses the already installed first-origin
first-exit classifier, not a fresh probability experiment.
-/

/-- Find the FIRST consumed prefix for which the first actual worker
origin after x has a classified good return. The prefix argument is
a chronological accumulator; the final argument is the unconsumed
suffix of the SAME scheduler word. A first classified bad exit
precludes a later first good exit. -/
noncomputable def bankTrialSuccessFirstGoodReturnPrefix
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (x : BankTrialLocalState q) :
    List (Fin n) → List (Fin n) → Option (List (Fin n))
  | pre, [] =>
      if bankTrialC5PostHeadFirstExit ring root S pre x =
          some true then some pre else none
  | pre, e :: tail =>
      if bankTrialC5PostHeadFirstExit ring root S pre x =
          some true then some pre
      else bankTrialSuccessFirstGoodReturnPrefix ring root S x
        (pre ++ [e]) tail

/-- Prefix at the j-th actual GOOD worker return.
Cut zero is the CLEAN starting state. Subsequent searches use
the actual reached state and the actual remaining suffix.
No assumption that the j-th return means j completed HEADS. -/
noncomputable def bankTrialSuccessGoodReturnCutPrefix
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (word : List (Fin n)) :
    Nat → Option (List (Fin n))
  | 0 => some []
  | j + 1 =>
      match bankTrialSuccessGoodReturnCutPrefix ring root S word j with
      | none => none
      | some pre =>
          match bankTrialSuccessFirstGoodReturnPrefix ring root S
              (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
              [] (word.drop pre.length) with
          | none => none
          | some segment => some (pre ++ segment)

/-- Candidate actual K-stage cut family for
Prob.firstStoppedSuffixWord. The j-th cut fires only at the prefix
where the j-th good worker return is FIRST classified. -/
noncomputable def bankTrialSuccessGoodReturnCutBool
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Nat) (pre : List (Fin n))
    (_x : BankTrialLocalState q) : Bool :=
  decide (bankTrialSuccessGoodReturnCutPrefix
    ring root S pre j = some pre)

/-- The initial cut is exactly the empty prefix. -/
theorem bankTrialSuccessGoodReturnCutZero
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (pre : List (Fin n)) (x : BankTrialLocalState q) :
    bankTrialSuccessGoodReturnCutBool ring root S 0 pre x =
      decide (pre = []) := by
  cases pre with
  | nil => rfl
  | cons e tail => rfl

/-- A zero-length tape has no first good launched-worker return.
This is the literal postservice first-origin scanner. -/
theorem bankTrialSuccessFirstGoodReturnEmpty
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (x : BankTrialLocalState q) :
    bankTrialSuccessFirstGoodReturnPrefix
      ring root S x [] [] = none := by
  rfl

/-- Which original-clock first-exit scanner belongs to the ACTUAL
cut state is determined by that state, not by a fixed Boolean
depending on j. A CSTART seed uses the post-head scanner;
an ARMED seed uses the pre-head scanner. -/
noncomputable def bankTrialSuccessGoodReturnStagePendingAt
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q)
    (suffix : List (Fin n)) : Bool :=
  if bankTrialLiveWaveRootMode x.bank = .CSTART then
    bankTrialC5CStartPendingBool ring root S x suffix
  else if BankTrialProbabilityArmedGate x then
    bankTrialC5PendingBeforeBool ring root S x suffix ||
      bankTrialC5PendingAfterBool ring root S x suffix
  else false

/-- The stage-j residual event at one FIXED total horizon.
It reuses the original-scheduler first-stopped-prefix operator.
This is a candidate for the j-th stage's raw pending numerator,
not yet proved equal to any sum of the installed stage terms. -/
noncomputable def bankTrialSuccessGoodReturnStagePendingBool
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j T : Nat) (word : List (Fin n)) : Bool :=
  Prob.firstStoppedSuffixWord (bankTrialLocalNext ring root)
    (bankTrialSuccessGoodReturnCutBool ring root S j)
    (fun x _ suffix =>
      bankTrialSuccessGoodReturnStagePendingAt
        ring root S x suffix)
    T [] (bankTrialLocalStart S) word

/-- The actual K-stage mass is a sum over stages, not an independent
resampling of the scheduler. The missing bridge is specifically between these raw events and
the one final pending stage/ordinal. -/
noncomputable def bankTrialSuccessGoodReturnPendingMass
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T K : Nat) : Nat :=
  bankTrialSuccessStageIndexSum (fun j =>
    Prob.scheduleSum n T (fun word =>
      Prob.indicator
        (bankTrialSuccessGoodReturnStagePendingBool
          ring root S j T word))) K

/-- Classification of a terminal endpoint by a worker origin:
a LOST endpoint is BAD; a WON endpoint is either the designated
GOOD return or the wrong-head BAD exit. This is a pure consequence
of the installed actual-origin predicates. -/
theorem bankTrialSuccessWorkerTerminalHasExit
    {n q : Nat} (o : BankTrialC5ActualOrigin n q)
    (z : BankTrialLocalState q)
    (ht : bankTrialLocalTerminal z) :
    bankTrialC5ActualReturned o z ∨
      bankTrialC5ActualBadExit o z := by
  rcases ht with hw | hl
  · by_cases hr : bankTrialC5ActualReturned o z
    · exact Or.inl hr
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hw, hr⟩)))
  · exact Or.inr (Or.inr (Or.inl hl))

/-- If the installed first-exit scanner for a LAUNCHED worker
returns none on its entire remaining tape, the FINAL state
has neither a good return nor a bad exit. The induction is
over the literal original scheduler suffix, not the number
of stage cuts. -/
theorem bankTrialSuccessWorkerFirstExitNoneUnclassified
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (o : BankTrialC5ActualOrigin n q) :
    ∀ (w : List (Fin n)) (z : BankTrialLocalState q),
      bankTrialC5WorkerFirstExit ring root o w z = none →
      ¬ bankTrialC5ActualReturned o
        (bankTrialLocalRun ring root w z) ∧
      ¬ bankTrialC5ActualBadExit o
        (bankTrialLocalRun ring root w z) := by
  intro w
  induction w with
  | nil =>
      intro z hnone
      change
        (if bankTrialC5ActualReturned o z then some true
         else if bankTrialC5ActualBadExit o z then some false
         else none) = none at hnone
      by_cases hr : bankTrialC5ActualReturned o z
      · rw [if_pos hr] at hnone
        cases hnone
      · rw [if_neg hr] at hnone
        by_cases hb : bankTrialC5ActualBadExit o z
        · rw [if_pos hb] at hnone
          cases hnone
        · exact ⟨hr, hb⟩
  | cons e tail ih =>
      intro z hnone
      change
        (if bankTrialC5ActualReturned o z then some true
         else if bankTrialC5ActualBadExit o z then some false
         else bankTrialC5WorkerFirstExit ring root o tail
           (bankTrialLocalNext ring root z e)) = none at hnone
      by_cases hr : bankTrialC5ActualReturned o z
      · rw [if_pos hr] at hnone
        cases hnone
      · rw [if_neg hr] at hnone
        by_cases hb : bankTrialC5ActualBadExit o z
        · rw [if_pos hb] at hnone
          cases hnone
        · rw [if_neg hb] at hnone
          change
            ¬ bankTrialC5ActualReturned o
              (bankTrialLocalRun ring root tail
                (bankTrialLocalNext ring root z e)) ∧
            ¬ bankTrialC5ActualBadExit o
              (bankTrialLocalRun ring root tail
                (bankTrialLocalNext ring root z e))
          exact ih (bankTrialLocalNext ring root z e) hnone

/-- NONTERMINAL HALF, for the launched-worker branch of a stage.
It needs no worker-kernel hypothesis: a first-exit scanner cannot
remain unclassified after reaching WON or LOST. -/
theorem bankTrialSuccessWorkerFirstExitNoneNonterminal
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (w : List (Fin n))
    (hnone : bankTrialC5WorkerFirstExit ring root o w o.after =
      none) :
    ¬ bankTrialLocalTerminal
      (bankTrialLocalRun ring root w o.after) := by
  have hu := bankTrialSuccessWorkerFirstExitNoneUnclassified
    ring root o w o.after hnone
  intro ht
  rcases bankTrialSuccessWorkerTerminalHasExit o
      (bankTrialLocalRun ring root w o.after) ht with hr | hb
  · exact hu.1 hr
  · exact hu.2 hb

/-- The preceding nonterminal fact is on the FULL original
scheduler word once a legitimate origin is launched at pre ++ [e].
This is the part of the stage bridge already discharged by
the existing first-exit definition and reachable-origin identity. -/
theorem bankTrialSuccessLaunchedWorkerNoneFinalNonterminal
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (pre : List (Fin n)) (x : BankTrialLocalState q)
    (hx : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (e : Fin n) (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (suffix : List (Fin n))
    (hnone : bankTrialC5WorkerFirstExit ring root o suffix
      o.after = none) :
    ¬ bankTrialLocalTerminal
      (bankTrialLocalRun ring root (pre ++ (e :: suffix))
        (bankTrialLocalStart S)) := by
  have hreach := bankTrialC5GoodReturnReachable
    ring root S pre x hx e o ho suffix
  rw [← hreach]
  exact bankTrialSuccessWorkerFirstExitNoneNonterminal
    ring root o suffix hnone

/-- The exact postservice head count at any such launched origin.
This certified equality is about HEADS, not the number of
classified good worker returns; those clocks must not be conflated.
-/
theorem bankTrialSuccessLaunchedWorkerHeadExact
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (x : BankTrialLocalState q)
    (hx : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (e : Fin n) (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e) :
    o.heads = bankTrialLiveHeadCount ring root (pre ++ [e])
      (bankTrialLocalStart S) := by
  exact bankTrialC5ActualOriginHeadCountExact
    ring root S hsp hlarge hwidth hclean pre x hx e o ho

/-- A literal CLEAN-origin tape: first complete the value-0
round, then execute the positive-t increment at value 1.
That increment has its own matching worker return to CSTART.
The head counter is 2 but the ordinal is 1, since that
ordinal identifies the HEAD round, not the number of good worker
returns. -/
def bankTrialSuccessSecondIncrementWord
    {n q : Nat} (ring : DirectedRing n) (root : Fin n) :
    List (Fin n) :=
  bankTrialC5Rounds ring root (compileAdvice q).b
    bankTrialC5Trailing 1 ++
  bankTrialC5IncrementWord ring root 1

/-- Independently certified endpoint of the literal second
increment. Under the CLEAN C.3 certificate it is LIVE/CSTART,
has two actual heads, and its pendingOrdinal is ONE, not TWO.
The remaining verification that the new first-return prefix
recognizer selects this exact word as its second cut is NOT
included in this theorem. -/
theorem bankTrialSuccessSecondIncrementOrdinalWitness
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root
          (bankTrialSuccessSecondIncrementWord (q := q) ring root)
          (bankTrialLocalStart S)).bank = .CSTART ∧
    bankTrialLiveHeadCount ring root
        (bankTrialSuccessSecondIncrementWord (q := q) ring root)
        (bankTrialLocalStart S) = 2 ∧
    bankTrialSuccessPendingOrdinal ring root S
        (bankTrialSuccessSecondIncrementWord (q := q) ring root) =
      1 ∧
    bankTrialSuccessPendingOrdinal ring root S
        (bankTrialSuccessSecondIncrementWord (q := q) ring root) ≠
      2 := by
  have hq : 3 ≤ q := by
    have hs : (compileAdvice q).useSmall =
      decide (q ≤ qStar) := rfl
    rw [hs] at hsp
    have hn : ¬ q ≤ qStar := of_decide_eq_false hsp
    change ¬ q ≤ 79 at hn
    omega
  have hK : 1 < (compileAdvice q).K := by
    change 1 < 2 * q + productionKappa q
    omega
  have hb : 1 + 1 < 2 ^ (compileAdvice q).b := by
    omega
  have harmed := (bankTrialProbabilityC5DesignatedCompletion
    ring root S hsp hlarge hclean).1 1 hK
  obtain ⟨begunBefore, hphaseBefore, hmodeBefore, htokensBefore,
    hvalueBefore, hsuccessBefore, hlockedBefore⟩ := harmed
  have hstart : BankTrialC5ArmedStart n q
      (bankTrialC5CleanRun ring root S
        (bankTrialC5Rounds ring root (compileAdvice q).b
          bankTrialC5Trailing 1)) :=
    ⟨bankTrialProbabilityUpperWindow hlarge, hlockedBefore,
      ⟨begunBefore, hphaseBefore⟩, hsuccessBefore,
      hmodeBefore, htokensBefore⟩
  have htrailOne : bankTrialC5Trailing 1 = 1 := by
    simp [bankTrialC5Trailing]
  have htrail : BankTrialC5TrailingOnes
      (bankTrialC5CleanRun ring root S
        (bankTrialC5Rounds ring root (compileAdvice q).b
          bankTrialC5Trailing 1)).bank 1 := by
    have ht := bankTrialC5TrailingFromBinary
      (bankTrialC5CleanRun ring root S
        (bankTrialC5Rounds ring root (compileAdvice q).b
          bankTrialC5Trailing 1)).bank
      1 hvalueBefore hb
    rw [htrailOne] at ht
    exact ht
  obtain ⟨begunAfter, hphaseAfter, _, hmodeAfter, _,
    hcarryAfter, _⟩ :=
    bankTrialC5CleanIncrementPositive ring root S hclean
      (bankTrialC5Rounds ring root (compileAdvice q).b
        bankTrialC5Trailing 1)
      1 hstart htrail (by omega)
  have hbeforeCarry :
      bankTrialLiveCarryValue
        (bankTrialC5CleanRun ring root S
          (bankTrialC5Rounds ring root (compileAdvice q).b
            bankTrialC5Trailing 1)).bank = 1 :=
    (bankTrialC5NoWorkerCarryBinary _ htokensBefore).trans
      hvalueBefore
  have hafterCarry :
      bankTrialLiveCarryValue
        (bankTrialLocalRun ring root
          (bankTrialSuccessSecondIncrementWord (q := q) ring root)
          (bankTrialLocalStart S)).bank = 2 := by
    change
      bankTrialLiveCarryValue
        (bankTrialC5CleanRun ring root S
          (bankTrialC5Rounds ring root (compileAdvice q).b
            bankTrialC5Trailing 1 ++
            bankTrialC5IncrementWord ring root 1)).bank = 2
    calc
      _ = bankTrialLiveCarryValue
            (bankTrialC5CleanRun ring root S
              (bankTrialC5Rounds ring root (compileAdvice q).b
                bankTrialC5Trailing 1)).bank + 1 := hcarryAfter
      _ = 2 := by rw [hbeforeCarry]
  have hphaseWord :
      (bankTrialLocalRun ring root
        (bankTrialSuccessSecondIncrementWord (q := q) ring root)
        (bankTrialLocalStart S)).phase = .live begunAfter := by
    change
      (bankTrialC5CleanRun ring root S
        (bankTrialC5Rounds ring root (compileAdvice q).b
          bankTrialC5Trailing 1 ++
          bankTrialC5IncrementWord ring root 1)).phase =
        .live begunAfter
    exact hphaseAfter
  have hmodeWord :
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root
          (bankTrialSuccessSecondIncrementWord (q := q) ring root)
          (bankTrialLocalStart S)).bank = .CSTART := by
    change
      bankTrialLiveWaveRootMode
        (bankTrialC5CleanRun ring root S
          (bankTrialC5Rounds ring root (compileAdvice q).b
            bankTrialC5Trailing 1 ++
            bankTrialC5IncrementWord ring root 1)).bank = .CSTART
    exact hmodeAfter
  have hstep : BankTrialC5CompletedHeadEdgePreservation
      ring root S :=
    bankTrialC5CompletedHeadEdgePreservationOfRows
      ring root S
      (bankTrialC5RemainingLiveRowsHolds ring root hlarge hwidth)
  have hInv := bankTrialC5CompletedHeadInvariantWordsOfStep
    ring root S hlarge hwidth hclean
    (bankTrialC5CompletedHeadInvariantStart S (by omega) hclean)
    hstep (bankTrialSuccessSecondIncrementWord (q := q) ring root)
  have hheads :
      bankTrialLiveHeadCount ring root
          (bankTrialSuccessSecondIncrementWord (q := q) ring root)
          (bankTrialLocalStart S) = 2 :=
    (hInv.liveCarry begunAfter hphaseWord).symm.trans hafterCarry
  have hnot :
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root
          (bankTrialSuccessSecondIncrementWord (q := q) ring root)
          (bankTrialLocalStart S)).bank ≠ .ARMED := by
    intro he
    rw [hmodeWord] at he
    cases he
  have hordinal :
      bankTrialSuccessPendingOrdinal ring root S
        (bankTrialSuccessSecondIncrementWord (q := q) ring root) =
        1 := by
    unfold bankTrialSuccessPendingOrdinal
    rw [if_neg hnot, hheads]
  refine ⟨hmodeWord, hheads, hordinal, ?_⟩
  rw [hordinal]
  omega

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-!
Count actual GOOD worker returns rather than ARMED HEADs.

The ordinal below is obtained from the previously installed
chronological good-return cuts. Its fuel is the number of actual
scheduler letters: no fresh scheduler or independent stage sample is
introduced. This is not bankTrialSuccessPendingOrdinal.
-/

/-- The number of classified good returns among the first m
successive positive-index cut tests on the SAME physical word. -/
noncomputable def bankTrialSuccessGoodReturnOrdinalPrefix
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word : List (Fin n)) (m : Nat) : Nat :=
  bankTrialSuccessStageIndexSum (fun j =>
    if (bankTrialSuccessGoodReturnCutPrefix
      ring root S word (j + 1)).isSome then 1 else 0) m

/-- New ordinal: count every actual classified good-worker return,
both increment-to-CSTART and comparator-to-ARMED, on the original
scheduler tape. Cut zero is the initial seed, not a good return. -/
noncomputable def bankTrialSuccessGoodReturnOrdinal
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word : List (Fin n)) : Nat :=
  bankTrialSuccessGoodReturnOrdinalPrefix ring root S
    word word.length

theorem bankTrialSuccessStageIndexSumUnit (m : Nat) :
    bankTrialSuccessStageIndexSum (fun _ => 1) m = m := by
  induction m with
  | zero => rfl
  | succ k ih =>
      change bankTrialSuccessStageIndexSum (fun _ => 1) k + 1 =
        k + 1
      rw [ih]

/-- The good-return ordinal never exceeds the number of
chronological physical scheduler letters scanned. No worker
bound, independence, or expensive advice arithmetic is used. -/
theorem bankTrialSuccessGoodReturnOrdinalLengthBound
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word : List (Fin n)) :
    bankTrialSuccessGoodReturnOrdinal ring root S word ≤
      word.length := by
  have hunit (j : Nat) :
      (if (bankTrialSuccessGoodReturnCutPrefix ring root S
          word (j + 1)).isSome then 1 else 0) ≤ 1 := by
    split <;> omega
  have hsum := bankTrialSuccessStageIndexSumMono
    (fun j =>
      if (bankTrialSuccessGoodReturnCutPrefix ring root S
        word (j + 1)).isSome then 1 else 0)
    (fun _ => 1) hunit word.length
  rw [bankTrialSuccessStageIndexSumUnit] at hsum
  exact hsum

/-- On the empty word there is no classified good-worker return. -/
theorem bankTrialSuccessGoodReturnOrdinalEmpty
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    bankTrialSuccessGoodReturnOrdinal ring root S [] = 0 := by
  rfl

/-- CSTART no-origin ONE-EDGE ROW, at an arbitrary CLEAN-reachable
LIVE/CSTART seed. An outgoing root edge necessarily emits the actual
comparator origin. If the census emits no origin, that edge cannot be
outgoing root, and the successor stays LIVE/CSTART.
The incoming-root exception is handled by the installed physical
incoming CSTART row; all other edges use the root-frame row. -/
theorem bankTrialSuccessCStartNoOriginNext
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (z : BankTrialLocalState q)
    (begun : Bool)
    (hreach : z = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hlive : z.phase = .live begun)
    (hmode : bankTrialLiveWaveRootMode z.bank = .CSTART)
    (e : Fin n)
    (hno : bankTrialC5ActualStarts ring root S z e = []) :
    ∃ nextBegun : Bool,
      (bankTrialLocalNext ring root z e).phase =
        .live nextBegun ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root z e).bank = .CSTART := by
  have hzeta :
      z = (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
    cases z with
    | mk B phase =>
      change phase = .live begun at hlive
      cases hlive
      rfl
  have hrun :
      bankTrialLocalRun ring root pre
        (bankTrialLocalStart S) =
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
    rw [← hreach]
    exact hzeta
  have hf : z.bank.success = false :=
    bankTrialProbabilityCleanLiveUnlatched
      ring root S hclean pre z.bank begun hrun
  by_cases he : e = root
  · subst e
    obtain ⟨o, ho, _, _⟩ :=
      bankTrialC5CStartRootActualOrigin
        ring root S hlarge hclean pre z begun
        hreach hlive hmode
    rw [hno] at ho
    cases ho
  · by_cases hin : ring.rightNeighbor e = root
    · have hm :
          ((GrantBankReference.bankLocalReferenceStepClamped
            ring root z.bank e).fields ⟨0, by omega⟩).1 =
              .CSTART :=
        bankTrialProbabilityIncomingCStartMode
          ring root e z.bank hf hmode he hin
      have hs :
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root z.bank e).success = false :=
        bankTrialLocalUnlatchedNonrootNoWin
          ring root e z.bank hf he
      have hstep := bankTrialProbabilityLiveCStartNext
        ring root e z.bank begun hs hm (Or.inr hin)
      refine ⟨true, ?_, ?_⟩
      · rw [hzeta, hstep]
      · rw [hzeta, bankTrialLocalNextLiveBank]
        exact hm
    · have hframe := bankTrialLocalRootNonincidentFrame
        ring root e z.bank hf he hin
      have hm :
          ((GrantBankReference.bankLocalReferenceStepClamped
            ring root z.bank e).fields ⟨0, by omega⟩).1 =
              .CSTART :=
        (congrArg (fun p => p.1) hframe).trans hmode
      have hs :
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root z.bank e).success = false :=
        bankTrialLocalUnlatchedNonrootNoWin
          ring root e z.bank hf he
      have hnotClean :
          ¬ BankTrialLocalClean q
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root z.bank e) := by
        intro hc
        have ha := hc.2.1
        rw [hm] at ha
        cases ha
      have hnotReset :
          ((GrantBankReference.bankLocalReferenceStepClamped
            ring root z.bank e).fields ⟨0, by omega⟩).1 ≠
              .RESET := by
        intro hr
        rw [hm] at hr
        cases hr
      have hstep :
          (bankTrialLocalNext ring root
            (⟨z.bank, .live begun⟩ : BankTrialLocalState q)
            e).phase =
          .live (begun || decide
            (e = root ∨ ring.rightNeighbor e = root)) := by
        simp [bankTrialLocalNext, hs, hnotClean]
        split
        · rename_i hr
          exact absurd hr hnotReset
        · rfl
      have hnotIncident :
          ¬ (e = root ∨ ring.rightNeighbor e = root) := by
        intro hi
        rcases hi with hr | hi
        · exact he hr
        · exact hin hi
      refine ⟨begun, ?_, ?_⟩
      · rw [hzeta]
        simpa [hnotIncident] using hstep
      · rw [hzeta, bankTrialLocalNextLiveBank]
        exact hm

/-- FULL-SUFFIX no-origin/first-origin dichotomy for a reachable
LIVE/CSTART seed. The [] census branch uses the ONE-EDGE ROW
above; the emitted-origin branch uses the already proved worker
first-exit nonterminal theorem. Thus the literal post-head
scanner's NONE outcome cannot end in WON or LOST. -/
theorem bankTrialSuccessCStartPostHeadNoneNonterminal
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S) :
    ∀ (word : List (Fin n))
      (pre : List (Fin n)) (z : BankTrialLocalState q)
      (begun : Bool),
      z = bankTrialLocalRun ring root pre (bankTrialLocalStart S) →
      z.phase = .live begun →
      bankTrialLiveWaveRootMode z.bank = .CSTART →
      bankTrialC5PostHeadFirstExit ring root S word z = none →
      ¬ bankTrialLocalTerminal
        (bankTrialLocalRun ring root word z) := by
  intro word
  induction word with
  | nil =>
      intro pre z begun hreach hlive hmode hnone
      change ¬ bankTrialLocalTerminal z
      intro ht
      rcases ht with hw | hl
      · rw [hlive] at hw
        cases hw
      · rw [hlive] at hl
        cases hl
  | cons e tail ih =>
      intro pre z begun hreach hlive hmode hnone
      have hscan :
          (match bankTrialC5ActualStarts ring root S z e with
          | [] =>
              bankTrialC5PostHeadFirstExit ring root S tail
                (bankTrialLocalNext ring root z e)
          | o :: _ =>
              bankTrialC5WorkerFirstExit ring root o tail
                (bankTrialLocalNext ring root z e)) = none := hnone
      cases hstarts : bankTrialC5ActualStarts ring root S z e with
      | nil =>
          rw [hstarts] at hscan
          obtain ⟨nextBegun, hphase, hmodeNext⟩ :=
            bankTrialSuccessCStartNoOriginNext
              ring root S hlarge hclean pre z begun
              hreach hlive hmode e hstarts
          have hreachNext :
              bankTrialLocalNext ring root z e =
                bankTrialLocalRun ring root (pre ++ [e])
                  (bankTrialLocalStart S) := by
            rw [bankTrialLocalRunAppend, ← hreach]
            rfl
          change ¬ bankTrialLocalTerminal
            (bankTrialLocalRun ring root tail
              (bankTrialLocalNext ring root z e))
          exact ih (pre ++ [e])
            (bankTrialLocalNext ring root z e)
            nextBegun hreachNext hphase hmodeNext hscan
      | cons o others =>
          rw [hstarts] at hscan
          have ho :
              o ∈ bankTrialC5ActualStarts ring root S z e := by
            rw [hstarts]
            simp
          have hpost :=
            bankTrialC5ActualStartPost ring root S z e o ho
          have hworker :
              bankTrialC5WorkerFirstExit ring root o tail
                o.after = none := by
            rw [hpost]
            exact hscan
          have hterminal :=
            bankTrialSuccessWorkerFirstExitNoneNonterminal
              ring root o tail hworker
          change ¬ bankTrialLocalTerminal
            (bankTrialLocalRun ring root tail
              (bankTrialLocalNext ring root z e))
          rw [← hpost]
          exact hterminal

/-- This is the requested no-origin half, expressed directly for
the installed CSTART pending indicator at a valid reachable cut. -/
theorem bankTrialSuccessCStartPendingFinalNonterminal
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (z : BankTrialLocalState q)
    (begun : Bool)
    (hreach : z = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hlive : z.phase = .live begun)
    (hmode : bankTrialLiveWaveRootMode z.bank = .CSTART)
    (suffix : List (Fin n))
    (hpending : bankTrialC5CStartPendingBool
      ring root S z suffix = true) :
    ¬ bankTrialLocalTerminal
      (bankTrialLocalRun ring root suffix z) := by
  have hnone :
      bankTrialC5PostHeadFirstExit ring root S suffix z = none := by
    by_cases hn :
        bankTrialC5PostHeadFirstExit ring root S suffix z = none
    · exact hn
    · have hf :
          bankTrialC5CStartPendingBool
            ring root S z suffix = false := by
        simp [bankTrialC5CStartPendingBool, hn]
      rw [hf] at hpending
      cases hpending
  exact bankTrialSuccessCStartPostHeadNoneNonterminal
    ring root S hlarge hclean suffix pre z begun
    hreach hlive hmode hnone

/-- If an authenticated actual cut is a reachable CSTART state,
then stage-indexed raw pending on its residual suffix is a
FINAL-horizon nonterminal event, with the original word restored.
The separate ARMED and index-identification cases are not assumed. -/
theorem bankTrialSuccessCStartPendingActualWordNonterminal
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre suffix : List (Fin n))
    (begun : Bool)
    (hlive :
      (bankTrialLocalRun ring root pre
        (bankTrialLocalStart S)).phase = .live begun)
    (hmode :
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root pre
          (bankTrialLocalStart S)).bank = .CSTART)
    (hpending : bankTrialSuccessGoodReturnStagePendingAt
      ring root S
      (bankTrialLocalRun ring root pre
        (bankTrialLocalStart S)) suffix = true) :
    ¬ bankTrialLocalTerminal
      (bankTrialLocalRun ring root (pre ++ suffix)
        (bankTrialLocalStart S)) := by
  have hc :
      bankTrialC5CStartPendingBool ring root S
        (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
        suffix = true := by
    simpa [bankTrialSuccessGoodReturnStagePendingAt,
      hmode] using hpending
  rw [bankTrialLocalRunAppend]
  exact bankTrialSuccessCStartPendingFinalNonterminal
    ring root S hlarge hclean pre
    (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
    begun rfl hlive hmode suffix hc

/-- The exact stage-sum bound follows from the new good-return
ordinal if the still-open actual-cut bridge is discharged.
This theorem does not silently identify a first-return cut with
a final-stage index. -/
theorem bankTrialSuccessGoodReturnPendingMassBoundOfBridge
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (T K : Nat)
    (hbridge : ∀ j w,
      bankTrialSuccessGoodReturnStagePendingBool
        ring root S j T w = true →
      bankTrialSuccessFinalNonterminalBool ring root S w =
        true ∧
      j = bankTrialSuccessGoodReturnOrdinal ring root S w) :
    bankTrialSuccessGoodReturnPendingMass ring root S T K ≤
      bankTrialDurationActiveMass ring root S T := by
  unfold bankTrialSuccessGoodReturnPendingMass
  exact bankTrialSuccessIndexedPendingMassBoundOfBridge
    ring root S T K
    (fun j w =>
      bankTrialSuccessGoodReturnStagePendingBool
        ring root S j T w)
    (bankTrialSuccessGoodReturnOrdinal ring root S)
    hbridge

/-- Once the actual-cut bridge is available, all K-index pending
terms receive ONE C.6 charge. The parameter K here is a cut-index
range, not yet claimed to be bounded by 2*(compileAdvice q).K. -/
theorem bankTrialSuccessGoodReturnPendingMarkovOfBridge
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (T K : Nat)
    (hbridge : ∀ j w,
      bankTrialSuccessGoodReturnStagePendingBool
        ring root S j T w = true →
      bankTrialSuccessFinalNonterminalBool ring root S w =
        true ∧
      j = bankTrialSuccessGoodReturnOrdinal ring root S w) :
    T * bankTrialSuccessGoodReturnPendingMass ring root S T K ≤
      n ^ T * ((8 * (compileAdvice q).b + 12) * n) := by
  calc
    T * bankTrialSuccessGoodReturnPendingMass ring root S T K ≤
      T * bankTrialDurationActiveMass ring root S T :=
        Nat.mul_le_mul_left T
          (bankTrialSuccessGoodReturnPendingMassBoundOfBridge
            ring root S T K hbridge)
    _ ≤ n ^ T * ((8 * (compileAdvice q).b + 12) * n) :=
      bankTrialSuccessMarkovOfDurationBound
        ring root hn hsmall hw hpositive hwidth S hclean T

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-!
ARMED pre-incident and first-outgoing-head rows.
The later ARMED cut and ordinal/slot injectivity gaps are kept
separate; no generic stage bridge is asserted without those rows.
-/

/-- Public root-incoming port equivalence, using the literal
modular ring coordinates and core Nat arithmetic only. -/
theorem bankTrialSuccessIncomingIffLeft {n : Nat}
    (ring : DirectedRing n) (root e : Fin n) :
    ring.rightNeighbor e = root ↔
      e = ring.leftNeighbor root := by
  have hleft (i : Fin n) :
      ring.leftNeighbor (ring.rightNeighbor i) = i := by
    apply Fin.ext
    change (((i.val + 1) % n + n - 1) % n) = i.val
    have heq :
        (i.val + 1) % n + n - 1 =
          (i.val + 1) % n + (n - 1) := by
      have hn := ring.hn
      omega
    rw [heq, Nat.mod_add_mod]
    have heq' : i.val + 1 + (n - 1) = i.val + n := by
      have hn := ring.hn
      omega
    rw [heq', Nat.add_mod]
    simp [Nat.mod_eq_of_lt i.isLt]
  have hright (i : Fin n) :
      ring.rightNeighbor (ring.leftNeighbor i) = i := by
    apply Fin.ext
    change (((i.val + n - 1) % n + 1) % n) = i.val
    rw [Nat.mod_add_mod]
    have heq : i.val + n - 1 + 1 = i.val + n := by
      have hn := ring.hn
      omega
    rw [heq, Nat.add_mod]
    simp [Nat.mod_eq_of_lt i.isLt]
  constructor
  · intro h
    calc
      e = ring.leftNeighbor (ring.rightNeighbor e) :=
        (hleft e).symm
      _ = ring.leftNeighbor root := congrArg ring.leftNeighbor h
  · intro h
    rw [h]
    exact hright root

/-- Before the FIRST incident, an unbegun ARMED observer stays
unbegun and ARMED. This physical row does not need the global
CLEAN start: the OLD success latch is false, and the old phase
is LIVE false. The Clean-loss guard cannot fire without a prior
begun flag or a root-incident edge. -/
theorem bankTrialSuccessUnbegunArmedNonincidentNext
    {n q : Nat} (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialLocalState q)
    (hlive : z.phase = .live false)
    (hf : z.bank.success = false)
    (hm : bankTrialLiveWaveRootMode z.bank = .ARMED)
    (hne : e ≠ root) (hni : ring.rightNeighbor e ≠ root) :
    (bankTrialLocalNext ring root z e).phase = .live false ∧
    bankTrialLiveWaveRootMode
      (bankTrialLocalNext ring root z e).bank = .ARMED ∧
    (bankTrialLocalNext ring root z e).bank.success = false := by
  have hzeta :
      z = (⟨z.bank, .live false⟩ : BankTrialLocalState q) := by
    cases z with
    | mk B phase =>
      change phase = .live false at hlive
      cases hlive
      rfl
  have hframe := bankTrialLocalRootNonincidentFrame
    ring root e z.bank hf hne hni
  have hmnew :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root z.bank e).fields ⟨0, by omega⟩).1 =
        .ARMED :=
    (congrArg (fun p => p.1) hframe).trans hm
  have hs :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root z.bank e).success = false :=
    bankTrialLocalUnlatchedNonrootNoWin
      ring root e z.bank hf hne
  have hguard :
      ¬ (BankTrialLocalClean q
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root z.bank e) ∧
          (false = true ∨ e = root ∨ ring.rightNeighbor e = root)) := by
    intro hg
    rcases hg.2 with hb | he | hi
    · cases hb
    · exact hne he
    · exact hni hi
  have hreset :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root z.bank e).fields ⟨0, by omega⟩).1 ≠
          .RESET := by
    intro hr
    rw [hmnew] at hr
    cases hr
  have hnext :
      bankTrialLocalNext ring root
        (⟨z.bank, .live false⟩ : BankTrialLocalState q) e =
      ⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root z.bank e, .live false⟩ := by
    simp [bankTrialLocalNext, hs, hguard, hne, hni]
    exact hreset
  refine ⟨?_, ?_, ?_⟩
  · rw [hzeta, hnext]
  · rw [hzeta, hnext]
    exact hmnew
  · rw [hzeta, hnext]
    exact hs

/-- Iterate the previous physical row over ALL letters before
the first outgoing or incoming root incident, without changing
the original scheduler tape. -/
theorem bankTrialSuccessUnbegunArmedBeforeIncident
    {n q : Nat} (ring : DirectedRing n) (root : Fin n) :
    ∀ (word : List (Fin n)) (z : BankTrialLocalState q),
      z.phase = .live false →
      z.bank.success = false →
      bankTrialLiveWaveRootMode z.bank = .ARMED →
      bankTrialProbabilityFirstIncidentOrientation
        root (ring.leftNeighbor root) word = none →
      (bankTrialLocalRun ring root word z).phase = .live false ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root word z).bank = .ARMED ∧
      (bankTrialLocalRun ring root word z).bank.success = false := by
  intro word
  induction word with
  | nil =>
      intro z hp hf hm _
      exact ⟨hp, hm, hf⟩
  | cons e tail ih =>
      intro z hp hf hm hnone
      have he : e ≠ root := by
        intro he
        have ht :
            bankTrialProbabilityFirstIncidentOrientation
              root (ring.leftNeighbor root) (e :: tail) =
                some true := by
          simp [bankTrialProbabilityFirstIncidentOrientation, he]
        rw [ht] at hnone
        cases hnone
      have hi : e ≠ ring.leftNeighbor root := by
        intro hi
        have ht :
            bankTrialProbabilityFirstIncidentOrientation
              root (ring.leftNeighbor root) (e :: tail) =
                some false := by
          simp [bankTrialProbabilityFirstIncidentOrientation, hi,
            (show ring.leftNeighbor root ≠ root from hi ▸ he)]
        rw [ht] at hnone
        cases hnone
      have hni : ring.rightNeighbor e ≠ root := by
        intro hin
        exact hi ((bankTrialSuccessIncomingIffLeft
          ring root e).mp hin)
      have htail :
          bankTrialProbabilityFirstIncidentOrientation
            root (ring.leftNeighbor root) tail = none := by
        simpa only [bankTrialProbabilityFirstIncidentOrientation,
          if_neg he, if_neg hi] using hnone
      obtain ⟨hpnext, hmnext, hfnext⟩ :=
        bankTrialSuccessUnbegunArmedNonincidentNext
          ring root e z hp hf hm he hni
      change
        (bankTrialLocalRun ring root tail
          (bankTrialLocalNext ring root z e)).phase = .live false ∧
        bankTrialLiveWaveRootMode
          (bankTrialLocalRun ring root tail
            (bankTrialLocalNext ring root z e)).bank = .ARMED ∧
        (bankTrialLocalRun ring root tail
          (bankTrialLocalNext ring root z e)).bank.success = false
      exact ih (bankTrialLocalNext ring root z e)
        hpnext hfnext hmnext htail

/-- The raw BEFORE-HEAD pending remainder at the genuine CLEAN
stage-zero cut is a FINAL-horizon nonterminal event. This is the
full no-first-incident result at the initial ARMED cut, not merely
a one-edge statement. -/
theorem bankTrialSuccessCleanArmedPendingBeforeNonterminal
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (word : List (Fin n))
    (hpending : bankTrialC5PendingBeforeBool
      ring root S (bankTrialLocalStart S) word = true) :
    ¬ bankTrialLocalTerminal
      (bankTrialLocalRun ring root word (bankTrialLocalStart S)) := by
  have hnone :
      bankTrialProbabilityFirstIncidentOrientation
        root (ring.leftNeighbor root) word = none := by
    by_cases h :
        bankTrialProbabilityFirstIncidentOrientation
          root (ring.leftNeighbor root) word = none
    · exact h
    · have hf : bankTrialC5PendingBeforeBool
          ring root S (bankTrialLocalStart S) word = false := by
        simp [bankTrialC5PendingBeforeBool, h]
      rw [hf] at hpending
      cases hpending
  have hrun := bankTrialSuccessUnbegunArmedBeforeIncident
    ring root word (bankTrialLocalStart S)
    rfl hclean.1 hclean.2.1 hnone
  intro ht
  rcases ht with hw | hl
  · rw [hrun.1] at hw
    cases hw
  · rw [hrun.1] at hl
    cases hl

/-- Every CLEAN-reachable LIVE/ARMED gate satisfies the full
C.1 ARMED-start certificate: no-RESET lock, empty worker tokens,
unlatched success and spatial nonalias. -/
theorem bankTrialSuccessReachableArmedStart
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (z : BankTrialLocalState q)
    (hz : z = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hgate : BankTrialProbabilityArmedGate z) :
    BankTrialC5ArmedStart n q z := by
  obtain ⟨⟨begun, hlive⟩, hm⟩ := hgate
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hlock : BankTrialLiveNoResetLocked z := by
    rw [hz]
    exact bankTrialWindowLockedCleanWords
      ring root hw S hclean pre
  have htokens : ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken z.bank j = .E := by
    intro j
    exact (hlock.1 begun hlive).headClear j (Or.inl hm)
  have hzeta :
      z = (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
    cases z with
    | mk B phase =>
      change phase = .live begun at hlive
      cases hlive
      rfl
  have hrun :
      bankTrialLocalRun ring root pre (bankTrialLocalStart S) =
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
    rw [← hz]
    exact hzeta
  have hf : z.bank.success = false :=
    bankTrialProbabilityCleanLiveUnlatched
      ring root S hclean pre z.bank begun hrun
  exact ⟨hw, hlock, ⟨begun, hlive⟩, hf, hm, htokens⟩

/-- If an authentic ARMED HEAD does not emit a worker origin,
the first digit was zero, and the HEAD is the workerless
LIVE/CSTART transition, not an unclassified terminal event. -/
theorem bankTrialSuccessArmedHeadNoOriginCStart
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (z : BankTrialLocalState q)
    (hz : z = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hgate : BankTrialProbabilityArmedGate z)
    (hno : bankTrialC5ActualStarts ring root S z root = []) :
    ∃ begun : Bool,
      (bankTrialLocalNext ring root z root).phase = .live begun ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root z root).bank = .CSTART := by
  obtain ⟨⟨oldBegun, hlive⟩, hm⟩ := id hgate
  have hstart := bankTrialSuccessReachableArmedStart
    ring root S hlarge hclean pre z hz hgate
  cases hbit : bankTrialLiveWaveBit z.bank
      ⟨0, bankTrialWindowWidthPos q⟩ with
  | false =>
      have hzero := bankTrialC5ArmedHeadZeroCStart
        ring root z hstart hbit
      obtain ⟨begun, hp⟩ := hzero.live
      exact ⟨begun, hp, hzero.cstart⟩
  | true =>
      have hone := bankTrialC5ArmedHeadOneStage
        ring root z hstart hbit
      obtain ⟨nextBegun, hphase⟩ := hone.1
      have hmode :
          bankTrialLiveWaveRootMode
            (bankTrialLocalNext ring root z root).bank = .IWAIT :=
        hone.2.2.1
      have hguard :
          BankTrialLocalClean q S ∧
          (∃ w : List (Fin n),
            bankTrialLocalRun ring root w (bankTrialLocalStart S) =
              z) ∧
          root = root ∧
          (∃ begun nextBegun : Bool,
            z.phase = .live begun ∧
            (bankTrialLocalNext ring root z root).phase =
              .live nextBegun) ∧
          ((bankTrialLiveWaveRootMode z.bank = .ARMED ∧
            bankTrialLiveWaveRootMode
              (bankTrialLocalNext ring root z root).bank = .IWAIT) ∨
           (bankTrialLiveWaveRootMode z.bank = .CSTART ∧
            bankTrialLiveWaveRootMode
              (bankTrialLocalNext ring root z root).bank = .CWAIT)) :=
        ⟨hclean, ⟨pre, hz.symm⟩, rfl,
          ⟨oldBegun, nextBegun, hlive, hphase⟩,
          Or.inl ⟨hm, hmode⟩⟩
      have hnonempty :
          bankTrialC5ActualStarts ring root S z root ≠ [] := by
        unfold bankTrialC5ActualStarts
        rw [if_pos hguard]
        simp
      exact False.elim (hnonempty hno)

/-- Full first-outgoing-HEAD ARMED case. If its first-origin
scanner has no classified exit at the FINAL suffix, the endpoint
is nonterminal. A workerless HEAD goes to CSTART;
a launched origin uses the first-worker NONE theorem. -/
theorem bankTrialSuccessArmedFirstOutgoingNoneNonterminal
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (z : BankTrialLocalState q)
    (hz : z = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hgate : BankTrialProbabilityArmedGate z)
    (tail : List (Fin n))
    (hnone : bankTrialC5PreHeadFirstExit ring root S
      (root :: tail) z = none) :
    ¬ bankTrialLocalTerminal
      (bankTrialLocalRun ring root (root :: tail) z) := by
  have hscan := hnone
  cases hstarts : bankTrialC5ActualStarts ring root S z root with
  | nil =>
      simp only [bankTrialC5PreHeadFirstExit, if_pos rfl, if_true,
        hstarts] at hscan
      obtain ⟨begun, hp, hm⟩ :=
        bankTrialSuccessArmedHeadNoOriginCStart
          ring root S hlarge hclean pre z hz hgate hstarts
      have hreachNext :
          bankTrialLocalNext ring root z root =
            bankTrialLocalRun ring root (pre ++ [root])
              (bankTrialLocalStart S) := by
        rw [bankTrialLocalRunAppend, ← hz]
        rfl
      change ¬ bankTrialLocalTerminal
        (bankTrialLocalRun ring root tail
          (bankTrialLocalNext ring root z root))
      exact bankTrialSuccessCStartPostHeadNoneNonterminal
        ring root S hlarge hclean tail (pre ++ [root])
        (bankTrialLocalNext ring root z root)
        begun hreachNext hp hm hscan
  | cons o others =>
      simp only [bankTrialC5PreHeadFirstExit, if_pos rfl, if_true,
        hstarts] at hscan
      have ho :
          o ∈ bankTrialC5ActualStarts ring root S z root := by
        rw [hstarts]
        simp
      have hpost :=
        bankTrialC5ActualStartPost ring root S z root o ho
      have hworker :
          bankTrialC5WorkerFirstExit ring root o tail o.after =
            none := by
        rw [hpost]
        exact hscan
      change ¬ bankTrialLocalTerminal
        (bankTrialLocalRun ring root tail
          (bankTrialLocalNext ring root z root))
      rw [← hpost]
      exact bankTrialSuccessWorkerFirstExitNoneNonterminal
        ring root o tail hworker

/-- A later good-return cut is impossible if its immediate
predecessor cut is absent on this very same scheduler word. -/
theorem bankTrialSuccessGoodReturnCutNoneSuccessor
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word : List (Fin n)) (j : Nat)
    (hnone : bankTrialSuccessGoodReturnCutPrefix
      ring root S word j = none) :
    bankTrialSuccessGoodReturnCutPrefix
      ring root S word (j + 1) = none := by
  simp only [bankTrialSuccessGoodReturnCutPrefix, hnone]

/-- The absent-cut property is upward closed under stage index. -/
theorem bankTrialSuccessGoodReturnCutNoneAbove
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word : List (Fin n)) (j : Nat)
    (hnone : bankTrialSuccessGoodReturnCutPrefix
      ring root S word j = none) :
    ∀ i, j ≤ i →
      bankTrialSuccessGoodReturnCutPrefix
        ring root S word i = none := by
  intro i
  induction i with
  | zero =>
      intro hle
      have hj : j = 0 := by omega
      rw [hj] at hnone
      simp [bankTrialSuccessGoodReturnCutPrefix] at hnone
  | succ i ih =>
      intro hle
      by_cases hprev : j ≤ i
      · exact bankTrialSuccessGoodReturnCutNoneSuccessor
          ring root S word i (ih hprev)
      · have heq : j = i + 1 := by omega
        rw [← heq]
        exact hnone

/-- Core finite indexed sum of a consecutive true prefix.
No Nat.find, Finset or non-small decide is used. -/
theorem bankTrialSuccessStageIndexSumPrefixMin
    (m j : Nat) :
    bankTrialSuccessStageIndexSum
      (fun i => if i < j then 1 else 0) m = min m j := by
  induction m with
  | zero =>
      simp [bankTrialSuccessStageIndexSum]
  | succ m ih =>
      change
        bankTrialSuccessStageIndexSum
            (fun i => if i < j then 1 else 0) m +
          (if m < j then 1 else 0) =
        min (m + 1) j
      rw [ih]
      by_cases hlt : m < j
      · rw [if_pos hlt,
          Nat.min_eq_left (by omega : m ≤ j),
          Nat.min_eq_left (by omega : m + 1 ≤ j)]
      · rw [if_neg hlt,
          Nat.min_eq_right (by omega : j ≤ m),
          Nat.min_eq_right (by omega : j ≤ m + 1)]
        omega

/-- Ordinal cut-count identity reduced to two explicit chronological
facts: all first j cuts exist, and cut j+1 does not. The remaining
task is to derive these facts from the raw stopped-suffix pending
scanner. The identity itself uses the ORIGINAL scheduler-word length.
-/
theorem bankTrialSuccessGoodReturnOrdinalOfFirstMissing
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word : List (Fin n)) (j : Nat)
    (hbound : j ≤ word.length)
    (hprevious : ∀ i, i < j →
      (bankTrialSuccessGoodReturnCutPrefix
        ring root S word (i + 1)).isSome = true)
    (hmissing : bankTrialSuccessGoodReturnCutPrefix
      ring root S word (j + 1) = none) :
    bankTrialSuccessGoodReturnOrdinal ring root S word = j := by
  have hindex (i : Nat) :
      (if (bankTrialSuccessGoodReturnCutPrefix
          ring root S word (i + 1)).isSome then 1 else 0) =
        (if i < j then 1 else 0) := by
    by_cases hi : i < j
    · simp [hi, hprevious i hi]
    · have hle : j + 1 ≤ i + 1 := by omega
      have hnone :=
        bankTrialSuccessGoodReturnCutNoneAbove
          ring root S word (j + 1) hmissing
          (i + 1) hle
      simp [hi, hnone]
  have heq :
      (fun i =>
        if (bankTrialSuccessGoodReturnCutPrefix
          ring root S word (i + 1)).isSome then 1 else 0) =
      (fun i => if i < j then 1 else 0) := by
    funext i
    exact hindex i
  unfold bankTrialSuccessGoodReturnOrdinal
    bankTrialSuccessGoodReturnOrdinalPrefix
  rw [heq, bankTrialSuccessStageIndexSumPrefixMin,
    Nat.min_eq_right hbound]

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-!
Exact positive-carry ARMED preservation on the original
scheduler. Successor LIVE-ness is established only AFTER ruling
out the CLEAN loss guard with exact postservice BANK carry.
-/

/-- The clamped reference conserves ALL weighted carry on a
non-root-incident edge at an authenticated, unlatched ARMED
snapshot. This has no hypothesis about the observer successor. -/
theorem bankTrialSuccessArmedNonincidentCarryExact
    {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .ARMED)
    (hne : e ≠ root)
    (hni : ring.rightNeighbor e ≠ root) :
    bankTrialLiveCarryValue
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) =
      bankTrialLiveCarryValue B := by
  have hOld : ∀ i : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken B i ≠ .IR := by
    intro i
    rw [hc.headClear i (Or.inl hm)]
    intro hh
    cases hh
  rcases Counter.resetTrialEdgeGeometry (q := q)
      ring root e with hsource | hin | hout
  · obtain ⟨j, hj, he⟩ := hsource
    by_cases htop : j = (compileAdvice q).b
    · subst j
      have hnoIR :
          bankTrialLiveWaveToken B
            ⟨(compileAdvice q).b - 1,
              by have hb := bankTrialCmpWidth q; omega⟩ ≠ .IR :=
        hOld _
      have hframe := bankTrialC5TopWholeBitTokenModeFrame
        ring root hw B hf hnoIR
      have hnew : ∀ i : Fin (compileAdvice q).b,
          bankTrialLiveWaveToken
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B
              (Counter.site ring root (compileAdvice q).b)) i ≠ .IR := by
        intro i
        rw [(hframe.1 i).2]
        exact hOld i
      rw [he]
      exact bankTrialC5CarryOfNoIRBitFrame B
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root (compileAdvice q).b))
        (fun i => (hframe.1 i).1) hOld hnew
    · by_cases hzero : j = 0
      · subst j
        have heq : e = root := by
          rw [he]
          simp [Counter.site]
        exact False.elim (hne heq)
      · have hjpos : 0 < j := by omega
        have hjlt : j < (compileAdvice q).b := by omega
        rw [he]
        exact bankTrialC5InteriorHeadClearCarryExact
          ring root hw B hf ⟨j, hjlt⟩ hjpos hc (Or.inl hm)
  · exact False.elim (hni hin)
  · have houtside : ¬ Counter.Support q ring root e := by
      intro hs
      rcases hs with hs | ⟨j, hj, he⟩
      · exact (hout 0 (by omega)).2 hs
      · exact (hout j hj).1 he
    rw [bankTrialLocalStepOutside ring root e B houtside]

/-- Positive carry prevents any spurious CLEAN-to-LOST transition
in the begun=true ARMED case. -/
theorem bankTrialSuccessPositiveArmedNonincidentNext
    {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hw : BankTrialLiveWindowNonalias n q)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n))
    (z : BankTrialLocalState q) (begun : Bool)
    (hz : z = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hlive : z.phase = .live begun)
    (hm : bankTrialLiveWaveRootMode z.bank = .ARMED)
    (hpos : 0 < bankTrialLiveCarryValue z.bank)
    (hne : e ≠ root)
    (hni : ring.rightNeighbor e ≠ root) :
    (bankTrialLocalNext ring root z e).phase = .live begun ∧
    bankTrialLiveWaveRootMode
      (bankTrialLocalNext ring root z e).bank = .ARMED ∧
    bankTrialLiveCarryValue
      (bankTrialLocalNext ring root z e).bank =
        bankTrialLiveCarryValue z.bank := by
  have hlock : BankTrialLiveNoResetLocked z := by
    rw [hz]
    exact bankTrialWindowLockedCleanWords ring root hw S hclean pre
  have hc : BankTrialLiveWaveCertificate q z.bank :=
    hlock.1 begun hlive
  have hzeta :
      z = (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
    cases z with
    | mk B phase =>
      change phase = .live begun at hlive
      cases hlive
      rfl
  have hrun :
      bankTrialLocalRun ring root pre (bankTrialLocalStart S) =
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) := by
    rw [← hz]
    exact hzeta
  have hf : z.bank.success = false :=
    bankTrialProbabilityCleanLiveUnlatched
      ring root S hclean pre z.bank begun hrun
  have hmodeRaw :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root z.bank e).fields ⟨0, by omega⟩).1 =
          .ARMED :=
    (congrArg (fun p => p.1)
      (bankTrialLocalRootNonincidentFrame
        ring root e z.bank hf hne hni)).trans hm
  have hcarryRaw := bankTrialSuccessArmedNonincidentCarryExact
    ring root e hw z.bank hf hc hm hne hni
  have hsuccessRaw :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root z.bank e).success = false :=
    bankTrialLocalUnlatchedNonrootNoWin
      ring root e z.bank hf hne
  have hnotCleanRaw :
      ¬ BankTrialLocalClean q
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root z.bank e) := by
    intro hnewClean
    have hzero := bankTrialLiveCarryClean
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root z.bank e) hnewClean
    rw [hcarryRaw] at hzero
    omega
  have hnotReset :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root z.bank e).fields ⟨0, by omega⟩).1 ≠ .RESET := by
    intro hr
    rw [hmodeRaw] at hr
    cases hr
  have hnext :
      bankTrialLocalNext ring root
        (⟨z.bank, .live begun⟩ : BankTrialLocalState q) e =
      ⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root z.bank e, .live begun⟩ := by
    simp [bankTrialLocalNext, hsuccessRaw, hnotCleanRaw, hne, hni]
    exact hnotReset
  refine ⟨?_, ?_, ?_⟩
  · rw [hzeta, hnext]
  · rw [hzeta, hnext]
    exact hmodeRaw
  · rw [hzeta, hnext]
    exact hcarryRaw

/-- Exact carry, phase and ARMED mode persist for any no-incident
scheduler suffix, including when the initial begun flag is true. -/
theorem bankTrialSuccessPositiveArmedBeforeIncident
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hw : BankTrialLiveWindowNonalias n q)
    (hclean : BankTrialLocalClean q S) :
    ∀ (word pre : List (Fin n))
      (z : BankTrialLocalState q) (begun : Bool),
      z = bankTrialLocalRun ring root pre
        (bankTrialLocalStart S) →
      z.phase = .live begun →
      bankTrialLiveWaveRootMode z.bank = .ARMED →
      0 < bankTrialLiveCarryValue z.bank →
      bankTrialProbabilityFirstIncidentOrientation
        root (ring.leftNeighbor root) word = none →
      (bankTrialLocalRun ring root word z).phase = .live begun ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root word z).bank = .ARMED ∧
      bankTrialLiveCarryValue
        (bankTrialLocalRun ring root word z).bank =
          bankTrialLiveCarryValue z.bank := by
  intro word
  induction word with
  | nil =>
      intro pre z begun hz hp hm hpos _
      exact ⟨hp, hm, rfl⟩
  | cons e tail ih =>
      intro pre z begun hz hp hm hpos hnone
      have hne : e ≠ root := by
        intro he
        have hh :
            bankTrialProbabilityFirstIncidentOrientation
              root (ring.leftNeighbor root) (e :: tail) =
                some true := by
          simp [bankTrialProbabilityFirstIncidentOrientation, he]
        rw [hh] at hnone
        cases hnone
      have hleft : e ≠ ring.leftNeighbor root := by
        intro he
        have hh :
            bankTrialProbabilityFirstIncidentOrientation
              root (ring.leftNeighbor root) (e :: tail) =
                some false := by
          simp [bankTrialProbabilityFirstIncidentOrientation,
            he, (show ring.leftNeighbor root ≠ root from he ▸ hne)]
        rw [hh] at hnone
        cases hnone
      have hni : ring.rightNeighbor e ≠ root := by
        intro hi
        exact hleft ((bankTrialSuccessIncomingIffLeft
          ring root e).mp hi)
      have htail :
          bankTrialProbabilityFirstIncidentOrientation
            root (ring.leftNeighbor root) tail = none := by
        simpa only [bankTrialProbabilityFirstIncidentOrientation,
          if_neg hne, if_neg hleft] using hnone
      obtain ⟨hpNext, hmNext, hcNext⟩ :=
        bankTrialSuccessPositiveArmedNonincidentNext
          ring root e S hw hclean pre z begun hz hp hm hpos hne hni
      have hzNext :
          bankTrialLocalNext ring root z e =
            bankTrialLocalRun ring root (pre ++ [e])
              (bankTrialLocalStart S) := by
        rw [bankTrialLocalRunAppend, ← hz]
        rfl
      have hposNext :
          0 < bankTrialLiveCarryValue
            (bankTrialLocalNext ring root z e).bank := by
        rw [hcNext]
        exact hpos
      have hrest := ih (pre ++ [e])
        (bankTrialLocalNext ring root z e)
        begun hzNext hpNext hmNext hposNext htail
      change
        (bankTrialLocalRun ring root tail
          (bankTrialLocalNext ring root z e)).phase = .live begun ∧
        bankTrialLiveWaveRootMode
          (bankTrialLocalRun ring root tail
            (bankTrialLocalNext ring root z e)).bank = .ARMED ∧
        bankTrialLiveCarryValue
          (bankTrialLocalRun ring root tail
            (bankTrialLocalNext ring root z e)).bank =
            bankTrialLiveCarryValue z.bank
      exact ⟨hrest.1, hrest.2.1, hrest.2.2.trans hcNext⟩

/-- Later CLEAN-reachable ARMED stage, positive authentic head
count: a pending BEFORE-HEAD scanner implies a nonterminal
FINAL endpoint on the same full scheduler tape. -/
theorem bankTrialSuccessPositiveHeadArmedPendingBeforeNonterminal
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (begun : Bool)
    (hlive :
      (bankTrialLocalRun ring root pre
        (bankTrialLocalStart S)).phase = .live begun)
    (hm :
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root pre
          (bankTrialLocalStart S)).bank = .ARMED)
    (hpositive :
      0 < bankTrialLiveHeadCount ring root pre
        (bankTrialLocalStart S))
    (suffix : List (Fin n))
    (hpending : bankTrialC5PendingBeforeBool
      ring root S
      (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
      suffix = true) :
    ¬ bankTrialLocalTerminal
      (bankTrialLocalRun ring root (pre ++ suffix)
        (bankTrialLocalStart S)) := by
  have hnone :
      bankTrialProbabilityFirstIncidentOrientation
        root (ring.leftNeighbor root) suffix = none := by
    by_cases h :
        bankTrialProbabilityFirstIncidentOrientation
          root (ring.leftNeighbor root) suffix = none
    · exact h
    · have hfalse : bankTrialC5PendingBeforeBool
          ring root S
          (bankTrialLocalRun ring root pre
            (bankTrialLocalStart S)) suffix = false := by
        simp [bankTrialC5PendingBeforeBool, h]
      rw [hfalse] at hpending
      cases hpending
  have hK : 0 < (compileAdvice q).K :=
    Counter.resetColdPrivateKPositive q hsp
  have hstep : BankTrialC5CompletedHeadEdgePreservation
      ring root S :=
    bankTrialC5CompletedHeadEdgePreservationOfRows
      ring root S
      (bankTrialC5RemainingLiveRowsHolds ring root hlarge hwidth)
  have hInv := bankTrialC5CompletedHeadInvariantWordsOfStep
    ring root S hlarge hwidth hclean
    (bankTrialC5CompletedHeadInvariantStart S hK hclean)
    hstep pre
  have hposCarry :
      0 < bankTrialLiveCarryValue
        (bankTrialLocalRun ring root pre
          (bankTrialLocalStart S)).bank := by
    rw [hInv.liveCarry begun hlive]
    exact hpositive
  have hrun := bankTrialSuccessPositiveArmedBeforeIncident
    ring root S (bankTrialProbabilityUpperWindow hlarge)
    hclean suffix pre
    (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
    begun rfl hlive hm hposCarry hnone
  rw [bankTrialLocalRunAppend]
  intro ht
  rcases ht with hw | hl
  · rw [hrun.1] at hw
    cases hw
  · rw [hrun.1] at hl
    cases hl

/-- At an authenticated ARMED-k return, empty worker tokens
make the BANK carry exactly k. -/
theorem bankTrialSuccessArmedAtPositiveCarry
    {q : Nat}
    (z : BankTrialLocalState q) (k : Nat)
    (harmed : BankTrialC5ArmedAt q z k)
    (hk : 0 < k) :
    0 < bankTrialLiveCarryValue z.bank := by
  obtain ⟨_, _, _, htokens, hvalue, _, _⟩ := harmed
  rw [bankTrialC5NoWorkerCarryBinary z.bank htokens, hvalue]
  exact hk

/-- Stage zero stops at the initial empty prefix. -/
theorem bankTrialSuccessGoodReturnStageZeroExact
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (T : Nat) (word : List (Fin n)) :
    bankTrialSuccessGoodReturnStagePendingBool
        ring root S 0 T word =
      bankTrialSuccessGoodReturnStagePendingAt
        ring root S (bankTrialLocalStart S) word := by
  unfold bankTrialSuccessGoodReturnStagePendingBool
  cases word with
  | nil =>
      simp [Prob.firstStoppedSuffixWord,
        bankTrialSuccessGoodReturnCutBool,
        bankTrialSuccessGoodReturnCutPrefix]
  | cons e tail =>
      simp [Prob.firstStoppedSuffixWord,
        bankTrialSuccessGoodReturnCutBool,
        bankTrialSuccessGoodReturnCutPrefix]

/-- The first-missing-cut ordinal equation for stage zero. -/
theorem bankTrialSuccessGoodReturnOrdinalZeroOfNoFirst
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word : List (Fin n))
    (hnone : bankTrialSuccessGoodReturnCutPrefix
      ring root S word 1 = none) :
    bankTrialSuccessGoodReturnOrdinal ring root S word = 0 := by
  exact bankTrialSuccessGoodReturnOrdinalOfFirstMissing
    ring root S word 0 (Nat.zero_le _)
    (by intro i hi; omega) hnone

/-- Existing completed-head invariant specialized to actual
reachable ARMED states: the authentic head count is strictly
below K. This is an ingredient, not the 2K return-slot injection. -/
theorem bankTrialSuccessReachableArmedHeadStrict
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n))
    (hgate : BankTrialProbabilityArmedGate
      (bankTrialLocalRun ring root pre
        (bankTrialLocalStart S))) :
    bankTrialLiveHeadCount ring root pre
      (bankTrialLocalStart S) < (compileAdvice q).K := by
  have hK : 0 < (compileAdvice q).K :=
    Counter.resetColdPrivateKPositive q hsp
  have hstep : BankTrialC5CompletedHeadEdgePreservation
      ring root S :=
    bankTrialC5CompletedHeadEdgePreservationOfRows
      ring root S
      (bankTrialC5RemainingLiveRowsHolds ring root hlarge hwidth)
  have hInv := bankTrialC5CompletedHeadInvariantWordsOfStep
    ring root S hlarge hwidth hclean
    (bankTrialC5CompletedHeadInvariantStart S hK hclean)
    hstep pre
  obtain ⟨⟨begun, hlive⟩, hmode⟩ := id hgate
  exact hInv.armedStrict begun hlive hmode

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Every actually emitted worker origin has positive postservice
chronological HEAD count. An ARMED origin pays its new HEAD; a CSTART
origin already had a positive HEAD count. -/
theorem bankTrialSuccessActualOriginHeadsPositive
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (x : BankTrialLocalState q)
    (hx : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (e : Fin n) (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e) :
    0 < o.heads := by
  by_cases hm : bankTrialLiveWaveRootMode x.bank = .ARMED
  · obtain ⟨_, _, he, ⟨begun, _, hlive, _⟩, _⟩ :=
      bankTrialC5ActualStartGuardFacts ring root S x e o ho
    have hg : BankTrialProbabilityArmedGate x :=
      ⟨⟨begun, hlive⟩, hm⟩
    have hone : bankTrialLiveHeadCount ring root [e] x = 1 := by
      change (if BankTrialProbabilityArmedGate x ∧ e = root
        then 1 else 0) + 0 = 1
      rw [if_pos ⟨hg, he⟩]
    have hpost :
        bankTrialLiveHeadCount ring root (pre ++ [e])
          (bankTrialLocalStart S) =
        bankTrialLiveHeadCount ring root pre
          (bankTrialLocalStart S) + 1 := by
      rw [bankTrialLiveHeadCountAppend, ← hx, hone]
    have hcount := bankTrialC5ActualOriginHeadCountExact
      ring root S hsp hlarge hwidth hclean pre x hx e o ho
    rw [hpost] at hcount
    omega
  · have hcomp : o.increment = false :=
      (bankTrialC5ActualIncrementTagExact
        ring root S x e o ho).trans (decide_eq_false hm)
    exact bankTrialC5ActualComparatorOriginPositive
      ring root S hsp hlarge hwidth x e o ho hcomp

/-- A GOOD return in the first-origin scan implies that the
CLEAN-start full scheduler word contains at least one HEAD. -/
theorem bankTrialSuccessPostHeadGoodHasHeads
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    ∀ (word pre : List (Fin n)) (x : BankTrialLocalState q),
      x = bankTrialLocalRun ring root pre
        (bankTrialLocalStart S) →
      bankTrialC5PostHeadFirstExit ring root S word x =
        some true →
      0 < bankTrialLiveHeadCount ring root (pre ++ word)
        (bankTrialLocalStart S) := by
  intro word
  induction word with
  | nil =>
      intro pre x hx hgood
      simp only [bankTrialC5PostHeadFirstExit] at hgood
      cases hgood
  | cons e tail ih =>
      intro pre x hx hgood
      cases hstarts : bankTrialC5ActualStarts ring root S x e with
      | nil =>
          have hscan :
              bankTrialC5PostHeadFirstExit ring root S tail
                (bankTrialLocalNext ring root x e) =
                  some true := by
            simpa only [bankTrialC5PostHeadFirstExit,
              hstarts] using hgood
          have hreach :
              bankTrialLocalNext ring root x e =
                bankTrialLocalRun ring root (pre ++ [e])
                  (bankTrialLocalStart S) := by
            rw [bankTrialLocalRunAppend, ← hx]
            rfl
          have hh := ih (pre ++ [e])
            (bankTrialLocalNext ring root x e) hreach hscan
          have hword : (pre ++ [e]) ++ tail =
              pre ++ (e :: tail) := by
            simp only [List.append_assoc, List.singleton_append]
          rw [hword] at hh
          exact hh
      | cons o others =>
          have ho :
              o ∈ bankTrialC5ActualStarts ring root S x e := by
            rw [hstarts]
            simp
          have hp := bankTrialSuccessActualOriginHeadsPositive
            ring root S hsp hlarge hwidth hclean
            pre x hx e o ho
          have hpost :
              bankTrialLocalRun ring root (pre ++ [e])
                (bankTrialLocalStart S) = o.after := by
            rw [bankTrialLocalRunAppend, ← hx]
            exact (bankTrialC5ActualStartPost
              ring root S x e o ho).symm
          have hcount := bankTrialC5ActualOriginHeadCountExact
            ring root S hsp hlarge hwidth hclean
            pre x hx e o ho
          have hsplit : pre ++ (e :: tail) =
              (pre ++ [e]) ++ tail := by
            simp only [List.append_assoc, List.singleton_append]
          have hfull :
              bankTrialLiveHeadCount ring root (pre ++ (e :: tail))
                  (bankTrialLocalStart S) =
                o.heads +
                  bankTrialLiveHeadCount ring root tail o.after := by
            calc
              _ = bankTrialLiveHeadCount ring root
                    ((pre ++ [e]) ++ tail)
                    (bankTrialLocalStart S) :=
                      congrArg (fun v =>
                        bankTrialLiveHeadCount ring root v
                          (bankTrialLocalStart S)) hsplit
              _ = bankTrialLiveHeadCount ring root (pre ++ [e])
                    (bankTrialLocalStart S) +
                  bankTrialLiveHeadCount ring root tail
                    (bankTrialLocalRun ring root (pre ++ [e])
                      (bankTrialLocalStart S)) :=
                bankTrialLiveHeadCountAppend ring root
                  (pre ++ [e]) tail (bankTrialLocalStart S)
              _ = o.heads +
                  bankTrialLiveHeadCount ring root tail o.after := by
                rw [← hcount, hpost]
          rw [hfull]
          omega

/-- A successful chronological first-good prefix has positive
HEAD count on the original CLEAN-start tape. -/
theorem bankTrialSuccessFirstGoodPrefixHeadsPositive
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) :
    ∀ (remaining base acc found : List (Fin n)),
      x = bankTrialLocalRun ring root base
        (bankTrialLocalStart S) →
      bankTrialSuccessFirstGoodReturnPrefix
        ring root S x acc remaining = some found →
      0 < bankTrialLiveHeadCount ring root (base ++ found)
        (bankTrialLocalStart S) := by
  intro remaining
  induction remaining with
  | nil =>
      intro base acc found hx hfound
      by_cases hscan :
          bankTrialC5PostHeadFirstExit ring root S acc x =
            some true
      · have hsome : some acc = some found := by
          simpa only [bankTrialSuccessFirstGoodReturnPrefix,
            if_pos hscan] using hfound
        have heq : acc = found := Option.some.inj hsome
        rw [← heq]
        exact bankTrialSuccessPostHeadGoodHasHeads
          ring root S hsp hlarge hwidth hclean
          acc base x hx hscan
      · simp only [bankTrialSuccessFirstGoodReturnPrefix,
          if_neg hscan] at hfound
        cases hfound
  | cons e tail ih =>
      intro base acc found hx hfound
      by_cases hscan :
          bankTrialC5PostHeadFirstExit ring root S acc x =
            some true
      · have hsome : some acc = some found := by
          simpa only [bankTrialSuccessFirstGoodReturnPrefix,
            if_pos hscan] using hfound
        have heq : acc = found := Option.some.inj hsome
        rw [← heq]
        exact bankTrialSuccessPostHeadGoodHasHeads
          ring root S hsp hlarge hwidth hclean
          acc base x hx hscan
      · have htail :
            bankTrialSuccessFirstGoodReturnPrefix
              ring root S x (acc ++ [e]) tail = some found := by
          simpa only [bankTrialSuccessFirstGoodReturnPrefix,
            if_neg hscan] using hfound
        exact ih base (acc ++ [e]) found hx htail

/-- Every positive-index recursive GOOD-return cut has positive
chronological HEAD count. The j+1 cut is inverted directly:
no unproved cut consistency is needed for positivity. -/
theorem bankTrialSuccessNonzeroGoodReturnCutHeadsPositive
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (word cut : List (Fin n)) (j : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word (j + 1) = some cut) :
    0 < bankTrialLiveHeadCount ring root cut
      (bankTrialLocalStart S) := by
  cases hprev :
      bankTrialSuccessGoodReturnCutPrefix
        ring root S word j with
  | none =>
      simp only [bankTrialSuccessGoodReturnCutPrefix,
        hprev] at hcut
      cases hcut
  | some prev =>
      cases hfirst :
          bankTrialSuccessFirstGoodReturnPrefix
            ring root S
            (bankTrialLocalRun ring root prev
              (bankTrialLocalStart S))
            [] (word.drop prev.length) with
      | none =>
          simp only [bankTrialSuccessGoodReturnCutPrefix,
            hprev, hfirst] at hcut
          cases hcut
      | some segment =>
          have hsome : some (prev ++ segment) = some cut := by
            simpa only [bankTrialSuccessGoodReturnCutPrefix,
              hprev, hfirst] using hcut
          have heq : prev ++ segment = cut := Option.some.inj hsome
          rw [← heq]
          exact bankTrialSuccessFirstGoodPrefixHeadsPositive
            ring root S hsp hlarge hwidth hclean
            (bankTrialLocalRun ring root prev (bankTrialLocalStart S))
            (word.drop prev.length) prev [] segment rfl hfirst

/-- A TRUE positive-index stage stop supplies the exact positive
HEAD budget needed later. -/
theorem bankTrialSuccessNonzeroCutBoolHeadsPositive
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (j : Nat)
    (hstop : bankTrialSuccessGoodReturnCutBool
      ring root S (j + 1) pre
        (bankTrialLocalRun ring root pre
          (bankTrialLocalStart S)) = true) :
    0 < bankTrialLiveHeadCount ring root pre
      (bankTrialLocalStart S) := by
  have hcut :
      bankTrialSuccessGoodReturnCutPrefix
        ring root S pre (j + 1) = some pre :=
    of_decide_eq_true (by
      simpa only [bankTrialSuccessGoodReturnCutBool] using hstop)
  exact bankTrialSuccessNonzeroGoodReturnCutHeadsPositive
    ring root S hsp hlarge hwidth hclean pre pre j hcut

/-- The later-ARMED pending-BEFORE nonterminal theorem now needs
no independent positive-head assumption: the genuine nonzero
good-return cut certifies it. -/
theorem bankTrialSuccessNonzeroGoodCutPendingBeforeNonterminal
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (word cut suffix : List (Fin n)) (j : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word (j + 1) = some cut)
    (begun : Bool)
    (hlive : (bankTrialLocalRun ring root cut
      (bankTrialLocalStart S)).phase = .live begun)
    (hm : bankTrialLiveWaveRootMode
      (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S)).bank = .ARMED)
    (hpending : bankTrialC5PendingBeforeBool ring root S
      (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S)) suffix = true) :
    ¬ bankTrialLocalTerminal
      (bankTrialLocalRun ring root (cut ++ suffix)
        (bankTrialLocalStart S)) := by
  have hp := bankTrialSuccessNonzeroGoodReturnCutHeadsPositive
    ring root S hsp hlarge hwidth hclean word cut j hcut
  exact bankTrialSuccessPositiveHeadArmedPendingBeforeNonterminal
    ring root S hsp hlarge hwidth hclean cut begun
    hlive hm hp suffix hpending

/-- Chronological first-exit ledger: positive postservice origin
credit is preserved as an absolute HEAD count at the actual
first-exit prefix of the same physical scheduler word. -/
theorem bankTrialSuccessActualFirstExitHeadsPositive
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (pre : List (Fin n))
    (hbefore : ∀ (u v : List (Fin n)) (f : Fin n),
      pre = u ++ (f :: v) →
      ¬ (bankTrialC5ActualReturned o
          (bankTrialLocalRun ring root u o.after) ∨
         bankTrialC5ActualBadExit o
          (bankTrialLocalRun ring root u o.after))) :
    ∃ launch : List (Fin n),
      bankTrialLocalRun ring root launch
        (bankTrialLocalStart S) = x ∧
      0 < bankTrialLiveHeadCount ring root
        (launch ++ (e :: pre)) (bankTrialLocalStart S) := by
  obtain ⟨launch, hlaunch, hcount⟩ :=
    bankTrialC5ActualOriginChronologicalHeadLedger
      ring root S hsp hlarge hwidth hclean x e o ho pre hbefore
  have hp := bankTrialSuccessActualOriginHeadsPositive
    ring root S hsp hlarge hwidth hclean
    launch x hlaunch.symm e o ho
  refine ⟨launch, hlaunch, ?_⟩
  rw [hcount]
  exact hp

/-- The run ledger: every strictly unresolved genuine worker
retains positive numeric carry throughout its pre-exit interval. -/
theorem bankTrialSuccessUnresolvedWorkerCarryPositive
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialC5ActualStarts ring root S x e)
    (pre : List (Fin n))
    (hbefore : ∀ (u v : List (Fin n)) (f : Fin n),
      pre = u ++ (f :: v) →
      ¬ (bankTrialC5ActualReturned o
          (bankTrialLocalRun ring root u o.after) ∨
         bankTrialC5ActualBadExit o
          (bankTrialLocalRun ring root u o.after)))
    (hcurrent :
      ¬ (bankTrialC5ActualReturned o
          (bankTrialLocalRun ring root pre o.after) ∨
         bankTrialC5ActualBadExit o
          (bankTrialLocalRun ring root pre o.after))) :
    0 < bankTrialLiveCarryValue
      (bankTrialLocalRun ring root pre o.after).bank := by
  obtain ⟨launch, hlaunch, _⟩ :=
    bankTrialC5ActualOriginChronologicalHeadLedger
      ring root S hsp hlarge hwidth hclean x e o ho pre hbefore
  have hp := bankTrialSuccessActualOriginHeadsPositive
    ring root S hsp hlarge hwidth hclean
    launch x hlaunch.symm e o ho
  have hr := bankTrialC5ActualOriginRunLedger
    ring root S hsp hlarge hwidth hclean
    x e o ho pre hbefore hcurrent
  rw [hr.2.2]
  exact hp

/-- A successful first-GOOD prefix is an actual prefix of its
accumulated scheduler tape. -/
theorem bankTrialSuccessFirstGoodPrefixIsPrefix
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (x : BankTrialLocalState q) :
    ∀ (remaining acc found : List (Fin n)),
      bankTrialSuccessFirstGoodReturnPrefix
        ring root S x acc remaining = some found →
      ∃ suffix : List (Fin n),
        acc ++ remaining = found ++ suffix := by
  intro remaining
  induction remaining with
  | nil =>
      intro acc found hfound
      by_cases hscan :
          bankTrialC5PostHeadFirstExit ring root S acc x =
            some true
      · have hsome : some acc = some found := by
          simpa only [bankTrialSuccessFirstGoodReturnPrefix,
            if_pos hscan] using hfound
        have heq : acc = found := Option.some.inj hsome
        rw [← heq]
        exact ⟨[], by simp⟩
      · simp only [bankTrialSuccessFirstGoodReturnPrefix,
          if_neg hscan] at hfound
        cases hfound
  | cons e tail ih =>
      intro acc found hfound
      by_cases hscan :
          bankTrialC5PostHeadFirstExit ring root S acc x =
            some true
      · have hsome : some acc = some found := by
          simpa only [bankTrialSuccessFirstGoodReturnPrefix,
            if_pos hscan] using hfound
        have heq : acc = found := Option.some.inj hsome
        rw [← heq]
        exact ⟨e :: tail, rfl⟩
      · have htail :
            bankTrialSuccessFirstGoodReturnPrefix
              ring root S x (acc ++ [e]) tail = some found := by
          simpa only [bankTrialSuccessFirstGoodReturnPrefix,
            if_neg hscan] using hfound
        obtain ⟨suffix, hprefix⟩ :=
          ih (acc ++ [e]) found htail
        refine ⟨suffix, ?_⟩
        simpa only [List.append_assoc, List.singleton_append] using
          hprefix

/-- A recursive good-return cut, at any index, is a prefix of
the original full word. This is a preparatory lemma for full
stopped-prefix/cut-prefix identification. -/
theorem bankTrialSuccessGoodReturnCutIsPrefix
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (word : List (Fin n)) :
    ∀ (j : Nat) (cut : List (Fin n)),
      bankTrialSuccessGoodReturnCutPrefix
        ring root S word j = some cut →
      ∃ suffix : List (Fin n), word = cut ++ suffix := by
  intro j
  induction j with
  | zero =>
      intro cut hcut
      have hsome : some ([] : List (Fin n)) = some cut := by
        simpa only [bankTrialSuccessGoodReturnCutPrefix] using hcut
      have heq : [] = cut := Option.some.inj hsome
      rw [← heq]
      exact ⟨word, by simp⟩
  | succ j ih =>
      intro cut hcut
      cases hprev :
          bankTrialSuccessGoodReturnCutPrefix
            ring root S word j with
      | none =>
          simp only [bankTrialSuccessGoodReturnCutPrefix,
            hprev] at hcut
          cases hcut
      | some prev =>
          obtain ⟨remaining, hword⟩ := ih prev hprev
          cases hfirst :
              bankTrialSuccessFirstGoodReturnPrefix
                ring root S
                (bankTrialLocalRun ring root prev
                  (bankTrialLocalStart S))
                [] (word.drop prev.length) with
          | none =>
              simp only [bankTrialSuccessGoodReturnCutPrefix,
                hprev, hfirst] at hcut
              cases hcut
          | some segment =>
              have hsome : some (prev ++ segment) = some cut := by
                simpa only [bankTrialSuccessGoodReturnCutPrefix,
                  hprev, hfirst] using hcut
              have heq : prev ++ segment = cut :=
                Option.some.inj hsome
              obtain ⟨tail, htail⟩ :=
                bankTrialSuccessFirstGoodPrefixIsPrefix
                  ring root S
                  (bankTrialLocalRun ring root prev
                    (bankTrialLocalStart S))
                  (word.drop prev.length) [] segment hfirst
              have hrem : remaining = segment ++ tail := by
                rw [hword] at htail
                simpa using htail
              refine ⟨tail, ?_⟩
              rw [hword, ← heq, hrem]
              simp only [List.append_assoc]

end L3


namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-!
The ARMED pending-AFTER branch and chronological
prefix consistency. All words are on the original physical
Fin n scheduler; no independent stage samples are introduced.
-/

/-- A raw pending-AFTER event has a FIRST outgoing incident
and neither classified first-exit outcome. This is the
literal four-way classifier, not an assumed worker fairness law. -/
theorem bankTrialSuccessPendingAfterFirstExitNone
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (z : BankTrialLocalState q) (word : List (Fin n))
    (hp : bankTrialC5PendingAfterBool ring root S z word =
      true) :
    bankTrialProbabilityFirstIncidentOrientation
        root (ring.leftNeighbor root) word = some true ∧
      bankTrialC5PreHeadFirstExit ring root S word z = none := by
  have hfirst :
      bankTrialProbabilityFirstIncidentOrientation
        root (ring.leftNeighbor root) word = some true := by
    by_cases hf :
        bankTrialProbabilityFirstIncidentOrientation
          root (ring.leftNeighbor root) word = some true
    · exact hf
    · have hfalse :
          bankTrialC5PendingAfterBool ring root S z word =
            false := by
        simp [bankTrialC5PendingAfterBool, hf]
      rw [hfalse] at hp
      cases hp
  refine ⟨hfirst, ?_⟩
  cases hscan :
      bankTrialC5PreHeadFirstExit ring root S word z with
  | none =>
      rfl
  | some b =>
      cases b with
      | false =>
          have hclass :
              bankTrialC5StageClass ring root S z word =
                .bad := by
            simp [bankTrialC5StageClass, hfirst, hscan]
          have hf :
              bankTrialC5PendingAfterBool ring root S z word =
                false := by
            simp [bankTrialC5PendingAfterBool, hfirst,
              bankTrialC5StageClassBool, hclass]
          rw [hf] at hp
          cases hp
      | true =>
          have hclass :
              bankTrialC5StageClass ring root S z word =
                .good := by
            simp [bankTrialC5StageClass, hfirst, hscan]
          have hf :
              bankTrialC5PendingAfterBool ring root S z word =
                false := by
            simp [bankTrialC5PendingAfterBool, hfirst,
              bankTrialC5StageClassBool, hclass]
          rw [hf] at hp
          cases hp

/-- An ARMED cut is safe on a nonincident edge if either it is
still unbegun, or its authenticated BANK carry is positive.
Both possibilities are preserved, including begun=true. -/
theorem bankTrialSuccessArmedNonincidentCreditNext
    {n q : Nat} (ring : DirectedRing n) (root e : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (z : BankTrialLocalState q)
    (begun : Bool)
    (hz : z = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hlive : z.phase = .live begun)
    (hm : bankTrialLiveWaveRootMode z.bank = .ARMED)
    (hcredit : begun = false ∨
      0 < bankTrialLiveCarryValue z.bank)
    (hne : e ≠ root) (hni : ring.rightNeighbor e ≠ root) :
    ∃ nextBegun : Bool,
      (bankTrialLocalNext ring root z e).phase =
        .live nextBegun ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root z e).bank = .ARMED ∧
      (nextBegun = false ∨
        0 < bankTrialLiveCarryValue
          (bankTrialLocalNext ring root z e).bank) := by
  rcases hcredit with hfalse | hpos
  · subst begun
    have hf : z.bank.success = false :=
      (bankTrialSuccessReachableArmedStart
        ring root S hlarge hclean pre z hz
        ⟨⟨false, hlive⟩, hm⟩).2.2.2.1
    obtain ⟨hp, hmode, _⟩ :=
      bankTrialSuccessUnbegunArmedNonincidentNext
        ring root e z hlive hf hm hne hni
    exact ⟨false, hp, hmode, Or.inl rfl⟩
  · obtain ⟨hp, hmode, hcarry⟩ :=
      bankTrialSuccessPositiveArmedNonincidentNext
        ring root e S
        (bankTrialProbabilityUpperWindow hlarge)
        hclean pre z begun hz hlive hm hpos hne hni
    refine ⟨begun, hp, hmode, Or.inr ?_⟩
    rw [hcarry]
    exact hpos

/-- Induct on the physical suffix until its FIRST outgoing
incident. The incoming TAIL branch is impossible under
orientation=some true. At the HEAD, both the
workerless CSTART wait and the launched-worker first exit are handled. -/
theorem bankTrialSuccessArmedFirstOutgoingNoneOfCredit
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S) :
    ∀ (word pre : List (Fin n))
      (z : BankTrialLocalState q) (begun : Bool),
      z = bankTrialLocalRun ring root pre
        (bankTrialLocalStart S) →
      z.phase = .live begun →
      bankTrialLiveWaveRootMode z.bank = .ARMED →
      (begun = false ∨
        0 < bankTrialLiveCarryValue z.bank) →
      bankTrialProbabilityFirstIncidentOrientation
        root (ring.leftNeighbor root) word = some true →
      bankTrialC5PreHeadFirstExit ring root S word z = none →
      ¬ bankTrialLocalTerminal
        (bankTrialLocalRun ring root (pre ++ word)
          (bankTrialLocalStart S)) := by
  intro word
  induction word with
  | nil =>
      intro pre z begun hz hlive hm hcredit hfirst hnone
      simp only [bankTrialProbabilityFirstIncidentOrientation] at hfirst
      cases hfirst
  | cons e tail ih =>
      intro pre z begun hz hlive hm hcredit hfirst hnone
      by_cases he : e = root
      · subst e
        rw [bankTrialLocalRunAppend, ← hz]
        exact bankTrialSuccessArmedFirstOutgoingNoneNonterminal
          ring root S hlarge hclean pre z hz
          ⟨⟨begun, hlive⟩, hm⟩ tail hnone
      · by_cases hi : e = ring.leftNeighbor root
        · have htailport :
              bankTrialProbabilityFirstIncidentOrientation
                root (ring.leftNeighbor root) (e :: tail) =
                some false := by
            simp [bankTrialProbabilityFirstIncidentOrientation,
              hi, (show ring.leftNeighbor root ≠ root from
                hi ▸ he)]
          rw [htailport] at hfirst
          cases hfirst
        · have hni : ring.rightNeighbor e ≠ root := by
            intro hin
            exact hi ((bankTrialSuccessIncomingIffLeft
              ring root e).mp hin)
          have hfirstTail :
              bankTrialProbabilityFirstIncidentOrientation
                root (ring.leftNeighbor root) tail = some true := by
            simpa only [bankTrialProbabilityFirstIncidentOrientation,
              if_neg he, if_neg hi] using hfirst
          have hnoneTail :
              bankTrialC5PreHeadFirstExit ring root S tail
                (bankTrialLocalNext ring root z e) = none := by
            simpa only [bankTrialC5PreHeadFirstExit,
              if_neg he, if_neg hi] using hnone
          obtain ⟨nextBegun, hp, hmode, hcreditNext⟩ :=
            bankTrialSuccessArmedNonincidentCreditNext
              ring root e S hlarge hclean pre z begun
              hz hlive hm hcredit he hni
          have hzNext :
              bankTrialLocalNext ring root z e =
                bankTrialLocalRun ring root (pre ++ [e])
                  (bankTrialLocalStart S) := by
            rw [bankTrialLocalRunAppend, ← hz]
            rfl
          have hrest := ih (pre ++ [e])
            (bankTrialLocalNext ring root z e) nextBegun
            hzNext hp hmode hcreditNext hfirstTail hnoneTail
          simpa only [List.append_assoc, List.singleton_append]
            using hrest

/-- The pending-AFTER half of the ARMED bridge: no re-sampling,
no assumption that begun=false, and no mistaken incoming-tail
classification. The separate credit premise is discharged at
every positive-index actual cut by the head ledger. -/
theorem bankTrialSuccessArmedPendingAfterOfCredit
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (z : BankTrialLocalState q)
    (begun : Bool)
    (hz : z = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hlive : z.phase = .live begun)
    (hm : bankTrialLiveWaveRootMode z.bank = .ARMED)
    (hcredit : begun = false ∨
      0 < bankTrialLiveCarryValue z.bank)
    (word : List (Fin n))
    (hp : bankTrialC5PendingAfterBool ring root S z word =
      true) :
    ¬ bankTrialLocalTerminal
      (bankTrialLocalRun ring root (pre ++ word)
        (bankTrialLocalStart S)) := by
  obtain ⟨hfirst, hnone⟩ :=
    bankTrialSuccessPendingAfterFirstExitNone
      ring root S z word hp
  exact bankTrialSuccessArmedFirstOutgoingNoneOfCredit
    ring root S hlarge hclean word pre z begun
    hz hlive hm hcredit hfirst hnone

/-- Pending-BEFORE is nonterminal under the same credit
disjunction, including the original unbegun CLEAN seed. -/
theorem bankTrialSuccessArmedPendingBeforeOfCredit
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (z : BankTrialLocalState q)
    (begun : Bool)
    (hz : z = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hlive : z.phase = .live begun)
    (hm : bankTrialLiveWaveRootMode z.bank = .ARMED)
    (hcredit : begun = false ∨
      0 < bankTrialLiveCarryValue z.bank)
    (word : List (Fin n))
    (hp : bankTrialC5PendingBeforeBool ring root S z word =
      true) :
    ¬ bankTrialLocalTerminal
      (bankTrialLocalRun ring root (pre ++ word)
        (bankTrialLocalStart S)) := by
  have hnone :
      bankTrialProbabilityFirstIncidentOrientation
        root (ring.leftNeighbor root) word = none := by
    by_cases h :
        bankTrialProbabilityFirstIncidentOrientation
          root (ring.leftNeighbor root) word = none
    · exact h
    · have hfalse :
          bankTrialC5PendingBeforeBool ring root S z word =
            false := by
        simp [bankTrialC5PendingBeforeBool, h]
      rw [hfalse] at hp
      cases hp
  rw [bankTrialLocalRunAppend, ← hz]
  rcases hcredit with hfalse | hpos
  · subst begun
    have hf : z.bank.success = false :=
      (bankTrialSuccessReachableArmedStart
        ring root S hlarge hclean pre z hz
        ⟨⟨false, hlive⟩, hm⟩).2.2.2.1
    have hrun := bankTrialSuccessUnbegunArmedBeforeIncident
      ring root word z hlive hf hm hnone
    intro ht
    rcases ht with hw | hl
    · rw [hrun.1] at hw
      cases hw
    · rw [hrun.1] at hl
      cases hl
  · have hrun := bankTrialSuccessPositiveArmedBeforeIncident
      ring root S (bankTrialProbabilityUpperWindow hlarge)
      hclean word pre z begun hz hlive hm hpos hnone
    intro ht
    rcases ht with hw | hl
    · rw [hrun.1] at hw
      cases hw
    · rw [hrun.1] at hl
      cases hl

/-- Full ARMED stage pending, BEFORE or AFTER: the exact
unmodified stage predicate is used. -/
theorem bankTrialSuccessArmedStagePendingOfCredit
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (z : BankTrialLocalState q)
    (begun : Bool)
    (hz : z = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hlive : z.phase = .live begun)
    (hm : bankTrialLiveWaveRootMode z.bank = .ARMED)
    (hcredit : begun = false ∨
      0 < bankTrialLiveCarryValue z.bank)
    (word : List (Fin n))
    (hp : bankTrialSuccessGoodReturnStagePendingAt
      ring root S z word = true) :
    ¬ bankTrialLocalTerminal
      (bankTrialLocalRun ring root (pre ++ word)
        (bankTrialLocalStart S)) := by
  have hnotCStart :
      bankTrialLiveWaveRootMode z.bank ≠ .CSTART := by
    rw [hm]
    intro hh
    cases hh
  have hgate : BankTrialProbabilityArmedGate z :=
    ⟨⟨begun, hlive⟩, hm⟩
  have hor :
      bankTrialC5PendingBeforeBool ring root S z word = true ∨
      bankTrialC5PendingAfterBool ring root S z word = true := by
    have hraw :
        (bankTrialC5PendingBeforeBool ring root S z word ||
          bankTrialC5PendingAfterBool ring root S z word) =
            true := by
      simpa only [bankTrialSuccessGoodReturnStagePendingAt,
        if_neg hnotCStart, if_pos hgate] using hp
    cases hb : bankTrialC5PendingBeforeBool ring root S z word with
    | true =>
        exact Or.inl rfl
    | false =>
        cases ha : bankTrialC5PendingAfterBool ring root S z word with
        | true =>
            exact Or.inr rfl
        | false =>
            rw [hb, ha] at hraw
            cases hraw
  rcases hor with hb | ha
  · exact bankTrialSuccessArmedPendingBeforeOfCredit
      ring root S hlarge hclean pre z begun
      hz hlive hm hcredit word hb
  · exact bankTrialSuccessArmedPendingAfterOfCredit
      ring root S hlarge hclean pre z begun
      hz hlive hm hcredit word ha

/-- Positive-index stage cuts that are LIVE/ARMED have the
needed carry credit without an additional hypothesis: the
actual cut HEAD count is positive, and the completed
head invariant identifies it with the current BANK carry. -/
theorem bankTrialSuccessNonzeroArmedCutCarryPositive
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (j : Nat) (begun : Bool)
    (hstop : bankTrialSuccessGoodReturnCutBool
      ring root S (j + 1) pre
        (bankTrialLocalRun ring root pre
          (bankTrialLocalStart S)) = true)
    (hlive : (bankTrialLocalRun ring root pre
      (bankTrialLocalStart S)).phase = .live begun) :
    0 < bankTrialLiveCarryValue
      (bankTrialLocalRun ring root pre
        (bankTrialLocalStart S)).bank := by
  have hheads := bankTrialSuccessNonzeroCutBoolHeadsPositive
    ring root S hsp hlarge hwidth hclean pre j hstop
  have hK : 0 < (compileAdvice q).K :=
    Counter.resetColdPrivateKPositive q hsp
  have hstep : BankTrialC5CompletedHeadEdgePreservation
      ring root S :=
    bankTrialC5CompletedHeadEdgePreservationOfRows
      ring root S
      (bankTrialC5RemainingLiveRowsHolds ring root hlarge hwidth)
  have hInv := bankTrialC5CompletedHeadInvariantWordsOfStep
    ring root S hlarge hwidth hclean
    (bankTrialC5CompletedHeadInvariantStart S hK hclean)
    hstep pre
  rw [hInv.liveCarry begun hlive]
  exact hheads

/-- The real first-stopped stage event is nonterminal whenever
its reached cut is LIVE and has the advertised ARMED or CSTART
mode. For positive indices, ARMED credit follows from the
stop predicate and the actual HEAD-count ledger. -/
theorem bankTrialSuccessNonzeroLiveCutStagePendingNonterminal
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre word : List (Fin n)) (j : Nat) (begun : Bool)
    (hstop : bankTrialSuccessGoodReturnCutBool
      ring root S (j + 1) pre
        (bankTrialLocalRun ring root pre
          (bankTrialLocalStart S)) = true)
    (hlive : (bankTrialLocalRun ring root pre
      (bankTrialLocalStart S)).phase = .live begun)
    (hmodes :
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root pre
          (bankTrialLocalStart S)).bank = .ARMED ∨
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root pre
          (bankTrialLocalStart S)).bank = .CSTART)
    (hp : bankTrialSuccessGoodReturnStagePendingAt
      ring root S
      (bankTrialLocalRun ring root pre
        (bankTrialLocalStart S)) word = true) :
    ¬ bankTrialLocalTerminal
      (bankTrialLocalRun ring root (pre ++ word)
        (bankTrialLocalStart S)) := by
  rcases hmodes with hm | hc
  · have hpos := bankTrialSuccessNonzeroArmedCutCarryPositive
      ring root S hsp hlarge hwidth hclean
      pre j begun hstop hlive
    exact bankTrialSuccessArmedStagePendingOfCredit
      ring root S hlarge hclean pre
      (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
      begun rfl hlive hm (Or.inr hpos) word hp
  · exact bankTrialSuccessCStartPendingActualWordNonterminal
      ring root S hlarge hclean pre word begun hlive hc hp

/-!
The remainder establishes suffix-extension consistency of the
earliest GOOD return and of the recursive cut family. This
gives a genuine prefix-free first-stopped cut, but the reverse
self-recognition and terminal-cut mode lemmas remain separate.
-/

/-- Once the accumulated scanner has observed GOOD on its first
worker, appending later scheduler letters cannot alter its
earliest recorded successful prefix. -/
theorem bankTrialSuccessFirstGoodPrefixAppend
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (x : BankTrialLocalState q) :
    ∀ (word acc found more : List (Fin n)),
      bankTrialSuccessFirstGoodReturnPrefix
        ring root S x acc word = some found →
      bankTrialSuccessFirstGoodReturnPrefix
        ring root S x acc (word ++ more) = some found := by
  intro word
  induction word with
  | nil =>
      intro acc found more hfound
      by_cases hg :
          bankTrialC5PostHeadFirstExit ring root S acc x =
            some true
      · have hsome : some acc = some found := by
          simpa only [bankTrialSuccessFirstGoodReturnPrefix,
            if_pos hg] using hfound
        have heq : acc = found := Option.some.inj hsome
        rw [← heq]
        cases more with
        | nil =>
            simp only [List.nil_append,
              bankTrialSuccessFirstGoodReturnPrefix, if_pos hg]
        | cons e tail =>
            simp only [List.nil_append,
              bankTrialSuccessFirstGoodReturnPrefix, if_pos hg]
      · simp only [bankTrialSuccessFirstGoodReturnPrefix,
          if_neg hg] at hfound
        cases hfound
  | cons e tail ih =>
      intro acc found more hfound
      by_cases hg :
          bankTrialC5PostHeadFirstExit ring root S acc x =
            some true
      · have hsome : some acc = some found := by
          simpa only [bankTrialSuccessFirstGoodReturnPrefix,
            if_pos hg] using hfound
        have heq : acc = found := Option.some.inj hsome
        rw [← heq]
        simp only [List.cons_append,
          bankTrialSuccessFirstGoodReturnPrefix, if_pos hg]
      · have ht :
            bankTrialSuccessFirstGoodReturnPrefix
              ring root S x (acc ++ [e]) tail = some found := by
          simpa only [bankTrialSuccessFirstGoodReturnPrefix,
            if_neg hg] using hfound
        have hext := ih (acc ++ [e]) found more ht
        simpa only [List.cons_append,
          bankTrialSuccessFirstGoodReturnPrefix, if_neg hg]
          using hext

/-- Core List identity used by the recursive cut: the suffix
after a known prefix is exactly the physical remaining tape. -/
theorem bankTrialSuccessDropPrefixAppend
    {α : Type} (pre suffix : List α) :
    (pre ++ suffix).drop pre.length = suffix := by
  induction pre with
  | nil =>
      rfl
  | cons e rest ih =>
      change (rest ++ suffix).drop rest.length = suffix
      exact ih

/-- Suffix-extension consistency for ALL recursive good-return
cut indices. This makes the prefix-based stop test stable:
later tape letters cannot retroactively change a finished cut. -/
theorem bankTrialSuccessGoodReturnCutAppend
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    ∀ (j : Nat) (word cut more : List (Fin n)),
      bankTrialSuccessGoodReturnCutPrefix
        ring root S word j = some cut →
      bankTrialSuccessGoodReturnCutPrefix
        ring root S (word ++ more) j = some cut := by
  intro j
  induction j with
  | zero =>
      intro word cut more hcut
      have hsome : some ([] : List (Fin n)) = some cut := by
        simpa only [bankTrialSuccessGoodReturnCutPrefix] using hcut
      have heq : [] = cut := Option.some.inj hsome
      rw [← heq]
      rfl
  | succ j ih =>
      intro word cut more hcut
      cases hprev :
          bankTrialSuccessGoodReturnCutPrefix
            ring root S word j with
      | none =>
          simp only [bankTrialSuccessGoodReturnCutPrefix,
            hprev] at hcut
          cases hcut
      | some prev =>
          obtain ⟨suffix, hword⟩ :=
            bankTrialSuccessGoodReturnCutIsPrefix
              ring root S word j prev hprev
          have hprevMore := ih word prev more hprev
          cases hscan :
              bankTrialSuccessFirstGoodReturnPrefix
                ring root S
                (bankTrialLocalRun ring root prev
                  (bankTrialLocalStart S))
                [] (word.drop prev.length) with
          | none =>
              simp only [bankTrialSuccessGoodReturnCutPrefix,
                hprev, hscan] at hcut
              cases hcut
          | some segment =>
              have hsome : some (prev ++ segment) = some cut := by
                simpa only [bankTrialSuccessGoodReturnCutPrefix,
                  hprev, hscan] using hcut
              have heq : prev ++ segment = cut :=
                Option.some.inj hsome
              have hdropOld : word.drop prev.length = suffix := by
                rw [hword]
                exact bankTrialSuccessDropPrefixAppend prev suffix
              have hdropMore :
                  (word ++ more).drop prev.length =
                    suffix ++ more := by
                rw [hword, List.append_assoc]
                exact bankTrialSuccessDropPrefixAppend
                  prev (suffix ++ more)
              have hscanOld :
                  bankTrialSuccessFirstGoodReturnPrefix
                    ring root S
                    (bankTrialLocalRun ring root prev
                      (bankTrialLocalStart S))
                    [] suffix = some segment := by
                rw [← hdropOld]
                exact hscan
              have hscanMore :=
                bankTrialSuccessFirstGoodPrefixAppend
                  ring root S
                  (bankTrialLocalRun ring root prev
                    (bankTrialLocalStart S))
                  suffix [] segment more hscanOld
              have hfullScan :
                  bankTrialSuccessFirstGoodReturnPrefix
                    ring root S
                    (bankTrialLocalRun ring root prev
                      (bankTrialLocalStart S))
                    [] ((word ++ more).drop prev.length) =
                      some segment := by
                rw [hdropMore]
                exact hscanMore
              rw [← heq]
              simp only [bankTrialSuccessGoodReturnCutPrefix,
                hprevMore, hfullScan]

/-- The actual prefix stop test is prefix-free: two successful
stops at u and u++v can coexist only when v is empty. -/
theorem bankTrialSuccessGoodReturnCutPrefixFree
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j : Nat) :
    Prob.StoppedPrefixFree
      (bankTrialLocalNext ring root)
      (bankTrialSuccessGoodReturnCutBool ring root S j)
      (bankTrialLocalStart S) := by
  intro u v hu huv
  have huCut :
      bankTrialSuccessGoodReturnCutPrefix
        ring root S u j = some u := by
    exact of_decide_eq_true
      (show decide
        (bankTrialSuccessGoodReturnCutPrefix
          ring root S u j = some u) = true from hu)
  have huvCut :
      bankTrialSuccessGoodReturnCutPrefix
        ring root S (u ++ v) j = some (u ++ v) := by
    exact of_decide_eq_true
      (show decide
        (bankTrialSuccessGoodReturnCutPrefix
          ring root S (u ++ v) j = some (u ++ v)) = true from huv)
  have hstable := bankTrialSuccessGoodReturnCutAppend
    ring root S j u u v huCut
  have heq : u = u ++ v :=
    Option.some.inj (hstable.symm.trans huvCut)
  cases v with
  | nil =>
      rfl
  | cons e tail =>
      have hlen := congrArg List.length heq
      simp only [List.length_append, List.length_cons] at hlen
      omega

end L3


namespace L3

/- The next lemmas do not identify a GOOD return with a completed
   HEAD.  They only locate the physical state at its FIRST
   recognition by the installed first-origin scanner. -/

theorem bankTrialSuccessWorkerFirstGoodAtLast
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (o : BankTrialC5ActualOrigin n q) :
    ∀ (pre : List (Fin n)) (z : BankTrialLocalState q)
      (e : Fin n),
      bankTrialC5WorkerFirstExit ring root o pre z ≠ some true →
      bankTrialC5WorkerFirstExit ring root o (pre ++ [e]) z =
        some true →
      bankTrialC5ActualReturned o
        (bankTrialLocalRun ring root (pre ++ [e]) z) := by
  intro pre
  induction pre with
  | nil =>
      intro z e hno hyes
      by_cases hr : bankTrialC5ActualReturned o z
      · exact False.elim (hno (by simp [bankTrialC5WorkerFirstExit, hr]))
      · by_cases hb : bankTrialC5ActualBadExit o z
        · have hf :
              bankTrialC5WorkerFirstExit ring root o ([] ++ [e]) z =
                some false := by
            simp [bankTrialC5WorkerFirstExit, hr, hb]
          rw [hf] at hyes
          cases hyes
        · have ht :
              bankTrialC5WorkerFirstExit ring root o []
                (bankTrialLocalNext ring root z e) = some true := by
            simpa [bankTrialC5WorkerFirstExit, hr, hb] using hyes
          have hret :
              bankTrialC5ActualReturned o
                (bankTrialLocalNext ring root z e) := by
            by_cases hnext :
                bankTrialC5ActualReturned o
                  (bankTrialLocalNext ring root z e)
            · exact hnext
            · simp only [bankTrialC5WorkerFirstExit,
                if_neg hnext] at ht
              split at ht <;> cases ht
          exact hret
  | cons a tail ih =>
      intro z e hno hyes
      by_cases hr : bankTrialC5ActualReturned o z
      · exact False.elim (hno (by simp [bankTrialC5WorkerFirstExit, hr]))
      · by_cases hb : bankTrialC5ActualBadExit o z
        · have hf :
              bankTrialC5WorkerFirstExit ring root o
                ((a :: tail) ++ [e]) z = some false := by
            simp [bankTrialC5WorkerFirstExit, hr, hb]
          rw [hf] at hyes
          cases hyes
        · have hnoTail :
              bankTrialC5WorkerFirstExit ring root o tail
                (bankTrialLocalNext ring root z a) ≠ some true := by
            intro ht
            apply hno
            simpa [bankTrialC5WorkerFirstExit, hr, hb] using ht
          have hyesTail :
              bankTrialC5WorkerFirstExit ring root o (tail ++ [e])
                (bankTrialLocalNext ring root z a) = some true := by
            simpa [bankTrialC5WorkerFirstExit, hr, hb] using hyes
          exact ih (bankTrialLocalNext ring root z a)
            e hnoTail hyesTail

theorem bankTrialSuccessPostHeadFirstGoodAtLast
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    ∀ (pre : List (Fin n)) (z : BankTrialLocalState q)
      (e : Fin n),
      bankTrialC5PostHeadFirstExit ring root S pre z ≠ some true →
      bankTrialC5PostHeadFirstExit ring root S (pre ++ [e]) z =
        some true →
      ∃ o : BankTrialC5ActualOrigin n q,
        bankTrialC5ActualReturned o
          (bankTrialLocalRun ring root (pre ++ [e]) z) := by
  intro pre
  induction pre with
  | nil =>
      intro z e _ hyes
      cases hstarts : bankTrialC5ActualStarts ring root S z e with
      | nil =>
          simp [bankTrialC5PostHeadFirstExit, hstarts] at hyes
      | cons o others =>
          have ht :
              bankTrialC5WorkerFirstExit ring root o []
                (bankTrialLocalNext ring root z e) = some true := by
            simpa [bankTrialC5PostHeadFirstExit, hstarts] using hyes
          have hr :
              bankTrialC5ActualReturned o
                (bankTrialLocalNext ring root z e) := by
            by_cases hret :
                bankTrialC5ActualReturned o
                  (bankTrialLocalNext ring root z e)
            · exact hret
            · simp only [bankTrialC5WorkerFirstExit,
                if_neg hret] at ht
              split at ht <;> cases ht
          exact ⟨o, hr⟩
  | cons a tail ih =>
      intro z e hno hyes
      cases hstarts : bankTrialC5ActualStarts ring root S z a with
      | nil =>
          have hnoTail :
              bankTrialC5PostHeadFirstExit ring root S tail
                (bankTrialLocalNext ring root z a) ≠ some true := by
            intro ht
            apply hno
            simpa [bankTrialC5PostHeadFirstExit, hstarts] using ht
          have hyesTail :
              bankTrialC5PostHeadFirstExit ring root S (tail ++ [e])
                (bankTrialLocalNext ring root z a) = some true := by
            simpa [bankTrialC5PostHeadFirstExit, hstarts] using hyes
          exact ih (bankTrialLocalNext ring root z a)
            e hnoTail hyesTail
      | cons o others =>
          have hnoTail :
              bankTrialC5WorkerFirstExit ring root o tail
                (bankTrialLocalNext ring root z a) ≠ some true := by
            intro ht
            apply hno
            simpa [bankTrialC5PostHeadFirstExit, hstarts] using ht
          have hyesTail :
              bankTrialC5WorkerFirstExit ring root o (tail ++ [e])
                (bankTrialLocalNext ring root z a) = some true := by
            simpa [bankTrialC5PostHeadFirstExit, hstarts] using hyes
          exact ⟨o, bankTrialSuccessWorkerFirstGoodAtLast
            ring root o tail (bankTrialLocalNext ring root z a)
            e hnoTail hyesTail⟩

theorem bankTrialSuccessGoodAccumulatorReturned
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (x : BankTrialLocalState q)
    (acc : List (Fin n))
    (hg : bankTrialC5PostHeadFirstExit ring root S acc x =
      some true)
    (hminimal : acc = [] ∨
      ∃ (prev : List (Fin n)) (e : Fin n),
        acc = prev ++ [e] ∧
        bankTrialC5PostHeadFirstExit ring root S prev x ≠
          some true) :
    ∃ o : BankTrialC5ActualOrigin n q,
      bankTrialC5ActualReturned o
        (bankTrialLocalRun ring root acc x) := by
  rcases hminimal with hnil | ⟨prev, e, heq, hno⟩
  · rw [hnil] at hg
    simp only [bankTrialC5PostHeadFirstExit] at hg
    cases hg
  · rw [heq] at hg ⊢
    exact bankTrialSuccessPostHeadFirstGoodAtLast
      ring root S prev x e hno hg

theorem bankTrialSuccessFirstGoodReturned
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (x : BankTrialLocalState q) :
    ∀ (remaining acc found : List (Fin n)),
      (acc = [] ∨
        ∃ (prev : List (Fin n)) (e : Fin n),
          acc = prev ++ [e] ∧
          bankTrialC5PostHeadFirstExit ring root S prev x ≠
            some true) →
      bankTrialSuccessFirstGoodReturnPrefix
        ring root S x acc remaining = some found →
      ∃ o : BankTrialC5ActualOrigin n q,
        bankTrialC5ActualReturned o
          (bankTrialLocalRun ring root found x) := by
  intro remaining
  induction remaining with
  | nil =>
      intro acc found hminimal hfound
      by_cases hg :
          bankTrialC5PostHeadFirstExit ring root S acc x =
            some true
      · have heq : acc = found := Option.some.inj (by
          simpa only [bankTrialSuccessFirstGoodReturnPrefix,
            if_pos hg] using hfound)
        rw [← heq]
        exact bankTrialSuccessGoodAccumulatorReturned
          ring root S x acc hg hminimal
      · simp only [bankTrialSuccessFirstGoodReturnPrefix,
          if_neg hg] at hfound
        cases hfound
  | cons e tail ih =>
      intro acc found hminimal hfound
      by_cases hg :
          bankTrialC5PostHeadFirstExit ring root S acc x =
            some true
      · have heq : acc = found := Option.some.inj (by
          simpa only [bankTrialSuccessFirstGoodReturnPrefix,
            if_pos hg] using hfound)
        rw [← heq]
        exact bankTrialSuccessGoodAccumulatorReturned
          ring root S x acc hg hminimal
      · have htail :
            bankTrialSuccessFirstGoodReturnPrefix ring root S x
              (acc ++ [e]) tail = some found := by
          simpa only [bankTrialSuccessFirstGoodReturnPrefix,
            if_neg hg] using hfound
        exact ih (acc ++ [e]) found
          (Or.inr ⟨acc, e, rfl, hg⟩) htail

theorem bankTrialSuccessPositiveGoodCutReturned
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word cut : List (Fin n)) (j : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word (j + 1) = some cut) :
    ∃ o : BankTrialC5ActualOrigin n q,
      bankTrialC5ActualReturned o
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)) := by
  cases hprev :
      bankTrialSuccessGoodReturnCutPrefix ring root S word j with
  | none =>
      simp only [bankTrialSuccessGoodReturnCutPrefix,
        hprev] at hcut
      cases hcut
  | some prev =>
      cases hfirst :
          bankTrialSuccessFirstGoodReturnPrefix ring root S
            (bankTrialLocalRun ring root prev
              (bankTrialLocalStart S))
            [] (word.drop prev.length) with
      | none =>
          simp only [bankTrialSuccessGoodReturnCutPrefix,
            hprev, hfirst] at hcut
          cases hcut
      | some segment =>
          have heq : prev ++ segment = cut := Option.some.inj (by
            simpa only [bankTrialSuccessGoodReturnCutPrefix,
              hprev, hfirst] using hcut)
          obtain ⟨o, hret⟩ := bankTrialSuccessFirstGoodReturned
            ring root S
            (bankTrialLocalRun ring root prev (bankTrialLocalStart S))
            (word.drop prev.length) [] segment (Or.inl rfl)
            hfirst
          refine ⟨o, ?_⟩
          rw [← heq, bankTrialLocalRunAppend]
          exact hret

/-- A positive chronological cut cannot be RESET, RECOVERY,
    IWAIT, CWAIT, RWAIT, or LOST.  It is exactly one of the
    three outcome shapes built into ActualReturned. -/
theorem bankTrialSuccessPositiveGoodCutClasses
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word cut : List (Fin n)) (j : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word (j + 1) = some cut) :
    (∃ begun : Bool,
      (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S)).phase = .live begun ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)).bank = .ARMED) ∨
    (∃ begun : Bool,
      (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S)).phase = .live begun ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)).bank = .CSTART) ∨
    (bankTrialLocalRun ring root cut
      (bankTrialLocalStart S)).phase = .won := by
  obtain ⟨o, hreturned⟩ :=
    bankTrialSuccessPositiveGoodCutReturned
      ring root S word cut j hcut
  cases hi : o.increment with
  | true =>
      simp only [bankTrialC5ActualReturned, hi,
        ↓reduceIte] at hreturned
      exact Or.inr (Or.inl hreturned)
  | false =>
      simp only [bankTrialC5ActualReturned, hi,
        Bool.false_eq_true, ↓reduceIte] at hreturned
      rcases hreturned with harmed | hwon
      · obtain ⟨begun, hphase, hmode, _, _, _, _⟩ := harmed.2
        exact Or.inl ⟨begun, hphase, hmode⟩
      · exact Or.inr (Or.inr hwon.2)

/-- The clean stage-zero stop is LIVE/ARMED without a
    separate head-count premise. -/
theorem bankTrialSuccessZeroStagePendingNonterminal
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (T : Nat) (word : List (Fin n))
    (hp : bankTrialSuccessGoodReturnStagePendingBool
      ring root S 0 T word = true) :
    ¬ bankTrialLocalTerminal
        (bankTrialLocalRun ring root word
          (bankTrialLocalStart S)) := by
  have hm :
      bankTrialLiveWaveRootMode (bankTrialLocalStart S).bank =
        .ARMED := hclean.2.1
  have hp0 :
      bankTrialSuccessGoodReturnStagePendingAt
        ring root S (bankTrialLocalStart S) word = true := by
    rw [bankTrialSuccessGoodReturnStageZeroExact
      ring root S T word] at hp
    exact hp
  have hn := bankTrialSuccessArmedStagePendingOfCredit
    ring root S hlarge hclean []
    (bankTrialLocalStart S) false rfl rfl hm
    (Or.inl rfl) word hp0
  simpa only [List.nil_append] using hn

/-- Pure Boolean consequence in the terminal class.  Establishing
    the mode exclusion for a CLEAN-reachable WON cut is the
    remaining physical-row obligation. -/
theorem bankTrialSuccessWonStagePendingFalseOfNonCStart
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (z : BankTrialLocalState q) (word : List (Fin n))
    (hwon : z.phase = .won)
    (hm : bankTrialLiveWaveRootMode z.bank ≠ .CSTART) :
    bankTrialSuccessGoodReturnStagePendingAt
      ring root S z word = false := by
  have hgate : ¬ BankTrialProbabilityArmedGate z := by
    rintro ⟨⟨begun, hlive⟩, _⟩
    rw [hwon] at hlive
    cases hlive
  simp [bankTrialSuccessGoodReturnStagePendingAt, hm, hgate]

/-- The remaining-positive-cut bridge conditional on the single
    terminal root-mode exclusion.  No classification premise for
    LIVE states is needed. -/
theorem bankTrialSuccessPositiveCutPendingOfWonMode
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre word : List (Fin n)) (j : Nat)
    (hstop : bankTrialSuccessGoodReturnCutBool
      ring root S (j + 1) pre
        (bankTrialLocalRun ring root pre
          (bankTrialLocalStart S)) = true)
    (hwonmode :
      (bankTrialLocalRun ring root pre
        (bankTrialLocalStart S)).phase = .won →
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root pre
          (bankTrialLocalStart S)).bank ≠ .CSTART)
    (hp : bankTrialSuccessGoodReturnStagePendingAt
      ring root S
      (bankTrialLocalRun ring root pre
        (bankTrialLocalStart S)) word = true) :
    ¬ bankTrialLocalTerminal
      (bankTrialLocalRun ring root (pre ++ word)
        (bankTrialLocalStart S)) := by
  have hcut :
      bankTrialSuccessGoodReturnCutPrefix
        ring root S pre (j + 1) = some pre :=
    of_decide_eq_true (by
      simpa only [bankTrialSuccessGoodReturnCutBool] using hstop)
  rcases bankTrialSuccessPositiveGoodCutClasses
      ring root S pre pre j hcut with
    ⟨begun, hlive, hm⟩ | ⟨begun, hlive, hm⟩ | hwon
  · exact bankTrialSuccessNonzeroLiveCutStagePendingNonterminal
      ring root S hsp hlarge hwidth hclean
      pre word j begun hstop hlive (Or.inl hm) hp
  · exact bankTrialSuccessNonzeroLiveCutStagePendingNonterminal
      ring root S hsp hlarge hwidth hclean
      pre word j begun hstop hlive (Or.inr hm) hp
  · have hf := bankTrialSuccessWonStagePendingFalseOfNonCStart
      ring root S
      (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
      word hwon (hwonmode hwon)
    rw [hf] at hp
    cases hp

/-- The stopped-prefix operator really presents a suffix at a
    reached authenticated cut; no resampling or exact-length
    assumption on the input word is used. -/
theorem bankTrialSuccessStopPendingWitness
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j : Nat) :
    ∀ (word : List (Fin n)) (T : Nat)
      (pre : List (Fin n)) (z : BankTrialLocalState q),
      z = bankTrialLocalRun ring root pre (bankTrialLocalStart S) →
      Prob.firstStoppedSuffixWord (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        (fun x _ suffix =>
          bankTrialSuccessGoodReturnStagePendingAt
            ring root S x suffix)
        T pre z word = true →
      ∃ used suffix : List (Fin n),
        word = used ++ suffix ∧
        bankTrialSuccessGoodReturnCutBool ring root S j
          (pre ++ used)
          (bankTrialLocalRun ring root (pre ++ used)
            (bankTrialLocalStart S)) = true ∧
        bankTrialSuccessGoodReturnStagePendingAt ring root S
          (bankTrialLocalRun ring root (pre ++ used)
            (bankTrialLocalStart S)) suffix = true := by
  intro word
  induction word with
  | nil =>
      intro T pre z hz hp
      cases hs :
          bankTrialSuccessGoodReturnCutBool ring root S j pre z with
      | true =>
          have hpend :
              bankTrialSuccessGoodReturnStagePendingAt
                ring root S z [] = true := by
            simpa [Prob.firstStoppedSuffixWord, hs] using hp
          refine ⟨[], [], rfl, ?_, ?_⟩
          · simpa only [List.append_nil, ← hz] using hs
          · simpa only [List.append_nil, ← hz] using hpend
      | false =>
          simp [Prob.firstStoppedSuffixWord, hs] at hp
  | cons e tail ih =>
      intro T pre z hz hp
      cases hs :
          bankTrialSuccessGoodReturnCutBool ring root S j pre z with
      | true =>
          have hpend :
              bankTrialSuccessGoodReturnStagePendingAt
                ring root S z (e :: tail) = true := by
            simpa [Prob.firstStoppedSuffixWord, hs] using hp
          refine ⟨[], e :: tail, rfl, ?_, ?_⟩
          · simpa only [List.append_nil, ← hz] using hs
          · simpa only [List.append_nil, ← hz] using hpend
      | false =>
          have htail :
              Prob.firstStoppedSuffixWord
                (bankTrialLocalNext ring root)
                (bankTrialSuccessGoodReturnCutBool ring root S j)
                (fun x _ suffix =>
                  bankTrialSuccessGoodReturnStagePendingAt
                    ring root S x suffix)
                (T - 1) (pre ++ [e])
                (bankTrialLocalNext ring root z e) tail = true := by
            simpa [Prob.firstStoppedSuffixWord, hs] using hp
          have hznext :
              bankTrialLocalNext ring root z e =
                bankTrialLocalRun ring root (pre ++ [e])
                  (bankTrialLocalStart S) := by
            rw [bankTrialLocalRunAppend, ← hz]
            rfl
          obtain ⟨used, suffix, hword, hstop, hpend⟩ :=
            ih (T - 1) (pre ++ [e])
              (bankTrialLocalNext ring root z e) hznext htail
          refine ⟨e :: used, suffix, ?_, ?_, ?_⟩
          · simpa only [List.cons_append] using
              congrArg (List.cons e) hword
          · simpa only [List.append_assoc,
              List.singleton_append] using hstop
          · simpa only [List.append_assoc,
              List.singleton_append] using hpend

/-- This is the full stage-Boolean to final-horizon bridge, with
    only the as-yet-unproved reachable-WON mode exclusion exposed.
    The original word and the original scheduler are preserved. -/
theorem bankTrialSuccessStagePendingFinalOfWonMode
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hwonmode : ∀ pre : List (Fin n),
      (bankTrialLocalRun ring root pre
        (bankTrialLocalStart S)).phase = .won →
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root pre
          (bankTrialLocalStart S)).bank ≠ .CSTART)
    (j T : Nat) (word : List (Fin n))
    (hp : bankTrialSuccessGoodReturnStagePendingBool
      ring root S j T word = true) :
    bankTrialSuccessFinalNonterminalBool ring root S word =
      true := by
  cases j with
  | zero =>
      have hn := bankTrialSuccessZeroStagePendingNonterminal
        ring root S hlarge hclean T word hp
      simp [bankTrialSuccessFinalNonterminalBool, hn]
  | succ j =>
      have hraw :
          Prob.firstStoppedSuffixWord (bankTrialLocalNext ring root)
            (bankTrialSuccessGoodReturnCutBool ring root S (j + 1))
            (fun x _ suffix =>
              bankTrialSuccessGoodReturnStagePendingAt
                ring root S x suffix)
            T [] (bankTrialLocalStart S) word = true := by
        simpa only [bankTrialSuccessGoodReturnStagePendingBool]
          using hp
      obtain ⟨used, suffix, hword, hstop, hpend⟩ :=
        bankTrialSuccessStopPendingWitness
          ring root S (j + 1) word T []
          (bankTrialLocalStart S) rfl hraw
      have hn := bankTrialSuccessPositiveCutPendingOfWonMode
        ring root S hsp hlarge hwidth hclean
        used suffix j
        (by simpa only [List.nil_append] using hstop)
        (hwonmode used)
        hpend
      have hfinal :
          ¬ bankTrialLocalTerminal
            (bankTrialLocalRun ring root word
              (bankTrialLocalStart S)) := by
        rw [hword]
        exact hn
      simp [bankTrialSuccessFinalNonterminalBool, hfinal]

end L3


namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A newly raised clamped success latch is caused by the old
CWAIT/CL1 root-outgoing acceptance guard. The physical bankPair
therefore writes RESET at the root on that very same service. -/
theorem bankTrialSuccessFreshSuccessRootReset
    {n q : Nat} (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hs : (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).success = true) :
    bankTrialLiveWaveRootMode
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) = .RESET := by
  have hwon :
      (bankTrialLocalNext ring root
        (⟨B, .live false⟩ : BankTrialLocalState q) e).phase =
          .won := by
    simp [bankTrialLocalNext, hs]
  obtain ⟨he, hm, ht⟩ :=
    bankTrialProbabilityLiveWonRequiresOldGuard
      ring root e B false hf hwon
  subst e
  have hraw := bankTrialDurationRawRootCLTrueReturn
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell
      B ⟨0, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell
      B ⟨1, by have hb := bankTrialCmpWidth q; omega⟩)
    (by have hb := bankTrialCmpWidth q; omega)
    rfl rfl rfl
    (show (B.fields ⟨0, by omega⟩).1 = .CWAIT from hm)
    (show (B.fields
      ⟨1, by have hb := bankTrialCmpWidth q; omega⟩).2.2.1 =
        .CL1 from ht)
  exact (bankTrialCmpRoot ring root hw B hf).1.trans hraw.1

/-- The latch-to-RESET implication is inductive at the clamped
reference level, including the already-latched absorbing case. -/
theorem bankTrialSuccessReferenceLatchResetStep
    {n q : Nat} (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hprev : B.success = true →
      bankTrialLiveWaveRootMode B = .RESET)
    (hpost : (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).success = true) :
    bankTrialLiveWaveRootMode
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) = .RESET := by
  by_cases hlatched : B.success = true
  · have hsame :
        GrantBankReference.bankLocalReferenceStepClamped
          ring root B e = B := by
      simp [GrantBankReference.bankLocalReferenceStepClamped,
        hlatched]
    rw [hsame]
    exact hprev hlatched
  · have hf : B.success = false := by
      cases hb : B.success with
      | false => rfl
      | true => exact False.elim (hlatched hb)
    exact bankTrialSuccessFreshSuccessRootReset
      ring root e hw B hf hpost

/-- The observer copies the clamped bank while active and preserves
the entire bank in either absorbing terminal phase. -/
theorem bankTrialSuccessLocalLatchResetStep
    {n q : Nat} (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q)
    (hprev : z.bank.success = true →
      bankTrialLiveWaveRootMode z.bank = .RESET) :
    (bankTrialLocalNext ring root z e).bank.success = true →
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root z e).bank = .RESET := by
  cases z with
  | mk B phase =>
      cases phase with
      | live begun =>
          rw [bankTrialLocalNextLiveBank ring root e B begun]
          exact bankTrialSuccessReferenceLatchResetStep
            ring root e hw B hprev
      | recovery =>
          rw [bankTrialLocalNextRecoveryBank ring root e B]
          exact bankTrialSuccessReferenceLatchResetStep
            ring root e hw B hprev
      | won =>
          rw [bankTrialLocalTerminalAbsorbs ring root e
            (⟨B, .won⟩ : BankTrialLocalState q) (Or.inl rfl)]
          exact hprev
      | lost =>
          rw [bankTrialLocalTerminalAbsorbs ring root e
            (⟨B, .lost⟩ : BankTrialLocalState q) (Or.inr rfl)]
          exact hprev

/-- The latch-to-RESET invariant holds after an arbitrary physical
scheduler word, with no assumption about observer phase at its end. -/
theorem bankTrialSuccessRunLatchedReset
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q) :
    ∀ (word : List (Fin n)) (z : BankTrialLocalState q),
      (z.bank.success = true →
        bankTrialLiveWaveRootMode z.bank = .RESET) →
      (bankTrialLocalRun ring root word z).bank.success = true →
        bankTrialLiveWaveRootMode
          (bankTrialLocalRun ring root word z).bank = .RESET := by
  intro word
  induction word with
  | nil =>
      intro z hprev
      exact hprev
  | cons e tail ih =>
      intro z hprev
      exact ih (bankTrialLocalNext ring root z e)
        (bankTrialSuccessLocalLatchResetStep
          ring root e hw z hprev)

/-- A one-edge transition to WON has a latched bank whenever an
already-WON predecessor has a latched bank. No reachability
assumption is needed for this one-step implication. -/
theorem bankTrialSuccessLocalWonLatchedStep
    {n q : Nat} (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialLocalState q)
    (hprev : z.phase = .won → z.bank.success = true) :
    (bankTrialLocalNext ring root z e).phase = .won →
      (bankTrialLocalNext ring root z e).bank.success = true := by
  cases z with
  | mk B phase =>
      cases phase with
      | won =>
          rw [bankTrialLocalTerminalAbsorbs ring root e
            (⟨B, .won⟩ : BankTrialLocalState q) (Or.inl rfl)]
          exact hprev
      | lost =>
          rw [bankTrialLocalTerminalAbsorbs ring root e
            (⟨B, .lost⟩ : BankTrialLocalState q) (Or.inr rfl)]
          exact hprev
      | recovery =>
          by_cases hs :
              (GrantBankReference.bankLocalReferenceStepClamped
                ring root B e).success = true
          · have hnext :=
              bankTrialLocalRecoverySuccessPriority
                ring root e B hs
            rw [hnext]
            intro _
            exact hs
          · intro hwon
            by_cases hclean :
                BankTrialLocalClean q
                  (GrantBankReference.bankLocalReferenceStepClamped
                    ring root B e)
            · simp [bankTrialLocalNext, hs, hclean] at hwon
            · simp [bankTrialLocalNext, hs, hclean] at hwon
      | live begun =>
          by_cases hs :
              (GrantBankReference.bankLocalReferenceStepClamped
                ring root B e).success = true
          · have hnext :
                bankTrialLocalNext ring root
                  (⟨B, .live begun⟩ : BankTrialLocalState q) e =
                ⟨GrantBankReference.bankLocalReferenceStepClamped
                    ring root B e, .won⟩ := by
                simp [bankTrialLocalNext, hs]
            rw [hnext]
            intro _
            exact hs
          · intro hwon
            by_cases hclean :
                BankTrialLocalClean q
                  (GrantBankReference.bankLocalReferenceStepClamped
                    ring root B e) ∧
                (begun = true ∨ e = root ∨
                  ring.rightNeighbor e = root)
            · simp [bankTrialLocalNext, hs, hclean] at hwon
            · simp [bankTrialLocalNext, hs, hclean] at hwon
              all_goals (split at hwon <;> simp at hwon)

/-- WON implies a set success latch throughout an original-clock
run, provided the implication holds in its initial state. -/
theorem bankTrialSuccessRunWonLatched
    {n q : Nat} (ring : DirectedRing n) (root : Fin n) :
    ∀ (word : List (Fin n)) (z : BankTrialLocalState q),
      (z.phase = .won → z.bank.success = true) →
      (bankTrialLocalRun ring root word z).phase = .won →
        (bankTrialLocalRun ring root word z).bank.success = true := by
  intro word
  induction word with
  | nil =>
      intro z hprev
      exact hprev
  | cons e tail ih =>
      intro z hprev
      exact ih (bankTrialLocalNext ring root z e)
        (bankTrialSuccessLocalWonLatchedStep
          ring root e z hprev)

/-- Every CLEAN-reachable WON snapshot has a RESET root, hence
cannot be a CSTART stage seed. Terminal absorption cannot alter it. -/
theorem bankTrialSuccessReachableWonNotCStart
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n))
    (hwon : (bankTrialLocalRun ring root pre
      (bankTrialLocalStart S)).phase = .won) :
    bankTrialLiveWaveRootMode
      (bankTrialLocalRun ring root pre
        (bankTrialLocalStart S)).bank ≠ .CSTART := by
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hseed :
      (bankTrialLocalStart S).bank.success = true →
        bankTrialLiveWaveRootMode
          (bankTrialLocalStart S).bank = .RESET := by
    intro h
    change S.success = true at h
    rw [hclean.1] at h
    cases h
  have hseedWon :
      (bankTrialLocalStart S).phase = .won →
        (bankTrialLocalStart S).bank.success = true := by
    intro h
    cases h
  have hlatched := bankTrialSuccessRunWonLatched
    ring root pre (bankTrialLocalStart S) hseedWon hwon
  have hreset := bankTrialSuccessRunLatchedReset
    ring root hw pre (bankTrialLocalStart S) hseed hlatched
  intro hc
  rw [hreset] at hc
  cases hc

/-- The complete final-horizon stage-pending bridge: no terminal
mode hypothesis remains, and all tests use the original word. -/
theorem bankTrialSuccessStagePendingBridge
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (j T : Nat) (word : List (Fin n))
    (hp : bankTrialSuccessGoodReturnStagePendingBool
      ring root S j T word = true) :
    bankTrialSuccessFinalNonterminalBool ring root S word = true := by
  exact bankTrialSuccessStagePendingFinalOfWonMode
    ring root S hsp hlarge hwidth hclean
    (fun pre hw =>
      bankTrialSuccessReachableWonNotCStart
        ring root S hlarge hclean pre hw)
    j T word hp

/-- When the first-GOOD scan succeeds, its answer is recognized on
the consumed portion alone; no future letters are needed. -/
theorem bankTrialSuccessFirstGoodRecognizedPrefix
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (x : BankTrialLocalState q) :
    ∀ (remaining acc found : List (Fin n)),
      bankTrialSuccessFirstGoodReturnPrefix
        ring root S x acc remaining = some found →
      ∃ taken suffix : List (Fin n),
        remaining = taken ++ suffix ∧
        found = acc ++ taken ∧
        bankTrialSuccessFirstGoodReturnPrefix
          ring root S x acc taken = some found := by
  intro remaining
  induction remaining with
  | nil =>
      intro acc found hfound
      by_cases hg :
          bankTrialC5PostHeadFirstExit ring root S acc x =
            some true
      · have heq : acc = found := Option.some.inj (by
          simpa only [bankTrialSuccessFirstGoodReturnPrefix,
            if_pos hg] using hfound)
        refine ⟨[], [], rfl, ?_, ?_⟩
        · simpa only [List.append_nil] using heq.symm
        · simp only [bankTrialSuccessFirstGoodReturnPrefix,
            if_pos hg]
          exact congrArg some heq
      · simp only [bankTrialSuccessFirstGoodReturnPrefix,
          if_neg hg] at hfound
        cases hfound
  | cons e tail ih =>
      intro acc found hfound
      by_cases hg :
          bankTrialC5PostHeadFirstExit ring root S acc x =
            some true
      · have heq : acc = found := Option.some.inj (by
          simpa only [bankTrialSuccessFirstGoodReturnPrefix,
            if_pos hg] using hfound)
        refine ⟨[], e :: tail, rfl, ?_, ?_⟩
        · simpa only [List.append_nil] using heq.symm
        · simp only [bankTrialSuccessFirstGoodReturnPrefix,
            if_pos hg]
          exact congrArg some heq
      · have htail :
            bankTrialSuccessFirstGoodReturnPrefix
              ring root S x (acc ++ [e]) tail = some found := by
          simpa only [bankTrialSuccessFirstGoodReturnPrefix,
            if_neg hg] using hfound
        obtain ⟨taken, suffix, hrest, hprefix, hshort⟩ :=
          ih (acc ++ [e]) found htail
        refine ⟨e :: taken, suffix, ?_, ?_, ?_⟩
        · simpa only [List.cons_append] using
            congrArg (List.cons e) hrest
        · simpa only [List.append_assoc,
            List.singleton_append] using hprefix
        · simpa only [bankTrialSuccessFirstGoodReturnPrefix,
            if_neg hg] using hshort

theorem bankTrialSuccessFirstGoodSelf
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (x : BankTrialLocalState q)
    (remaining segment : List (Fin n))
    (hfound : bankTrialSuccessFirstGoodReturnPrefix
      ring root S x [] remaining = some segment) :
    bankTrialSuccessFirstGoodReturnPrefix
      ring root S x [] segment = some segment := by
  obtain ⟨taken, suffix, _, hsegment, hshort⟩ :=
    bankTrialSuccessFirstGoodRecognizedPrefix
      ring root S x remaining [] segment hfound
  have heq : segment = taken := by
    simpa only [List.nil_append] using hsegment
  rw [heq] at hshort ⊢
  simpa only [List.nil_append] using hshort

/-- Reverse recognition of every defined chronological GOOD cut:
the complete word and the exact cut prefix return the same cut. -/
theorem bankTrialSuccessGoodReturnCutSelf
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (word : List (Fin n)) :
    ∀ (j : Nat) (cut : List (Fin n)),
      bankTrialSuccessGoodReturnCutPrefix
        ring root S word j = some cut →
      bankTrialSuccessGoodReturnCutPrefix
        ring root S cut j = some cut := by
  intro j
  induction j with
  | zero =>
      intro cut hcut
      have heq : ([] : List (Fin n)) = cut :=
        Option.some.inj (by
          simpa only [bankTrialSuccessGoodReturnCutPrefix]
            using hcut)
      subst cut
      rfl
  | succ j ih =>
      intro cut hcut
      cases hprev :
          bankTrialSuccessGoodReturnCutPrefix
            ring root S word j with
      | none =>
          simp only [bankTrialSuccessGoodReturnCutPrefix,
            hprev] at hcut
          cases hcut
      | some prev =>
          have hprevSelf := ih prev hprev
          obtain ⟨suffix, hword⟩ :=
            bankTrialSuccessGoodReturnCutIsPrefix
              ring root S word j prev hprev
          cases hscan :
              bankTrialSuccessFirstGoodReturnPrefix ring root S
                (bankTrialLocalRun ring root prev
                  (bankTrialLocalStart S))
                [] (word.drop prev.length) with
          | none =>
              simp only [bankTrialSuccessGoodReturnCutPrefix,
                hprev, hscan] at hcut
              cases hcut
          | some segment =>
              have heq : prev ++ segment = cut :=
                Option.some.inj (by
                  simpa only [bankTrialSuccessGoodReturnCutPrefix,
                    hprev, hscan] using hcut)
              have hdrop : word.drop prev.length = suffix := by
                rw [hword]
                exact bankTrialSuccessDropPrefixAppend prev suffix
              have hscanSuffix :
                  bankTrialSuccessFirstGoodReturnPrefix
                    ring root S
                    (bankTrialLocalRun ring root prev
                      (bankTrialLocalStart S))
                    [] suffix = some segment := by
                rw [← hdrop]
                exact hscan
              have hscanShort :=
                bankTrialSuccessFirstGoodSelf ring root S
                  (bankTrialLocalRun ring root prev
                    (bankTrialLocalStart S))
                  suffix segment hscanSuffix
              have hprevShort :
                  bankTrialSuccessGoodReturnCutPrefix
                    ring root S (prev ++ segment) j = some prev :=
                bankTrialSuccessGoodReturnCutAppend
                  ring root S j prev prev segment hprevSelf
              have hshort :
                  bankTrialSuccessGoodReturnCutPrefix
                    ring root S (prev ++ segment) (j + 1) =
                      some (prev ++ segment) := by
                simp only [bankTrialSuccessGoodReturnCutPrefix,
                  hprevShort, bankTrialSuccessDropPrefixAppend,
                  hscanShort]
              rw [← heq]
              exact hshort

/-- At an authenticated cut there is no earlier stopping prefix.
The first-stopped operator reaches this cut and evaluates exactly
the remaining physical suffix, even when the horizon is arbitrary. -/
theorem bankTrialSuccessFirstStoppedSuffixAtCut
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j : Nat) :
    ∀ (used suffix pre : List (Fin n))
      (z : BankTrialLocalState q) (T : Nat),
      z = bankTrialLocalRun ring root pre (bankTrialLocalStart S) →
      bankTrialSuccessGoodReturnCutPrefix
        ring root S (pre ++ used) j = some (pre ++ used) →
      Prob.firstStoppedSuffixWord (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        (fun x _ remaining =>
          bankTrialSuccessGoodReturnStagePendingAt
            ring root S x remaining)
        T pre z (used ++ suffix) =
      bankTrialSuccessGoodReturnStagePendingAt ring root S
        (bankTrialLocalRun ring root (pre ++ used)
          (bankTrialLocalStart S)) suffix := by
  intro used
  induction used with
  | nil =>
      intro suffix pre z T hz hcut
      have hbase :
          bankTrialSuccessGoodReturnCutPrefix
            ring root S pre j = some pre := by
        simpa only [List.append_nil] using hcut
      have hstop :
          bankTrialSuccessGoodReturnCutBool
            ring root S j pre z = true := by
        simp [bankTrialSuccessGoodReturnCutBool, hbase]
      have hread :
          Prob.firstStoppedSuffixWord (bankTrialLocalNext ring root)
            (bankTrialSuccessGoodReturnCutBool ring root S j)
            (fun x _ remaining =>
              bankTrialSuccessGoodReturnStagePendingAt
                ring root S x remaining)
            T pre z suffix =
          bankTrialSuccessGoodReturnStagePendingAt
            ring root S z suffix := by
        cases suffix with
        | nil =>
            simp [Prob.firstStoppedSuffixWord, hstop]
        | cons a tail =>
            simp [Prob.firstStoppedSuffixWord, hstop]
      simpa only [List.nil_append, List.append_nil, hz] using hread
  | cons e tail ih =>
      intro suffix pre z T hz hcut
      have hbig :
          bankTrialSuccessGoodReturnCutBool ring root S j
            (pre ++ (e :: tail))
            (Prob.stoppedTapeRun (bankTrialLocalNext ring root)
              (pre ++ (e :: tail)) (bankTrialLocalStart S)) =
                true := by
        simp [bankTrialSuccessGoodReturnCutBool, hcut]
      have hstopFalse :
          bankTrialSuccessGoodReturnCutBool
            ring root S j pre z = false := by
        cases hs :
            bankTrialSuccessGoodReturnCutBool
              ring root S j pre z with
        | false =>
            rfl
        | true =>
            have hsmall :
                bankTrialSuccessGoodReturnCutBool ring root S j
                  pre
                  (Prob.stoppedTapeRun
                    (bankTrialLocalNext ring root)
                    pre (bankTrialLocalStart S)) = true := by
              simpa only [bankTrialSuccessGoodReturnCutBool] using hs
            have hnil :=
              bankTrialSuccessGoodReturnCutPrefixFree
                ring root S j pre (e :: tail) hsmall hbig
            cases hnil
      have hznext :
          bankTrialLocalNext ring root z e =
            bankTrialLocalRun ring root (pre ++ [e])
              (bankTrialLocalStart S) := by
        rw [bankTrialLocalRunAppend, ← hz]
        rfl
      have hnextCut :
          bankTrialSuccessGoodReturnCutPrefix
            ring root S ((pre ++ [e]) ++ tail) j =
              some ((pre ++ [e]) ++ tail) := by
        simpa only [List.append_assoc,
          List.singleton_append] using hcut
      have htail :=
        ih suffix (pre ++ [e])
          (bankTrialLocalNext ring root z e) (T - 1)
          hznext hnextCut
      simpa [Prob.firstStoppedSuffixWord, hstopFalse,
        List.cons_append, List.append_assoc,
        List.singleton_append] using htail

/-- First stopping on a full tape agrees with the j-th recursive
GOOD cut; the inspected suffix is the literal word.drop cut.length. -/
theorem bankTrialSuccessFirstStoppedSuffixOfGoodCut
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word cut : List (Fin n)) (j T : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word j = some cut) :
    Prob.firstStoppedSuffixWord (bankTrialLocalNext ring root)
      (bankTrialSuccessGoodReturnCutBool ring root S j)
      (fun x _ suffix =>
        bankTrialSuccessGoodReturnStagePendingAt ring root S x suffix)
      T [] (bankTrialLocalStart S) word =
    bankTrialSuccessGoodReturnStagePendingAt ring root S
      (bankTrialLocalRun ring root cut (bankTrialLocalStart S))
      (word.drop cut.length) := by
  obtain ⟨suffix, hword⟩ :=
    bankTrialSuccessGoodReturnCutIsPrefix
      ring root S word j cut hcut
  have hself :=
    bankTrialSuccessGoodReturnCutSelf
      ring root S word j cut hcut
  have hbase :
      bankTrialSuccessGoodReturnCutPrefix
        ring root S ([] ++ cut) j = some ([] ++ cut) := by
    simpa only [List.nil_append] using hself
  have hstop :=
    bankTrialSuccessFirstStoppedSuffixAtCut
      ring root S j cut suffix []
      (bankTrialLocalStart S) T rfl hbase
  rw [hword, bankTrialSuccessDropPrefixAppend]
  simpa only [List.nil_append] using hstop

/-- A genuine first GOOD return needs at least one scheduler letter. -/
theorem bankTrialSuccessFirstGoodSegmentNonempty
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (x : BankTrialLocalState q)
    (segment : List (Fin n))
    (hfound : bankTrialSuccessFirstGoodReturnPrefix
      ring root S x [] segment = some segment) :
    segment ≠ [] := by
  intro hnil
  subst segment
  rw [bankTrialSuccessFirstGoodReturnEmpty] at hfound
  cases hfound

/-- The j-th GOOD return cannot be certified with fewer than j
physical scheduler letters in its own stopping prefix. -/
theorem bankTrialSuccessGoodCutIndexLeLength
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (word : List (Fin n)) :
    ∀ (j : Nat) (cut : List (Fin n)),
      bankTrialSuccessGoodReturnCutPrefix
        ring root S word j = some cut →
      j ≤ cut.length := by
  intro j
  induction j with
  | zero =>
      intro cut _
      exact Nat.zero_le _
  | succ j ih =>
      intro cut hcut
      cases hprev :
          bankTrialSuccessGoodReturnCutPrefix ring root S word j with
      | none =>
          simp only [bankTrialSuccessGoodReturnCutPrefix,
            hprev] at hcut
          cases hcut
      | some prev =>
          have hlen := ih prev hprev
          cases hscan :
              bankTrialSuccessFirstGoodReturnPrefix ring root S
                (bankTrialLocalRun ring root prev
                  (bankTrialLocalStart S))
                [] (word.drop prev.length) with
          | none =>
              simp only [bankTrialSuccessGoodReturnCutPrefix,
                hprev, hscan] at hcut
              cases hcut
          | some segment =>
              have heq : prev ++ segment = cut :=
                Option.some.inj (by
                  simpa only [bankTrialSuccessGoodReturnCutPrefix,
                    hprev, hscan] using hcut)
              have hshort :=
                bankTrialSuccessFirstGoodSelf ring root S
                  (bankTrialLocalRun ring root prev
                    (bankTrialLocalStart S))
                  (word.drop prev.length) segment hscan
              have hnot :=
                bankTrialSuccessFirstGoodSegmentNonempty
                  ring root S
                  (bankTrialLocalRun ring root prev
                    (bankTrialLocalStart S))
                  segment hshort
              have hpos : 0 < segment.length := by
                cases segment with
                | nil =>
                    exact False.elim (hnot rfl)
                | cons a tail =>
                    simp only [List.length_cons]
                    omega
              rw [← heq, List.length_append]
              omega

theorem bankTrialSuccessGoodCutIndexLeWord
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (word cut : List (Fin n)) (j : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word j = some cut) :
    j ≤ word.length := by
  have hlen :=
    bankTrialSuccessGoodCutIndexLeLength
      ring root S word j cut hcut
  obtain ⟨suffix, hword⟩ :=
    bankTrialSuccessGoodReturnCutIsPrefix
      ring root S word j cut hcut
  rw [hword, List.length_append]
  omega

/-- An existing j-th GOOD cut and an absent (j+1)-st cut determine
the exact ordinal j. Earlier cuts and the length bound are derived,
rather than supplied as extra premises. -/
theorem bankTrialSuccessOrdinalOfAdjacentCuts
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (word cut : List (Fin n)) (j : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word j = some cut)
    (hmissing : bankTrialSuccessGoodReturnCutPrefix
      ring root S word (j + 1) = none) :
    bankTrialSuccessGoodReturnOrdinal ring root S word = j := by
  have hbound :=
    bankTrialSuccessGoodCutIndexLeWord
      ring root S word cut j hcut
  have hprevious : ∀ i, i < j →
      (bankTrialSuccessGoodReturnCutPrefix
        ring root S word (i + 1)).isSome = true := by
    intro i hi
    cases hc :
        bankTrialSuccessGoodReturnCutPrefix
          ring root S word (i + 1) with
    | some earlier =>
        rfl
    | none =>
        have habsent :=
          bankTrialSuccessGoodReturnCutNoneAbove
            ring root S word (i + 1) hc j (by omega)
        rw [habsent] at hcut
        cases hcut
  exact bankTrialSuccessGoodReturnOrdinalOfFirstMissing
    ring root S word j hbound hprevious hmissing

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- At the actual initial ARMED cut, the installed four-class
PENDING event implies the raw, suffix-evaluated stage-zero event.
No independent stage scheduler is introduced. -/
theorem bankTrialSuccessInitialStagePendingRaw
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (T : Nat) (word : List (Fin n))
    (hcase : bankTrialC5StageClass ring root S
      (bankTrialLocalStart S) word = .pending) :
    bankTrialSuccessGoodReturnStagePendingBool
      ring root S 0 T word = true := by
  have hone :
      bankTrialC5StageIndicator
          (bankTrialC5StageClass ring root S
            (bankTrialLocalStart S) word) .pending = 1 := by
    simp [bankTrialC5StageIndicator, hcase]
  have hpart :=
    (bankTrialC5PendingAndHeadIndicators
      ring root S (bankTrialLocalStart S) word).1
  rw [hone] at hpart
  have hor :
      (bankTrialC5PendingBeforeBool ring root S
          (bankTrialLocalStart S) word ||
        bankTrialC5PendingAfterBool ring root S
          (bankTrialLocalStart S) word) = true := by
    cases hb : bankTrialC5PendingBeforeBool ring root S
        (bankTrialLocalStart S) word with
    | true =>
        simp [hb]
    | false =>
        cases ha : bankTrialC5PendingAfterBool ring root S
            (bankTrialLocalStart S) word with
        | true =>
            simp [hb, ha]
        | false =>
            simp [Prob.indicator, hb, ha] at hpart
  have hm :
      bankTrialLiveWaveRootMode
        (bankTrialLocalStart S).bank = .ARMED :=
    hclean.2.1
  have hc :
      bankTrialLiveWaveRootMode
        (bankTrialLocalStart S).bank ≠ .CSTART := by
    rw [hm]
    intro hh
    cases hh
  have hg :
      BankTrialProbabilityArmedGate
        (bankTrialLocalStart S) :=
    ⟨⟨false, rfl⟩, hm⟩
  rw [bankTrialSuccessGoodReturnStageZeroExact
    ring root S T word]
  simpa only [bankTrialSuccessGoodReturnStagePendingAt,
    if_neg hc, if_pos hg] using hor

/-- The entire initial-stage pending class is included in the
ONE final-horizon nonterminal event. This is a mass inclusion on
the original Fin n scheduler, not a restarted stage experiment. -/
theorem bankTrialSuccessInitialStagePendingMassLeActive
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (T : Nat) :
    bankTrialC5StageMass ring root S
        (bankTrialLocalStart S) T .pending ≤
      bankTrialDurationActiveMass ring root S T := by
  have hword (word : List (Fin n)) :
      bankTrialC5StageIndicator
          (bankTrialC5StageClass ring root S
            (bankTrialLocalStart S) word) .pending ≤
        (if bankTrialLocalTerminal
            (bankTrialLocalRun ring root word
              (bankTrialLocalStart S))
         then 0 else 1) := by
    by_cases hc : bankTrialC5StageClass ring root S
        (bankTrialLocalStart S) word = .pending
    · have hp := bankTrialSuccessInitialStagePendingRaw
        ring root S hclean T word hc
      have hn := bankTrialSuccessZeroStagePendingNonterminal
        ring root S hlarge hclean T word hp
      simp [bankTrialC5StageIndicator, hc, hn]
    · simp [bankTrialC5StageIndicator, hc]
  change Prob.scheduleSum n T (fun word =>
      bankTrialC5StageIndicator
        (bankTrialC5StageClass ring root S
          (bankTrialLocalStart S) word) .pending) ≤
    Prob.scheduleSum n T (fun word =>
      if bankTrialLocalTerminal
          (bankTrialLocalRun ring root word
            (bankTrialLocalStart S))
      then 0 else 1)
  exact bankTrialProbabilityScheduleSumMono n T _ _ hword

/-- The initial ARMED stage receives one unconditional C.6
original-clock charge, with no stage-local mean assumption. -/
theorem bankTrialSuccessInitialStagePendingMarkov
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (T : Nat) :
    T * bankTrialC5StageMass ring root S
        (bankTrialLocalStart S) T .pending ≤
      n ^ T * ((8 * (compileAdvice q).b + 12) * n) := by
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hn : 2 ≤ n := by
    have hh := hw
    unfold BankTrialLiveWindowNonalias at hh
    omega
  have hq : 3 ≤ q := by
    have hs : (compileAdvice q).useSmall =
        decide (q ≤ qStar) := rfl
    rw [hs] at hsp
    have hh : ¬ q ≤ qStar := of_decide_eq_false hsp
    change ¬ q ≤ 79 at hh
    omega
  have hk : 0 < (compileAdvice q).K := by
    change 0 < 2 * q + productionKappa q
    omega
  calc
    T * bankTrialC5StageMass ring root S
        (bankTrialLocalStart S) T .pending ≤
      T * bankTrialDurationActiveMass ring root S T :=
        Nat.mul_le_mul_left T
          (bankTrialSuccessInitialStagePendingMassLeActive
            ring root S hlarge hclean T)
    _ ≤ n ^ T * ((8 * (compileAdvice q).b + 12) * n) :=
      bankTrialSuccessMarkovOfDurationBound
        ring root hn hsp hw hk hwidth S hclean T

/-- One-stage stopped-tree algebra on opaque naturals.
The weighted pre-head and post-head pending charges are paid by
the same final pending mass, then by one clock budget. -/
theorem bankTrialSuccessOneStageForwardOpaque
    {D N X G Q R A B T : Nat}
    (hstage : D * X ≤
      (2 * D * G + 2 * N * X) +
        (D * Q + 2 * D * R))
    (hpending : Q + R ≤ A)
    (hbudget : T * A ≤ B * X) :
    D * T * X ≤
      (2 * D * T * G + 2 * N * T * X) +
        2 * D * B * X := by
  have hweighted :
      D * Q + 2 * D * R ≤ 2 * D * (Q + R) := by
    have hd : D ≤ 2 * D := by omega
    have hq : D * Q ≤ (2 * D) * Q :=
      Nat.mul_le_mul_right Q hd
    calc
      D * Q + 2 * D * R ≤
          (2 * D) * Q + (2 * D) * R :=
        Nat.add_le_add_right hq _
      _ = 2 * D * (Q + R) := by rw [Nat.mul_add]
  have hqr : T * (Q + R) ≤ B * X :=
    Nat.le_trans (Nat.mul_le_mul_left T hpending) hbudget
  have hpendBudget :
      T * (D * Q + 2 * D * R) ≤
        2 * D * B * X := by
    calc
      T * (D * Q + 2 * D * R) ≤
          T * (2 * D * (Q + R)) :=
        Nat.mul_le_mul_left T hweighted
      _ = (2 * D) * (T * (Q + R)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ (2 * D) * (B * X) :=
        Nat.mul_le_mul_left (2 * D) hqr
      _ = 2 * D * B * X := by
        simp only [Nat.mul_assoc]
  calc
    D * T * X = T * (D * X) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ T * ((2 * D * G + 2 * N * X) +
        (D * Q + 2 * D * R)) :=
      Nat.mul_le_mul_left T hstage
    _ = T * (2 * D * G + 2 * N * X) +
        T * (D * Q + 2 * D * R) := by
      rw [Nat.mul_add]
    _ ≤ T * (2 * D * G + 2 * N * X) +
        2 * D * B * X :=
      Nat.add_le_add_left hpendBudget _
    _ = (2 * D * T * G + 2 * N * T * X) +
        2 * D * B * X := by
      simp only [Nat.mul_add, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm]

/-- A complete ONE-ARMED-CUT finite-horizon forward inequality.
It uses the existing actual-origin kernel (including its
conditionalRarity field), the first-incident fair-bit law, and
the one original-clock C.6 pending budget. It does NOT assert
the K-head completed-mass hforward estimate. -/
theorem bankTrialSuccessOneArmedForwardOfKernel
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (T : Nat) :
    bankTrialProbabilityC5WorkerDenominator q * T * n ^ T ≤
      (2 * bankTrialProbabilityC5WorkerDenominator q * T *
          bankTrialC5StageMass ring root S
            (bankTrialLocalStart S) T .good +
        2 * bankTrialProbabilityC5WorkerNumerator q * T * n ^ T) +
      2 * bankTrialProbabilityC5WorkerDenominator q *
        ((8 * (compileAdvice q).b + 12) * n) * n ^ T := by
  have hg :
      BankTrialProbabilityArmedGate
        (bankTrialLocalStart S) :=
    ⟨⟨false, rfl⟩, hclean.2.1⟩
  have hstage := bankTrialC5OneArmedStage
    ring root S hkernel hlarge hclean []
    (bankTrialLocalStart S) rfl hg T
  have hpending :
      bankTrialC5PendingBeforeMass ring root S
          (bankTrialLocalStart S) T +
        bankTrialC5PendingAfterMass ring root S
          (bankTrialLocalStart S) T ≤
      bankTrialC5StageMass ring root S
        (bankTrialLocalStart S) T .pending := by
    rw [bankTrialC5PendingMassSplit]
    exact Nat.le_refl _
  have hbudget :
      T * bankTrialC5StageMass ring root S
          (bankTrialLocalStart S) T .pending ≤
        ((8 * (compileAdvice q).b + 12) * n) * n ^ T := by
    calc
      T * bankTrialC5StageMass ring root S
          (bankTrialLocalStart S) T .pending ≤
        n ^ T * ((8 * (compileAdvice q).b + 12) * n) :=
        bankTrialSuccessInitialStagePendingMarkov
          ring root S hsp hlarge hwidth hclean T
      _ = ((8 * (compileAdvice q).b + 12) * n) * n ^ T :=
        Nat.mul_comm _ _
  exact bankTrialSuccessOneStageForwardOpaque
    (D := bankTrialProbabilityC5WorkerDenominator q)
    (N := bankTrialProbabilityC5WorkerNumerator q)
    (X := n ^ T)
    (G := bankTrialC5StageMass ring root S
      (bankTrialLocalStart S) T .good)
    (Q := bankTrialC5PendingBeforeMass ring root S
      (bankTrialLocalStart S) T)
    (R := bankTrialC5PendingAfterMass ring root S
      (bankTrialLocalStart S) T)
    (A := bankTrialC5StageMass ring root S
      (bankTrialLocalStart S) T .pending)
    (B := ((8 * (compileAdvice q).b + 12) * n))
    (T := T) hstage hpending hbudget

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-!
Exact stopped-prefix transfer for chronological GOOD-return
cuts. All sums refer to the original Fin n scheduler tape.

The first return from a cut is tested with the installed post-head
first-origin scanner. A fresh stage experiment is never introduced.
-/

/-- The two structurally identical original-scheduler runners agree.
This is useful when applying Prob.stoppedPrefixFactorization. -/
theorem bankTrialSuccessStoppedRunEqLocal
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (word : List (Fin n)) (x : BankTrialLocalState q) :
    Prob.stoppedTapeRun (bankTrialLocalNext ring root) word x =
      bankTrialLocalRun ring root word x := by
  induction word generalizing x with
  | nil => rfl
  | cons e tail ih =>
      change
        Prob.stoppedTapeRun (bankTrialLocalNext ring root) tail
            (bankTrialLocalNext ring root x e) =
          bankTrialLocalRun ring root tail
            (bankTrialLocalNext ring root x e)
      exact ih _

/-- Generic static observer evaluated on the physical suffix at an
authenticated j-th GOOD cut. The horizon parameter is unused by the
observer, so its subtraction along the prefix causes no mismatch.
This is the observer-general form of FirstStoppedSuffixOfGoodCut. -/
theorem bankTrialSuccessStaticStoppedAtCut
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (A : BankTrialLocalState q → List (Fin n) → Bool)
    (j : Nat) :
    ∀ (used suffix pre : List (Fin n))
      (z : BankTrialLocalState q) (T : Nat),
      z = bankTrialLocalRun ring root pre
        (bankTrialLocalStart S) →
      bankTrialSuccessGoodReturnCutPrefix ring root S
        (pre ++ used) j = some (pre ++ used) →
      Prob.firstStoppedSuffixWord (bankTrialLocalNext ring root)
          (bankTrialSuccessGoodReturnCutBool ring root S j)
          (fun x _ remaining => A x remaining)
          T pre z (used ++ suffix) =
        A (bankTrialLocalRun ring root (pre ++ used)
          (bankTrialLocalStart S)) suffix := by
  intro used
  induction used with
  | nil =>
      intro suffix pre z T hz hcut
      have hbase :
          bankTrialSuccessGoodReturnCutPrefix ring root S
            pre j = some pre := by
        simpa only [List.append_nil] using hcut
      have hstop :
          bankTrialSuccessGoodReturnCutBool ring root S j
            pre z = true := by
        simp [bankTrialSuccessGoodReturnCutBool, hbase]
      have hread :
          Prob.firstStoppedSuffixWord
              (bankTrialLocalNext ring root)
              (bankTrialSuccessGoodReturnCutBool ring root S j)
              (fun x _ remaining => A x remaining)
              T pre z suffix = A z suffix := by
        cases suffix with
        | nil =>
            simp [Prob.firstStoppedSuffixWord, hstop]
        | cons e tail =>
            simp [Prob.firstStoppedSuffixWord, hstop]
      simpa only [List.nil_append, List.append_nil, hz] using hread
  | cons e tail ih =>
      intro suffix pre z T hz hcut
      have hbig :
          bankTrialSuccessGoodReturnCutBool ring root S j
            (pre ++ (e :: tail))
            (Prob.stoppedTapeRun (bankTrialLocalNext ring root)
              (pre ++ (e :: tail)) (bankTrialLocalStart S)) =
            true := by
        simp [bankTrialSuccessGoodReturnCutBool, hcut]
      have hstopFalse :
          bankTrialSuccessGoodReturnCutBool ring root S j
            pre z = false := by
        cases hs :
            bankTrialSuccessGoodReturnCutBool ring root S j
              pre z with
        | false => rfl
        | true =>
            have hsmall :
                bankTrialSuccessGoodReturnCutBool ring root S j
                  pre
                  (Prob.stoppedTapeRun
                    (bankTrialLocalNext ring root)
                    pre (bankTrialLocalStart S)) = true := by
              simpa only [bankTrialSuccessGoodReturnCutBool]
                using hs
            have hnil :=
              bankTrialSuccessGoodReturnCutPrefixFree
                ring root S j pre (e :: tail) hsmall hbig
            cases hnil
      have hznext :
          bankTrialLocalNext ring root z e =
            bankTrialLocalRun ring root (pre ++ [e])
              (bankTrialLocalStart S) := by
        rw [bankTrialLocalRunAppend, ← hz]
        rfl
      have hnextCut :
          bankTrialSuccessGoodReturnCutPrefix ring root S
            ((pre ++ [e]) ++ tail) j =
              some ((pre ++ [e]) ++ tail) := by
        simpa only [List.append_assoc, List.singleton_append]
          using hcut
      have htail :=
        ih suffix (pre ++ [e])
          (bankTrialLocalNext ring root z e) (T - 1)
          hznext hnextCut
      simpa [Prob.firstStoppedSuffixWord, hstopFalse,
        List.cons_append, List.append_assoc,
        List.singleton_append] using htail

/-- The authenticated cut on a full word determines the exact
suffix seen by ANY static first-stop observer. -/
theorem bankTrialSuccessStaticStoppedOfGoodCut
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (A : BankTrialLocalState q → List (Fin n) → Bool)
    (word cut : List (Fin n)) (j T : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix ring root S
      word j = some cut) :
    Prob.firstStoppedSuffixWord (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        (fun x _ suffix => A x suffix)
        T [] (bankTrialLocalStart S) word =
      A (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S)) (word.drop cut.length) := by
  obtain ⟨suffix, hword⟩ :=
    bankTrialSuccessGoodReturnCutIsPrefix
      ring root S word j cut hcut
  have hself :=
    bankTrialSuccessGoodReturnCutSelf
      ring root S word j cut hcut
  have hbase :
      bankTrialSuccessGoodReturnCutPrefix ring root S
        ([] ++ cut) j = some ([] ++ cut) := by
    simpa only [List.nil_append] using hself
  have hstop :=
    bankTrialSuccessStaticStoppedAtCut
      ring root S A j cut suffix [] (bankTrialLocalStart S)
      T rfl hbase
  rw [hword, bankTrialSuccessDropPrefixAppend]
  simpa only [List.nil_append] using hstop

/-- A missing j-th cut on the full tape cannot be fabricated by
testing any shorter consumed prefix. This is the no-cut half of
the pointwise stopping-time transfer. -/
theorem bankTrialSuccessStaticStoppedNone
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (A : BankTrialLocalState q → List (Fin n) → Bool)
    (j : Nat) :
    ∀ (word pre : List (Fin n))
      (z : BankTrialLocalState q) (T : Nat),
      z = bankTrialLocalRun ring root pre
        (bankTrialLocalStart S) →
      bankTrialSuccessGoodReturnCutPrefix ring root S
        (pre ++ word) j = none →
      Prob.firstStoppedSuffixWord (bankTrialLocalNext ring root)
          (bankTrialSuccessGoodReturnCutBool ring root S j)
          (fun x _ suffix => A x suffix)
          T pre z word = false := by
  intro word
  induction word with
  | nil =>
      intro pre z T hz hnone
      have hstopFalse :
          bankTrialSuccessGoodReturnCutBool ring root S j
            pre z = false := by
        cases hs : bankTrialSuccessGoodReturnCutBool
            ring root S j pre z with
        | false => rfl
        | true =>
            have hc :
                bankTrialSuccessGoodReturnCutPrefix ring root S
                  pre j = some pre :=
              of_decide_eq_true
                (show decide
                  (bankTrialSuccessGoodReturnCutPrefix ring root S
                    pre j = some pre) = true from hs)
            have hn :
                bankTrialSuccessGoodReturnCutPrefix ring root S
                  pre j = none := by
              simpa only [List.append_nil] using hnone
            rw [hc] at hn
            cases hn
      simp [Prob.firstStoppedSuffixWord, hstopFalse]
  | cons e tail ih =>
      intro pre z T hz hnone
      have hstopFalse :
          bankTrialSuccessGoodReturnCutBool ring root S j
            pre z = false := by
        cases hs : bankTrialSuccessGoodReturnCutBool
            ring root S j pre z with
        | false => rfl
        | true =>
            have hc :
                bankTrialSuccessGoodReturnCutPrefix ring root S
                  pre j = some pre :=
              of_decide_eq_true
                (show decide
                  (bankTrialSuccessGoodReturnCutPrefix ring root S
                    pre j = some pre) = true from hs)
            have hfull :=
              bankTrialSuccessGoodReturnCutAppend
                ring root S j pre pre (e :: tail) hc
            rw [hfull] at hnone
            cases hnone
      have hznext :
          bankTrialLocalNext ring root z e =
            bankTrialLocalRun ring root (pre ++ [e])
              (bankTrialLocalStart S) := by
        rw [bankTrialLocalRunAppend, ← hz]
        rfl
      have hnextNone :
          bankTrialSuccessGoodReturnCutPrefix ring root S
            ((pre ++ [e]) ++ tail) j = none := by
        simpa only [List.append_assoc, List.singleton_append]
          using hnone
      have htail := ih (pre ++ [e])
        (bankTrialLocalNext ring root z e)
        (T - 1) hznext hnextNone
      simpa [Prob.firstStoppedSuffixWord, hstopFalse] using htail

/-- POINTWISE exact equality, not merely an event inclusion:
the first-stopped suffix after cut j has another classified GOOD
return iff the chronological cut j+1 exists on the SAME tape. -/
theorem bankTrialSuccessNextGoodCutWordExact
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j T : Nat) (word : List (Fin n)) :
    Prob.firstStoppedSuffixWord (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        (fun x _ suffix =>
          (bankTrialSuccessFirstGoodReturnPrefix
            ring root S x [] suffix).isSome)
        T [] (bankTrialLocalStart S) word =
      (bankTrialSuccessGoodReturnCutPrefix
        ring root S word (j + 1)).isSome := by
  cases hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word j with
  | none =>
      have hnone :
          bankTrialSuccessGoodReturnCutPrefix
            ring root S word (j + 1) = none := by
        simp only [bankTrialSuccessGoodReturnCutPrefix, hcut]
      have hstop :=
        bankTrialSuccessStaticStoppedNone
          ring root S
          (fun x suffix =>
            (bankTrialSuccessFirstGoodReturnPrefix
              ring root S x [] suffix).isSome)
          j word [] (bankTrialLocalStart S) T rfl
          (by simpa only [List.nil_append] using hcut)
      rw [hstop, hnone]
      rfl
  | some cut =>
      have hstop :=
        bankTrialSuccessStaticStoppedOfGoodCut
          ring root S
          (fun x suffix =>
            (bankTrialSuccessFirstGoodReturnPrefix
              ring root S x [] suffix).isSome)
          word cut j T hcut
      rw [hstop]
      cases hscan :
          bankTrialSuccessFirstGoodReturnPrefix ring root S
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S))
            [] (word.drop cut.length) with
      | none =>
          simp [bankTrialSuccessGoodReturnCutPrefix, hcut, hscan]
      | some segment =>
          simp [bankTrialSuccessGoodReturnCutPrefix, hcut, hscan]

/-- COMPLETE STOPPED-PREFIX MASS TRANSFER (requested part (1)).
The numerator of length-T words passing the (j+1)-st real GOOD
return equals the sum over FIRST j-th stopping prefixes cut of
the conditional numerator of another GOOD return on the actual
remaining T-cut.length scheduler letters, starting at the actual
state after cut. No restarting, averaging or independence occurs. -/
theorem bankTrialSuccessNextGoodCutMassTransfer
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j T : Nat) :
    Prob.scheduleSum n T (fun word =>
        Prob.indicator
          (bankTrialSuccessGoodReturnCutPrefix
            ring root S word (j + 1)).isSome) =
      ((Prob.firstStoppedPrefixes
          (bankTrialLocalNext ring root)
          (bankTrialSuccessGoodReturnCutBool ring root S j)
          T [] (bankTrialLocalStart S)).map (fun cut =>
        Prob.scheduleSum n (T - cut.length) (fun suffix =>
          Prob.indicator
            (bankTrialSuccessFirstGoodReturnPrefix ring root S
              (bankTrialLocalRun ring root cut
                (bankTrialLocalStart S))
              [] suffix).isSome))).sum := by
  have hfactor :
      Prob.scheduleSum n T (fun word =>
        Prob.indicator
          (Prob.firstStoppedSuffixWord
            (bankTrialLocalNext ring root)
            (bankTrialSuccessGoodReturnCutBool ring root S j)
            (fun x _ suffix =>
              (bankTrialSuccessFirstGoodReturnPrefix
                ring root S x [] suffix).isSome)
            T [] (bankTrialLocalStart S) word)) =
      ((Prob.firstStoppedPrefixes
          (bankTrialLocalNext ring root)
          (bankTrialSuccessGoodReturnCutBool ring root S j)
          T [] (bankTrialLocalStart S)).map (fun cut =>
        Prob.scheduleSum n (T - cut.length) (fun suffix =>
          Prob.indicator
            (bankTrialSuccessFirstGoodReturnPrefix ring root S
              (bankTrialLocalRun ring root cut
                (bankTrialLocalStart S))
              [] suffix).isSome))).sum := by
    simpa only [bankTrialSuccessStoppedRunEqLocal] using
      (Prob.stoppedPrefixFactorization
        (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        (fun x _ suffix =>
          (bankTrialSuccessFirstGoodReturnPrefix
            ring root S x [] suffix).isSome)
        (bankTrialLocalStart S) T
        (bankTrialSuccessGoodReturnCutPrefixFree ring root S j))
  calc
    Prob.scheduleSum n T (fun word =>
        Prob.indicator
          (bankTrialSuccessGoodReturnCutPrefix
            ring root S word (j + 1)).isSome) =
      Prob.scheduleSum n T (fun word =>
        Prob.indicator
          (Prob.firstStoppedSuffixWord
            (bankTrialLocalNext ring root)
            (bankTrialSuccessGoodReturnCutBool ring root S j)
            (fun x _ suffix =>
              (bankTrialSuccessFirstGoodReturnPrefix
                ring root S x [] suffix).isSome)
            T [] (bankTrialLocalStart S) word)) := by
        apply congrArg (Prob.scheduleSum n T)
        funext word
        exact congrArg Prob.indicator
          (bankTrialSuccessNextGoodCutWordExact
            ring root S j T word).symm
    _ = _ := hfactor

/-- Requested part (2), at the actual positive chronological cut:
the ARMED and CSTART observers get their respective installed
local estimates; a WON cut is terminal instead. The CLEAN
reachability of each cut comes from its literal word-prefix run.
This result does not identify local GOOD with future completion. -/
theorem bankTrialSuccessPositiveGoodCutLocalStageCases
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (word cut : List (Fin n)) (j : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word (j + 1) = some cut) :
    (∃ begun : Bool,
      (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S)).phase = .live begun ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)).bank = .ARMED ∧
      ∀ t : Nat,
        bankTrialProbabilityC5WorkerDenominator q * n ^ t ≤
          (2 * bankTrialProbabilityC5WorkerDenominator q *
              bankTrialC5StageMass ring root S
                (bankTrialLocalRun ring root cut
                  (bankTrialLocalStart S)) t .good +
            2 * bankTrialProbabilityC5WorkerNumerator q * n ^ t) +
          (bankTrialProbabilityC5WorkerDenominator q *
              bankTrialC5PendingBeforeMass ring root S
                (bankTrialLocalRun ring root cut
                  (bankTrialLocalStart S)) t +
            2 * bankTrialProbabilityC5WorkerDenominator q *
              bankTrialC5PendingAfterMass ring root S
                (bankTrialLocalRun ring root cut
                  (bankTrialLocalStart S)) t)) ∨
    (∃ begun : Bool,
      (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S)).phase = .live begun ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)).bank = .CSTART ∧
      ∀ t : Nat,
        bankTrialProbabilityC5WorkerDenominator q * n ^ t ≤
          bankTrialProbabilityC5WorkerDenominator q *
            bankTrialC5CStartMass ring root S
              (bankTrialLocalRun ring root cut
                (bankTrialLocalStart S)) t (some true) +
          bankTrialProbabilityC5WorkerNumerator q * n ^ t +
          bankTrialProbabilityC5WorkerDenominator q *
            bankTrialC5CStartMass ring root S
              (bankTrialLocalRun ring root cut
                (bankTrialLocalStart S)) t none) ∨
    (bankTrialLocalRun ring root cut
      (bankTrialLocalStart S)).phase = .won := by
  rcases bankTrialSuccessPositiveGoodCutClasses
      ring root S word cut j hcut with
    ⟨begun, hlive, hmode⟩ |
    ⟨begun, hlive, hmode⟩ | hwon
  · left
    refine ⟨begun, hlive, hmode, ?_⟩
    intro t
    exact bankTrialC5OneArmedStage
      ring root S hkernel hlarge hclean cut
      (bankTrialLocalRun ring root cut (bankTrialLocalStart S))
      rfl ⟨⟨begun, hlive⟩, hmode⟩ t
  · right
    left
    refine ⟨begun, hlive, hmode, ?_⟩
    have hw : BankTrialLiveWindowNonalias n q :=
      bankTrialProbabilityUpperWindow hlarge
    have hlive' :
        (bankTrialC5CleanRun ring root S cut).phase =
          .live begun := by
      change
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)).phase = .live begun
      exact hlive
    have hmode' :
        bankTrialLiveWaveRootMode
          (bankTrialC5CleanRun ring root S cut).bank =
            .CSTART := by
      change
        bankTrialLiveWaveRootMode
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)).bank = .CSTART
      exact hmode
    have htokens :
        ∀ i : Fin (compileAdvice q).b,
          bankTrialLiveWaveToken
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)).bank i = .E := by
      have htok := bankTrialC5CleanCStartTokensEmpty
        ring root hw S hclean cut begun hlive' hmode'
      change
        ∀ i : Fin (compileAdvice q).b,
          bankTrialLiveWaveToken
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)).bank i = .E at htok
      exact htok
    intro t
    exact bankTrialC5OneCStartStage
      ring root S hkernel hlarge hclean cut
      (bankTrialLocalRun ring root cut (bankTrialLocalStart S))
      begun rfl hlive hmode htokens t
  · exact Or.inr (Or.inr hwon)

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-The comparison is pointwise on the ORIGINAL scheduler suffix. -/

/-- A non-outgoing-root service cannot emit an actual worker origin. -/
theorem bankTrialSuccessNoActualOriginOfNonroot
    {n q : Nat} (ring : DirectedRing n) (root e : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (hne : e ≠ root) :
    bankTrialC5ActualStarts ring root S x e = [] := by
  cases hs : bankTrialC5ActualStarts ring root S x e with
  | nil =>
      rfl
  | cons o others =>
      have ho : o ∈ bankTrialC5ActualStarts ring root S x e := by
        rw [hs]
        simp
      exact False.elim
        (hne (bankTrialC5ActualStartAtRoot ring root S x e o ho))

/-- An ARMED first-HEAD good exit is also a post-head good exit.
The post-head scan may inspect more words, but cannot miss an
outgoing first-incident HEAD accepted by the pre-head scan. -/
theorem bankTrialSuccessPreHeadGoodImpliesPostHeadGood
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    ∀ (word : List (Fin n)) (x : BankTrialLocalState q),
      bankTrialC5PreHeadFirstExit ring root S word x = some true →
      bankTrialC5PostHeadFirstExit ring root S word x = some true := by
  intro word
  induction word with
  | nil =>
      intro x hgood
      cases hgood
  | cons e tail ih =>
      intro x hgood
      by_cases he : e = root
      · simpa only [bankTrialC5PreHeadFirstExit,
          bankTrialC5PostHeadFirstExit, if_pos he] using hgood
      · by_cases hi : e = ring.leftNeighbor root
        · simp only [bankTrialC5PreHeadFirstExit,
            if_neg he, if_pos hi] at hgood
          cases hgood
        · have htail :
              bankTrialC5PreHeadFirstExit ring root S tail
                (bankTrialLocalNext ring root x e) =
                  some true := by
            simpa only [bankTrialC5PreHeadFirstExit,
              if_neg he, if_neg hi] using hgood
          have hpost := ih (bankTrialLocalNext ring root x e) htail
          have hnone :=
            bankTrialSuccessNoActualOriginOfNonroot
              ring root e S x he
          simpa only [bankTrialC5PostHeadFirstExit, hnone]
            using hpost

/-- If the full post-head scanner says GOOD, the first-good
prefix scanner necessarily returns SOME, at the very same horizon.
No future stability or Markov resampling is assumed. -/
theorem bankTrialSuccessPostHeadGoodImpliesFirstGoodSome
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (x : BankTrialLocalState q) :
    ∀ (remaining acc : List (Fin n)),
      bankTrialC5PostHeadFirstExit ring root S
        (acc ++ remaining) x = some true →
      (bankTrialSuccessFirstGoodReturnPrefix
        ring root S x acc remaining).isSome = true := by
  intro remaining
  induction remaining with
  | nil =>
      intro acc hgood
      simp only [List.append_nil] at hgood
      simp [bankTrialSuccessFirstGoodReturnPrefix, hgood]
  | cons e tail ih =>
      intro acc hgood
      by_cases hnow :
          bankTrialC5PostHeadFirstExit ring root S acc x =
            some true
      · simp [bankTrialSuccessFirstGoodReturnPrefix, hnow]
      · have htail :
            bankTrialC5PostHeadFirstExit ring root S
              ((acc ++ [e]) ++ tail) x = some true := by
          simpa only [List.append_assoc,
            List.singleton_append] using hgood
        have hnext := ih (acc ++ [e]) htail
        simpa only [bankTrialSuccessFirstGoodReturnPrefix,
          if_neg hnow] using hnext

/-- A word classified GOOD by the ARMED stage is counted by
the actual first-good-return scanner. -/
theorem bankTrialSuccessArmedStageGoodImpliesFirstGoodSome
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (word : List (Fin n))
    (hgood : bankTrialC5StageClass ring root S x word = .good) :
    (bankTrialSuccessFirstGoodReturnPrefix
      ring root S x [] word).isSome = true := by
  have hpre :
      bankTrialC5PreHeadFirstExit ring root S word x =
        some true := by
    unfold bankTrialC5StageClass at hgood
    split at hgood
    · cases hgood
    · split at hgood
      · assumption
      · split at hgood <;> cases hgood
  have hpost :=
    bankTrialSuccessPreHeadGoodImpliesPostHeadGood
      ring root S word x hpre
  exact bankTrialSuccessPostHeadGoodImpliesFirstGoodSome
    ring root S x word []
    (by simpa only [List.nil_append] using hpost)

/-- Pointwise ARMED good-indicator inclusion. -/
theorem bankTrialSuccessArmedGoodIndicatorLeFirstGood
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (word : List (Fin n)) :
    bankTrialC5StageIndicator
      (bankTrialC5StageClass ring root S x word) .good ≤
    Prob.indicator
      (bankTrialSuccessFirstGoodReturnPrefix
        ring root S x [] word).isSome := by
  by_cases hg :
      bankTrialC5StageClass ring root S x word = .good
  · have hs :=
      bankTrialSuccessArmedStageGoodImpliesFirstGoodSome
        ring root S x word hg
    simp [bankTrialC5StageIndicator, Prob.indicator, hg, hs]
  · simp [bankTrialC5StageIndicator, hg]

/-- Pointwise CSTART good-indicator inclusion. -/
theorem bankTrialSuccessCStartGoodIndicatorLeFirstGood
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (word : List (Fin n)) :
    Prob.indicator (bankTrialC5CStartGoodBool ring root S x word) ≤
    Prob.indicator
      (bankTrialSuccessFirstGoodReturnPrefix
        ring root S x [] word).isSome := by
  by_cases hg :
      bankTrialC5PostHeadFirstExit ring root S word x =
        some true
  · have hs :=
      bankTrialSuccessPostHeadGoodImpliesFirstGoodSome
        ring root S x word []
        (by simpa only [List.nil_append] using hg)
    simp [bankTrialC5CStartGoodBool, Prob.indicator, hg, hs]
  · simp [bankTrialC5CStartGoodBool, Prob.indicator, hg]

/-- Exact ARMED stage-good numerator versus the conditional
first-good-return numerator appearing in the mass-transfer identity. -/
theorem bankTrialSuccessArmedGoodMassLeFirstGoodMass
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (T : Nat) :
    bankTrialC5StageMass ring root S x T .good ≤
    Prob.scheduleSum n T (fun suffix =>
      Prob.indicator
        (bankTrialSuccessFirstGoodReturnPrefix
          ring root S x [] suffix).isSome) := by
  unfold bankTrialC5StageMass
  exact bankTrialProbabilityScheduleSumMono n T _ _
    (bankTrialSuccessArmedGoodIndicatorLeFirstGood ring root S x)

/-- Exact CSTART good numerator versus the same first-good-return
numerator; no ARMED fairness factor is introduced here. -/
theorem bankTrialSuccessCStartGoodMassLeFirstGoodMass
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (T : Nat) :
    bankTrialC5CStartMass ring root S x T (some true) ≤
    Prob.scheduleSum n T (fun suffix =>
      Prob.indicator
        (bankTrialSuccessFirstGoodReturnPrefix
          ring root S x [] suffix).isSome) := by
  change
    Prob.scheduleSum n T (fun suffix =>
      Prob.indicator
        (bankTrialC5CStartGoodBool ring root S x suffix)) ≤
    Prob.scheduleSum n T (fun suffix =>
      Prob.indicator
        (bankTrialSuccessFirstGoodReturnPrefix
          ring root S x [] suffix).isSome)
  exact bankTrialProbabilityScheduleSumMono n T _ _
    (bankTrialSuccessCStartGoodIndicatorLeFirstGood ring root S x)

/-- At an authenticated positive chronological cut, BOTH possible
live seed types satisfy the relevant exact numerator compatibility.
The third possibility is a terminal WON cut. -/
theorem bankTrialSuccessPositiveGoodCutMassCompatibility
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word cut : List (Fin n)) (j : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word (j + 1) = some cut) :
    (∃ begun : Bool,
      (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S)).phase = .live begun ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)).bank = .ARMED ∧
      ∀ t : Nat,
        bankTrialC5StageMass ring root S
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) t .good ≤
          Prob.scheduleSum n t (fun suffix =>
            Prob.indicator
              (bankTrialSuccessFirstGoodReturnPrefix ring root S
                (bankTrialLocalRun ring root cut
                  (bankTrialLocalStart S)) [] suffix).isSome)) ∨
    (∃ begun : Bool,
      (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S)).phase = .live begun ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)).bank = .CSTART ∧
      ∀ t : Nat,
        bankTrialC5CStartMass ring root S
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) t (some true) ≤
          Prob.scheduleSum n t (fun suffix =>
            Prob.indicator
              (bankTrialSuccessFirstGoodReturnPrefix ring root S
                (bankTrialLocalRun ring root cut
                  (bankTrialLocalStart S)) [] suffix).isSome)) ∨
    (bankTrialLocalRun ring root cut
      (bankTrialLocalStart S)).phase = .won := by
  rcases bankTrialSuccessPositiveGoodCutClasses
      ring root S word cut j hcut with
    ⟨begun, hlive, hmode⟩ |
    ⟨begun, hlive, hmode⟩ | hwon
  · exact Or.inl ⟨begun, hlive, hmode, fun t =>
      bankTrialSuccessArmedGoodMassLeFirstGoodMass ring root S
        (bankTrialLocalRun ring root cut (bankTrialLocalStart S)) t⟩
  · exact Or.inr (Or.inl ⟨begun, hlive, hmode, fun t =>
      bankTrialSuccessCStartGoodMassLeFirstGoodMass ring root S
        (bankTrialLocalRun ring root cut (bankTrialLocalStart S)) t⟩)
  · exact Or.inr (Or.inr hwon)

/-- Opaque natural-number substitution for the ARMED stage factor. -/
theorem bankTrialSuccessArmedStageGoodSubstitution
    {D N X G F Q R : Nat}
    (hstage : D * X ≤
      (2 * D * G + 2 * N * X) + (D * Q + 2 * D * R))
    (hgood : G ≤ F) :
    D * X ≤
      (2 * D * F + 2 * N * X) + (D * Q + 2 * D * R) := by
  calc
    D * X ≤
        (2 * D * G + 2 * N * X) + (D * Q + 2 * D * R) :=
      hstage
    _ ≤ (2 * D * F + 2 * N * X) + (D * Q + 2 * D * R) :=
      Nat.add_le_add_right
        (Nat.add_le_add_right
          (Nat.mul_le_mul_left (2 * D) hgood) (2 * N * X))
        (D * Q + 2 * D * R)

/-- Opaque natural-number substitution for the CSTART stage factor. -/
theorem bankTrialSuccessCStartStageGoodSubstitution
    {D N X G F P : Nat}
    (hstage : D * X ≤ D * G + N * X + D * P)
    (hgood : G ≤ F) :
    D * X ≤ D * F + N * X + D * P := by
  calc
    D * X ≤ D * G + N * X + D * P := hstage
    _ ≤ D * F + N * X + D * P :=
      Nat.add_le_add_right
        (Nat.add_le_add_right
          (Nat.mul_le_mul_left D hgood) (N * X))
        (D * P)

/-- Base of the prospective one-tape cut induction: cut zero
exists on every scheduler word, so its total mass is n^T. -/
theorem bankTrialSuccessZeroGoodCutMass
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) :
    Prob.scheduleSum n T (fun word =>
      Prob.indicator
        (bankTrialSuccessGoodReturnCutPrefix
          ring root S word 0).isSome) = n ^ T := by
  have heq :
      (fun word : List (Fin n) =>
        Prob.indicator
          (bankTrialSuccessGoodReturnCutPrefix
            ring root S word 0).isSome) =
      (fun _ => 1) := by
    funext word
    rfl
  rw [heq]
  simpa only [Nat.mul_one] using
    (bankTrialProbabilityScheduleSumConst n T 1)

/-- Every subsequent actual GOOD cut requires the previous cut,
so the cut-reach numerators are monotone on one scheduler tape. -/
theorem bankTrialSuccessGoodCutMassMono
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j T : Nat) :
    Prob.scheduleSum n T (fun word =>
      Prob.indicator
        (bankTrialSuccessGoodReturnCutPrefix
          ring root S word (j + 1)).isSome) ≤
    Prob.scheduleSum n T (fun word =>
      Prob.indicator
        (bankTrialSuccessGoodReturnCutPrefix
          ring root S word j).isSome) := by
  apply bankTrialProbabilityScheduleSumMono n T
  intro word
  cases hj :
      bankTrialSuccessGoodReturnCutPrefix ring root S word j with
  | none =>
      have hnext :
          bankTrialSuccessGoodReturnCutPrefix
            ring root S word (j + 1) = none := by
        simp only [bankTrialSuccessGoodReturnCutPrefix, hj]
      simp [Prob.indicator, hj, hnext]
  | some cut =>
      cases hnext :
          bankTrialSuccessGoodReturnCutPrefix
            ring root S word (j + 1) with
      | none =>
          simp [Prob.indicator, hj, hnext]
      | some nextCut =>
          simp [Prob.indicator, hj, hnext]

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
The recurrence uses one
physical scheduler tape.  In particular the WON cut is charged
separately: a WON cut does not launch another worker.
-/

/-- The literal length-T mass reaching chronological GOOD cut j. -/
noncomputable def bankTrialSuccessCutReachMass
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j T : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    Prob.indicator
      (bankTrialSuccessGoodReturnCutPrefix
        ring root S word j).isSome)

/-- A prefix listed by the actual first-stop enumerator really
satisfies its stopping predicate on its own consumed tape. -/
theorem bankTrialSuccessStoppedPrefixesSound
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool) :
    ∀ (T : Nat) (pre : List (Fin n)) (x : X)
      (cut : List (Fin n)),
      cut ∈ Prob.firstStoppedPrefixes next stop T pre x →
      stop (pre ++ cut) (Prob.stoppedTapeRun next cut x) =
        true := by
  intro T
  induction T with
  | zero =>
      intro pre x cut hmem
      cases hs : stop pre x with
      | false =>
          simp [Prob.firstStoppedPrefixes, hs] at hmem
      | true =>
          have hnil : cut = [] := by
            simpa [Prob.firstStoppedPrefixes, hs] using hmem
          subst cut
          simpa only [List.append_nil, Prob.stoppedTapeRun] using hs
  | succ t ih =>
      intro pre x cut hmem
      cases hs : stop pre x with
      | true =>
          have hnil : cut = [] := by
            simpa [Prob.firstStoppedPrefixes, hs] using hmem
          subst cut
          simpa only [List.append_nil, Prob.stoppedTapeRun] using hs
      | false =>
          have hm :
              cut ∈ (List.ofFn (fun e : Fin n => e)).flatMap
                (fun e =>
                  (Prob.firstStoppedPrefixes next stop t
                    (pre ++ [e]) (next x e)).map (List.cons e)) := by
            simpa only [Prob.firstStoppedPrefixes, hs,
              Bool.false_eq_true, if_false] using hmem
          obtain ⟨e, _, he⟩ := List.mem_flatMap.mp hm
          obtain ⟨tail, htail, hcut⟩ := List.mem_map.mp he
          subst cut
          have hgood := ih (pre ++ [e]) (next x e) tail htail
          simpa only [List.append_assoc, List.singleton_append,
            Prob.stoppedTapeRun] using hgood

/-- The j-th first-stop-prefix enumerator has no forged cuts. -/
theorem bankTrialSuccessStoppedGoodCutAuthenticated
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j T : Nat)
    (cut : List (Fin n))
    (hmem : cut ∈
      Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        T [] (bankTrialLocalStart S)) :
    bankTrialSuccessGoodReturnCutPrefix ring root S cut j =
      some cut := by
  have hs := bankTrialSuccessStoppedPrefixesSound
    (bankTrialLocalNext ring root)
    (bankTrialSuccessGoodReturnCutBool ring root S j)
    T [] (bankTrialLocalStart S) cut hmem
  change decide
    (bankTrialSuccessGoodReturnCutPrefix ring root S cut j =
      some cut) = true at hs
  exact of_decide_eq_true hs

/-- The unit observer expands the mass of the j-th cut into
powers of the remaining *original* word horizon. -/
theorem bankTrialSuccessStoppedUnitSum
    {n : Nat} (T : Nat)
    (cuts : List (List (Fin n))) :
    ((cuts.map (fun cut =>
      Prob.scheduleSum n (T - cut.length)
        (fun _ : List (Fin n) => Prob.indicator true))).sum) =
    ((cuts.map (fun cut => n ^ (T - cut.length))).sum) := by
  induction cuts with
  | nil => rfl
  | cons cut cuts ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      have hc :
          Prob.scheduleSum n (T - cut.length)
              (fun _ : List (Fin n) => Prob.indicator true) =
            n ^ (T - cut.length) := by
        simpa [Prob.indicator] using
          (bankTrialProbabilityScheduleSumConst
            n (T - cut.length) 1)
      rw [hc]

/-- Exact factorization of M_j(T) by its authentic stop prefixes. -/
theorem bankTrialSuccessCutReachMassFactorization
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j T : Nat) :
    bankTrialSuccessCutReachMass ring root S j T =
      ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        T [] (bankTrialLocalStart S)).map (fun cut =>
          n ^ (T - cut.length))).sum := by
  have hword (word : List (Fin n)) :
      Prob.firstStoppedSuffixWord (bankTrialLocalNext ring root)
          (bankTrialSuccessGoodReturnCutBool ring root S j)
          (fun _ _ _ => true) T [] (bankTrialLocalStart S) word =
        (bankTrialSuccessGoodReturnCutPrefix
          ring root S word j).isSome := by
    cases hcut :
        bankTrialSuccessGoodReturnCutPrefix
          ring root S word j with
    | none =>
        have hs := bankTrialSuccessStaticStoppedNone
          ring root S (fun _ _ => true) j word []
          (bankTrialLocalStart S) T rfl
          (by simpa only [List.nil_append] using hcut)
        rw [hs]
        rfl
    | some cut =>
        have hs := bankTrialSuccessStaticStoppedOfGoodCut
          ring root S (fun _ _ => true)
          word cut j T hcut
        rw [hs]
        rfl
  have heq :
      (fun word : List (Fin n) =>
        Prob.indicator
          (bankTrialSuccessGoodReturnCutPrefix
            ring root S word j).isSome) =
      (fun word : List (Fin n) =>
        Prob.indicator
          (Prob.firstStoppedSuffixWord
            (bankTrialLocalNext ring root)
            (bankTrialSuccessGoodReturnCutBool ring root S j)
            (fun _ _ _ => true)
            T [] (bankTrialLocalStart S) word)) := by
    funext word
    exact congrArg Prob.indicator (hword word).symm
  unfold bankTrialSuccessCutReachMass
  rw [heq]
  calc
    Prob.scheduleSum n T (fun word =>
        Prob.indicator
          (Prob.firstStoppedSuffixWord
            (bankTrialLocalNext ring root)
            (bankTrialSuccessGoodReturnCutBool ring root S j)
            (fun _ _ _ => true)
            T [] (bankTrialLocalStart S) word)) =
      ((Prob.firstStoppedPrefixes
          (bankTrialLocalNext ring root)
          (bankTrialSuccessGoodReturnCutBool ring root S j)
          T [] (bankTrialLocalStart S)).map (fun cut =>
        Prob.scheduleSum n (T - cut.length) (fun _ =>
          Prob.indicator true))).sum :=
      Prob.stoppedPrefixFactorization
        (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        (fun _ _ _ => true) (bankTrialLocalStart S) T
        (bankTrialSuccessGoodReturnCutPrefixFree ring root S j)
    _ = _ :=
      bankTrialSuccessStoppedUnitSum T
        (Prob.firstStoppedPrefixes
          (bankTrialLocalNext ring root)
          (bankTrialSuccessGoodReturnCutBool ring root S j)
          T [] (bankTrialLocalStart S))

/-- A cut mass never exceeds the full exact-length-T word count. -/
theorem bankTrialSuccessCutReachMassLeTotal
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j T : Nat) :
    bankTrialSuccessCutReachMass ring root S j T ≤ n ^ T := by
  have hword (w : List (Fin n)) :
      Prob.indicator
        (bankTrialSuccessGoodReturnCutPrefix
          ring root S w j).isSome ≤ 1 := by
    cases hc :
        (bankTrialSuccessGoodReturnCutPrefix
          ring root S w j).isSome <;>
      simp [Prob.indicator, hc]
  calc
    bankTrialSuccessCutReachMass ring root S j T ≤
      Prob.scheduleSum n T (fun _ => 1) := by
        unfold bankTrialSuccessCutReachMass
        exact bankTrialProbabilityScheduleSumMono n T _ _ hword
    _ = n ^ T := by
      simpa only [Nat.mul_one] using
        (bankTrialProbabilityScheduleSumConst n T 1)

/-- The unaveraged local stage charge: ARMED pays Q+2R,
CSTART pays its post-head NONE mass, other modes pay zero. -/
noncomputable def bankTrialSuccessCutPenaltyAt
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (t : Nat) : Nat :=
  if bankTrialLiveWaveRootMode x.bank = .CSTART then
    bankTrialProbabilityC5WorkerDenominator q *
      bankTrialC5CStartMass ring root S x t none
  else if BankTrialProbabilityArmedGate x then
    bankTrialProbabilityC5WorkerDenominator q *
      bankTrialC5PendingBeforeMass ring root S x t +
    2 * bankTrialProbabilityC5WorkerDenominator q *
      bankTrialC5PendingAfterMass ring root S x t
  else 0

/-- Terminal padding from a WON cut; it cannot be omitted when
recurring to cut j+1 because the successful run has absorbed. -/
def bankTrialSuccessCutWonAt {q : Nat}
    (n : Nat) (x : BankTrialLocalState q) (t : Nat) : Nat :=
  if x.phase = .won then n ^ t else 0

/-- Opaque arithmetic: a CSTART bound with factor one implies the
common factor-two bound used for the mixed-stage recurrence. -/
theorem bankTrialSuccessCStartCommonFactor
    {D N X F P : Nat}
    (h : D * X ≤ D * F + N * X + D * P) :
    D * X ≤ (2 * D * F + 2 * N * X) + D * P := by
  have hinflate (a b c : Nat) :
      a + b + c ≤ (2 * a + 2 * b) + c := by
    omega
  exact Nat.le_trans h
    (by simpa only [Nat.mul_assoc] using
      (hinflate (D * F) (N * X) (D * P)))

/-- The actual local inequality is uniform across ARMED, CSTART,
and WON stopping prefixes. The WON contribution is separate.
At a LIVE cut the proof uses the exact installed stage inequality
and the earlier conditional GOOD numerator compatibility. -/
theorem bankTrialSuccessCutLocalForwardOfKernel
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (cut : List (Fin n)) (j t : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S cut j = some cut) :
    bankTrialProbabilityC5WorkerDenominator q * n ^ t ≤
      (2 * bankTrialProbabilityC5WorkerDenominator q *
          Prob.scheduleSum n t (fun suffix =>
            Prob.indicator
              (bankTrialSuccessFirstGoodReturnPrefix ring root S
                (bankTrialLocalRun ring root cut
                  (bankTrialLocalStart S)) [] suffix).isSome) +
        2 * bankTrialProbabilityC5WorkerNumerator q * n ^ t) +
      bankTrialSuccessCutPenaltyAt ring root S
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)) t +
      bankTrialProbabilityC5WorkerDenominator q *
        bankTrialSuccessCutWonAt n
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) t := by
  cases j with
  | zero =>
      have hnil : ([] : List (Fin n)) = cut :=
        Option.some.inj (by
          simpa only [bankTrialSuccessGoodReturnCutPrefix] using hcut)
      subst cut
      have hgate :
          BankTrialProbabilityArmedGate
            (bankTrialLocalStart S) :=
        ⟨⟨false, rfl⟩, hclean.2.1⟩
      have hnc :
          bankTrialLiveWaveRootMode
            (bankTrialLocalStart S).bank ≠ .CSTART := by
        have hm :
            bankTrialLiveWaveRootMode
              (bankTrialLocalStart S).bank = .ARMED :=
          hclean.2.1
        rw [hm]
        intro hc
        cases hc
      have hstage := bankTrialC5OneArmedStage
        ring root S hkernel hlarge hclean []
        (bankTrialLocalStart S) rfl hgate t
      have hgood :=
        bankTrialSuccessArmedGoodMassLeFirstGoodMass
          ring root S (bankTrialLocalStart S) t
      have hsub := bankTrialSuccessArmedStageGoodSubstitution
        hstage hgood
      have hpad := Nat.le_trans hsub
        (Nat.le_add_right _
          (bankTrialProbabilityC5WorkerDenominator q *
            bankTrialSuccessCutWonAt n
              (bankTrialLocalRun ring root []
                (bankTrialLocalStart S)) t))
      have hnil :
          bankTrialLocalRun ring root [] (bankTrialLocalStart S) =
            bankTrialLocalStart S := rfl
      simpa only [List.nil_append, hnil,
        bankTrialSuccessCutPenaltyAt,
        if_neg hnc, if_pos hgate] using hpad
  | succ j =>
      rcases bankTrialSuccessPositiveGoodCutLocalStageCases
          ring root S hkernel hlarge hclean
          cut cut j hcut with
        ⟨begun, hlive, hmode, hstage⟩ |
        ⟨begun, hlive, hmode, hstage⟩ | hwon
      · have hnc :
            bankTrialLiveWaveRootMode
              (bankTrialLocalRun ring root cut
                (bankTrialLocalStart S)).bank ≠ .CSTART := by
          rw [hmode]
          intro hc
          cases hc
        have hgate :
            BankTrialProbabilityArmedGate
              (bankTrialLocalRun ring root cut
                (bankTrialLocalStart S)) :=
          ⟨⟨begun, hlive⟩, hmode⟩
        have hgood :=
          bankTrialSuccessArmedGoodMassLeFirstGoodMass
            ring root S
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) t
        have hsub := bankTrialSuccessArmedStageGoodSubstitution
          (hstage t) hgood
        have hpad := Nat.le_trans hsub
          (Nat.le_add_right _
            (bankTrialProbabilityC5WorkerDenominator q *
              bankTrialSuccessCutWonAt n
                (bankTrialLocalRun ring root cut
                  (bankTrialLocalStart S)) t))
        simpa only [bankTrialSuccessCutPenaltyAt,
          if_neg hnc, if_pos hgate] using hpad
      · have hgood :=
          bankTrialSuccessCStartGoodMassLeFirstGoodMass
            ring root S
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) t
        have hsub := bankTrialSuccessCStartStageGoodSubstitution
          (hstage t) hgood
        have hcommon := bankTrialSuccessCStartCommonFactor hsub
        have hpad := Nat.le_trans hcommon
          (Nat.le_add_right _
            (bankTrialProbabilityC5WorkerDenominator q *
              bankTrialSuccessCutWonAt n
                (bankTrialLocalRun ring root cut
                  (bankTrialLocalStart S)) t))
        simpa only [bankTrialSuccessCutPenaltyAt,
          if_pos hmode] using hpad
      · have hterm :
          bankTrialSuccessCutWonAt n
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) t = n ^ t := by
          simp only [bankTrialSuccessCutWonAt, if_pos hwon]
        rw [hterm]
        exact Nat.le_add_left _ _

/-- Finite list summation of one local inequality. Powers are
entirely opaque to this lemma; it needs only Nat addition. -/
theorem bankTrialSuccessOpaqueStageListSum
    {A : Type} (xs : List A) (D N : Nat)
    (total good penalty won : A → Nat) :
    (∀ x, x ∈ xs →
      D * total x ≤
        (2 * D * good x + 2 * N * total x) +
        penalty x + D * won x) →
    D * (xs.map total).sum ≤
      (2 * D * (xs.map good).sum +
        2 * N * (xs.map total).sum) +
      (xs.map penalty).sum + D * (xs.map won).sum := by
  induction xs with
  | nil =>
      intro _
      simp
  | cons x xs ih =>
      intro h
      have hx := h x (by simp)
      have ht : ∀ y, y ∈ xs →
          D * total y ≤
            (2 * D * good y + 2 * N * total y) +
            penalty y + D * won y := by
        intro y hy
        exact h y (by simp [hy])
      have hsum := Nat.add_le_add hx (ih ht)
      simpa only [List.map_cons, List.sum_cons, Nat.mul_add,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum

/-- The exact original-tape sum of stage-local charges at the
chronological j-th first-stop prefixes. -/
noncomputable def bankTrialSuccessCutPenaltyMass
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j T : Nat) : Nat :=
  ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
    (bankTrialSuccessGoodReturnCutBool ring root S j)
    T [] (bankTrialLocalStart S)).map (fun cut =>
      bankTrialSuccessCutPenaltyAt ring root S
        (bankTrialLocalRun ring root cut (bankTrialLocalStart S))
        (T - cut.length))).sum

/-- Original-tape terminal WON mass at the j-th stopping prefix.
This is charged instead of demanding another worker after WON. -/
noncomputable def bankTrialSuccessCutWonMass
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j T : Nat) : Nat :=
  ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
    (bankTrialSuccessGoodReturnCutBool ring root S j)
    T [] (bankTrialLocalStart S)).map (fun cut =>
      bankTrialSuccessCutWonAt n
        (bankTrialLocalRun ring root cut (bankTrialLocalStart S))
        (T - cut.length))).sum

/-- ONE COMPLETE j-to-(j+1) STOPPED-PREFIX RECURRENCE.
Every included cut is authenticated by the enumerator lemma.
The local stage factor is 2 for ARMED, 1 for CSTART; this
common-factor recurrence uses 2 for both.  The rarity still
multiplies M_j, not an independently restarted full tape.
The terminal WON cut is charged explicitly. -/
theorem bankTrialSuccessCutOneStepOfKernel
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (j T : Nat) :
    bankTrialProbabilityC5WorkerDenominator q *
        bankTrialSuccessCutReachMass ring root S j T ≤
      (2 * bankTrialProbabilityC5WorkerDenominator q *
          bankTrialSuccessCutReachMass ring root S (j + 1) T +
        2 * bankTrialProbabilityC5WorkerNumerator q *
          bankTrialSuccessCutReachMass ring root S j T) +
      bankTrialSuccessCutPenaltyMass ring root S j T +
      bankTrialProbabilityC5WorkerDenominator q *
        bankTrialSuccessCutWonMass ring root S j T := by
  have hcuts (cut : List (Fin n))
      (hmem : cut ∈
        Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
          (bankTrialSuccessGoodReturnCutBool ring root S j)
          T [] (bankTrialLocalStart S)) :
      bankTrialProbabilityC5WorkerDenominator q *
          n ^ (T - cut.length) ≤
        (2 * bankTrialProbabilityC5WorkerDenominator q *
            Prob.scheduleSum n (T - cut.length) (fun suffix =>
              Prob.indicator
                (bankTrialSuccessFirstGoodReturnPrefix ring root S
                  (bankTrialLocalRun ring root cut
                    (bankTrialLocalStart S)) [] suffix).isSome) +
          2 * bankTrialProbabilityC5WorkerNumerator q *
            n ^ (T - cut.length)) +
        bankTrialSuccessCutPenaltyAt ring root S
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) (T - cut.length) +
        bankTrialProbabilityC5WorkerDenominator q *
          bankTrialSuccessCutWonAt n
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) (T - cut.length) := by
    exact bankTrialSuccessCutLocalForwardOfKernel
      ring root S hkernel hlarge hclean cut j
      (T - cut.length)
      (bankTrialSuccessStoppedGoodCutAuthenticated
        ring root S j T cut hmem)
  have hlist := bankTrialSuccessOpaqueStageListSum
    (Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
      (bankTrialSuccessGoodReturnCutBool ring root S j)
      T [] (bankTrialLocalStart S))
    (bankTrialProbabilityC5WorkerDenominator q)
    (bankTrialProbabilityC5WorkerNumerator q)
    (fun cut => n ^ (T - cut.length))
    (fun cut =>
      Prob.scheduleSum n (T - cut.length) (fun suffix =>
        Prob.indicator
          (bankTrialSuccessFirstGoodReturnPrefix ring root S
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) [] suffix).isSome))
    (fun cut => bankTrialSuccessCutPenaltyAt ring root S
      (bankTrialLocalRun ring root cut (bankTrialLocalStart S))
      (T - cut.length))
    (fun cut => bankTrialSuccessCutWonAt n
      (bankTrialLocalRun ring root cut (bankTrialLocalStart S))
      (T - cut.length))
    hcuts
  have hthis :=
    bankTrialSuccessCutReachMassFactorization ring root S j T
  have hnext :
      bankTrialSuccessCutReachMass ring root S (j + 1) T =
        ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
          (bankTrialSuccessGoodReturnCutBool ring root S j)
          T [] (bankTrialLocalStart S)).map (fun cut =>
            Prob.scheduleSum n (T - cut.length) (fun suffix =>
              Prob.indicator
                (bankTrialSuccessFirstGoodReturnPrefix ring root S
                  (bankTrialLocalRun ring root cut
                    (bankTrialLocalStart S)) [] suffix).isSome))).sum := by
    exact bankTrialSuccessNextGoodCutMassTransfer ring root S j T
  rw [hthis, hnext]
  change
    bankTrialProbabilityC5WorkerDenominator q *
      ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        T [] (bankTrialLocalStart S)).map (fun cut =>
          n ^ (T - cut.length))).sum ≤
      (2 * bankTrialProbabilityC5WorkerDenominator q *
        ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
          (bankTrialSuccessGoodReturnCutBool ring root S j)
          T [] (bankTrialLocalStart S)).map (fun cut =>
            Prob.scheduleSum n (T - cut.length) (fun suffix =>
              Prob.indicator
                (bankTrialSuccessFirstGoodReturnPrefix ring root S
                  (bankTrialLocalRun ring root cut
                    (bankTrialLocalStart S)) [] suffix).isSome))).sum +
        2 * bankTrialProbabilityC5WorkerNumerator q *
          ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
            (bankTrialSuccessGoodReturnCutBool ring root S j)
            T [] (bankTrialLocalStart S)).map (fun cut =>
              n ^ (T - cut.length))).sum) +
      ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        T [] (bankTrialLocalStart S)).map (fun cut =>
          bankTrialSuccessCutPenaltyAt ring root S
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S))
            (T - cut.length))).sum +
      bankTrialProbabilityC5WorkerDenominator q *
        ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
          (bankTrialSuccessGoodReturnCutBool ring root S j)
          T [] (bankTrialLocalStart S)).map (fun cut =>
            bankTrialSuccessCutWonAt n
              (bankTrialLocalRun ring root cut
                (bankTrialLocalStart S))
              (T - cut.length))).sum
  exact hlist

/-- Charge the per-cut rarity against the one full-horizon n^T. -/
noncomputable def bankTrialSuccessCutStepDebt
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j T : Nat) : Nat :=
  2 * bankTrialProbabilityC5WorkerNumerator q * n ^ T +
    bankTrialSuccessCutPenaltyMass ring root S j T +
    bankTrialProbabilityC5WorkerDenominator q *
      bankTrialSuccessCutWonMass ring root S j T

theorem bankTrialSuccessCutOneStepGlobalRarity
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (j T : Nat) :
    bankTrialProbabilityC5WorkerDenominator q *
        bankTrialSuccessCutReachMass ring root S j T ≤
      2 * bankTrialProbabilityC5WorkerDenominator q *
        bankTrialSuccessCutReachMass ring root S (j + 1) T +
      bankTrialSuccessCutStepDebt ring root S j T := by
  have hraw :=
    bankTrialSuccessCutOneStepOfKernel
      ring root S hkernel hlarge hclean j T
  have hr :
      2 * bankTrialProbabilityC5WorkerNumerator q *
          bankTrialSuccessCutReachMass ring root S j T ≤
        2 * bankTrialProbabilityC5WorkerNumerator q * n ^ T :=
    Nat.mul_le_mul_left _
      (bankTrialSuccessCutReachMassLeTotal ring root S j T)
  have hbound :=
    Nat.add_le_add_right
      (Nat.add_le_add_right
        (Nat.add_le_add_left hr
          (2 * bankTrialProbabilityC5WorkerDenominator q *
            bankTrialSuccessCutReachMass ring root S (j + 1) T))
        (bankTrialSuccessCutPenaltyMass ring root S j T))
      (bankTrialProbabilityC5WorkerDenominator q *
        bankTrialSuccessCutWonMass ring root S j T)
  have hcombined := Nat.le_trans hraw hbound
  simpa only [bankTrialSuccessCutStepDebt,
    Nat.add_assoc] using hcombined

/-- The exact chronological accumulation of nonnegative stage
debts, with the common worst-case factor two. -/
def bankTrialSuccessWeightedStageDebt
    (debt : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => bankTrialSuccessWeightedStageDebt debt j +
      2 ^ j * debt j

/-- Pure Nat induction on the one-step inequality. No compiled
advice powers occur, and no independence is used. -/
theorem bankTrialSuccessOpaqueStageInduction
    (D : Nat) (mass debt : Nat → Nat)
    (hstep : ∀ j, D * mass j ≤
      2 * D * mass (j + 1) + debt j) :
    ∀ j, D * mass 0 ≤
      2 ^ j * D * mass j +
        bankTrialSuccessWeightedStageDebt debt j := by
  intro j
  induction j with
  | zero =>
      simp [bankTrialSuccessWeightedStageDebt]
  | succ j ih =>
      have hs := Nat.mul_le_mul_left (2 ^ j) (hstep j)
      calc
        D * mass 0 ≤
          2 ^ j * D * mass j +
            bankTrialSuccessWeightedStageDebt debt j := ih
        _ ≤ 2 ^ j *
              (2 * D * mass (j + 1) + debt j) +
            bankTrialSuccessWeightedStageDebt debt j := by
              exact Nat.add_le_add_right
                (by simpa only [Nat.mul_assoc] using hs) _
        _ = 2 ^ (j + 1) * D * mass (j + 1) +
              bankTrialSuccessWeightedStageDebt debt (j + 1) := by
              have hw : bankTrialSuccessWeightedStageDebt debt (j + 1) =
                  bankTrialSuccessWeightedStageDebt debt j +
                    2 ^ j * debt j := rfl
              rw [hw, Nat.mul_add, Nat.pow_succ,
                Nat.mul_assoc 2 D (mass (j + 1)),
                Nat.mul_assoc (2 ^ j * 2) D (mass (j + 1)),
                Nat.mul_assoc (2 ^ j) 2 (D * mass (j + 1))]
              omega

/-- The requested induction over chronological j (hence also for
j <= 2K+1). The charges remain explicit; proving the sharp 2^K
completed-head estimate requires the separate head-slot alignment,
a terminal-not-completed bound, and a single pending Markov charge. -/
theorem bankTrialSuccessCutInductionOfKernel
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (j T : Nat) :
    bankTrialProbabilityC5WorkerDenominator q * n ^ T ≤
      2 ^ j * bankTrialProbabilityC5WorkerDenominator q *
        bankTrialSuccessCutReachMass ring root S j T +
      bankTrialSuccessWeightedStageDebt
        (fun i => bankTrialSuccessCutStepDebt ring root S i T) j := by
  have hstep (i : Nat) :
      bankTrialProbabilityC5WorkerDenominator q *
          bankTrialSuccessCutReachMass ring root S i T ≤
        2 * bankTrialProbabilityC5WorkerDenominator q *
          bankTrialSuccessCutReachMass ring root S (i + 1) T +
        bankTrialSuccessCutStepDebt ring root S i T :=
    bankTrialSuccessCutOneStepGlobalRarity
      ring root S hkernel hlarge hclean i T
  have hind := bankTrialSuccessOpaqueStageInduction
    (bankTrialProbabilityC5WorkerDenominator q)
    (fun i => bankTrialSuccessCutReachMass ring root S i T)
    (fun i => bankTrialSuccessCutStepDebt ring root S i T)
    hstep j
  have hzero :
      bankTrialSuccessCutReachMass ring root S 0 T =
        n ^ T :=
    bankTrialSuccessZeroGoodCutMass ring root S T
  rw [hzero] at hind
  exact hind


/-!
Sharp-factor work.  The following typed arithmetic
recurrence is unconditional given its one-step hypotheses.  The
machine-level CSTART inequality below genuinely has coefficient ONE;
no factor-two "common factor" is used in its proof.  The mode split
is over the actual one-tape j-th cut, not fresh scheduler samples.
There is no asserted final completed-head bound here.
-/

/-- An authenticated live ARMED cut has one fair-bit factor two. -/
theorem bankTrialSuccessCutArmedStageFactorTwo
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (cut : List (Fin n)) (t : Nat)
    (hgate : BankTrialProbabilityArmedGate
      (bankTrialLocalRun ring root cut (bankTrialLocalStart S))) :
    bankTrialProbabilityC5WorkerDenominator q * n ^ t ≤
      (2 * bankTrialProbabilityC5WorkerDenominator q *
          Prob.scheduleSum n t (fun suffix =>
            Prob.indicator
              (bankTrialSuccessFirstGoodReturnPrefix ring root S
                (bankTrialLocalRun ring root cut
                  (bankTrialLocalStart S)) [] suffix).isSome) +
        2 * bankTrialProbabilityC5WorkerNumerator q * n ^ t) +
      (bankTrialProbabilityC5WorkerDenominator q *
          bankTrialC5PendingBeforeMass ring root S
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) t +
        2 * bankTrialProbabilityC5WorkerDenominator q *
          bankTrialC5PendingAfterMass ring root S
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) t) := by
  exact bankTrialSuccessArmedStageGoodSubstitution
    (bankTrialC5OneArmedStage
      ring root S hkernel hlarge hclean cut
      (bankTrialLocalRun ring root cut (bankTrialLocalStart S))
      rfl hgate t)
    (bankTrialSuccessArmedGoodMassLeFirstGoodMass
      ring root S
      (bankTrialLocalRun ring root cut (bankTrialLocalStart S)) t)

/-- At a live CSTART GOOD cut, no fair-bit factor is incurred. -/
theorem bankTrialSuccessCutCStartStageFactorOne
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (cut : List (Fin n)) (j t : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S cut j = some cut)
    (begun : Bool)
    (hlive : (bankTrialLocalRun ring root cut
      (bankTrialLocalStart S)).phase = .live begun)
    (hmode : bankTrialLiveWaveRootMode
      (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S)).bank = .CSTART) :
    bankTrialProbabilityC5WorkerDenominator q * n ^ t ≤
      bankTrialProbabilityC5WorkerDenominator q *
        Prob.scheduleSum n t (fun suffix =>
          Prob.indicator
            (bankTrialSuccessFirstGoodReturnPrefix ring root S
              (bankTrialLocalRun ring root cut
                (bankTrialLocalStart S)) [] suffix).isSome) +
      bankTrialProbabilityC5WorkerNumerator q * n ^ t +
      bankTrialProbabilityC5WorkerDenominator q *
        bankTrialC5CStartMass ring root S
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) t none := by
  cases j with
  | zero =>
      have hnil : ([] : List (Fin n)) = cut :=
        Option.some.inj (by
          simpa only [bankTrialSuccessGoodReturnCutPrefix] using hcut)
      subst cut
      change bankTrialLiveWaveRootMode
        (bankTrialLocalStart S).bank = .CSTART at hmode
      have hm : bankTrialLiveWaveRootMode
          (bankTrialLocalStart S).bank = .ARMED := hclean.2.1
      rw [hm] at hmode
      cases hmode
  | succ j =>
      rcases bankTrialSuccessPositiveGoodCutLocalStageCases
          ring root S hkernel hlarge hclean
          cut cut j hcut with
        ⟨otherBegun, hphase, harmed, hstage⟩ |
        ⟨otherBegun, hphase, hcstart, hstage⟩ | hwon
      · rw [hmode] at harmed
        cases harmed
      · exact bankTrialSuccessCStartStageGoodSubstitution
          (hstage t)
          (bankTrialSuccessCStartGoodMassLeFirstGoodMass
            ring root S
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) t)
      · rw [hwon] at hlive
        cases hlive

/-- LIVE CSTART, unlike a terminal WON state. -/
def bankTrialSuccessCutCStartGate {q : Nat}
    (x : BankTrialLocalState q) : Prop :=
  (∃ begun : Bool, x.phase = .live begun) ∧
    bankTrialLiveWaveRootMode x.bank = .CSTART

/-- Every actual j-th GOOD return has one of these modes. -/
theorem bankTrialSuccessCutModeTrichotomy
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (word cut : List (Fin n)) (j : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word j = some cut) :
    BankTrialProbabilityArmedGate
      (bankTrialLocalRun ring root cut (bankTrialLocalStart S)) ∨
    bankTrialSuccessCutCStartGate
      (bankTrialLocalRun ring root cut (bankTrialLocalStart S)) ∨
    (bankTrialLocalRun ring root cut
      (bankTrialLocalStart S)).phase = .won := by
  cases j with
  | zero =>
      have hnil : ([] : List (Fin n)) = cut :=
        Option.some.inj (by
          simpa only [bankTrialSuccessGoodReturnCutPrefix] using hcut)
      subst cut
      exact Or.inl ⟨⟨false, rfl⟩, hclean.2.1⟩
  | succ j =>
      rcases bankTrialSuccessPositiveGoodCutClasses
          ring root S word cut j hcut with
        ⟨begun, hlive, hmode⟩ |
        ⟨begun, hlive, hmode⟩ | hwon
      · exact Or.inl ⟨⟨begun, hlive⟩, hmode⟩
      · exact Or.inr (Or.inl ⟨⟨begun, hlive⟩, hmode⟩)
      · exact Or.inr (Or.inr hwon)

/-- The mode predicates are disjoint and exhaust authentic cuts. -/
theorem bankTrialSuccessCutModePartition
    {q : Nat} (x : BankTrialLocalState q)
    (hcase : BankTrialProbabilityArmedGate x ∨
      bankTrialSuccessCutCStartGate x ∨ x.phase = .won) :
    (if BankTrialProbabilityArmedGate x then 1 else 0) +
      (if bankTrialSuccessCutCStartGate x then 1 else 0) +
      (if x.phase = .won then 1 else 0) = 1 := by
  rcases hcase with harmed | hcstart | hwon
  · have hnotc : ¬ bankTrialSuccessCutCStartGate x := by
      intro hc
      have hm := hc.2
      have hm2 := harmed.2.symm.trans hm
      cases hm2
    have hnotw : x.phase ≠ .won := by
      intro hw
      obtain ⟨begun, hlive⟩ := harmed.1
      rw [hw] at hlive
      cases hlive
    simp [harmed, hnotc, hnotw]
  · have hnota : ¬ BankTrialProbabilityArmedGate x := by
      intro ha
      have hm := hcstart.2
      have hm2 := ha.2.symm.trans hm
      cases hm2
    have hnotw : x.phase ≠ .won := by
      intro hw
      obtain ⟨begun, hlive⟩ := hcstart.1
      rw [hw] at hlive
      cases hlive
    simp [hnota, hcstart, hnotw]
  · have hnota : ¬ BankTrialProbabilityArmedGate x := by
      intro ha
      obtain ⟨begun, hlive⟩ := ha.1
      rw [hwon] at hlive
      cases hlive
    have hnotc : ¬ bankTrialSuccessCutCStartGate x := by
      intro hc
      obtain ⟨begun, hlive⟩ := hc.1
      rw [hwon] at hlive
      cases hlive
    simp [hnota, hnotc, hwon]

/-- Three *disjoint* indicators of a reached cut's root mode. -/
noncomputable def bankTrialSuccessCutArmedWordMass
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (word : List (Fin n)) (j : Nat) : Nat :=
  match bankTrialSuccessGoodReturnCutPrefix ring root S word j with
  | none => 0
  | some cut =>
      if BankTrialProbabilityArmedGate
          (bankTrialLocalRun ring root cut (bankTrialLocalStart S))
      then 1 else 0

noncomputable def bankTrialSuccessCutCStartWordMass
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (word : List (Fin n)) (j : Nat) : Nat :=
  match bankTrialSuccessGoodReturnCutPrefix ring root S word j with
  | none => 0
  | some cut =>
      if bankTrialSuccessCutCStartGate
          (bankTrialLocalRun ring root cut (bankTrialLocalStart S))
      then 1 else 0

noncomputable def bankTrialSuccessCutWonWordMass
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (word : List (Fin n)) (j : Nat) : Nat :=
  match bankTrialSuccessGoodReturnCutPrefix ring root S word j with
  | none => 0
  | some cut =>
      if (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S)).phase = .won then 1 else 0

theorem bankTrialSuccessCutWordModePartition
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (word : List (Fin n)) (j : Nat) :
    Prob.indicator
        (bankTrialSuccessGoodReturnCutPrefix
          ring root S word j).isSome =
      bankTrialSuccessCutArmedWordMass ring root S word j +
      bankTrialSuccessCutCStartWordMass ring root S word j +
      bankTrialSuccessCutWonWordMass ring root S word j := by
  cases hc : bankTrialSuccessGoodReturnCutPrefix
      ring root S word j with
  | none =>
      simp only [bankTrialSuccessCutArmedWordMass,
        bankTrialSuccessCutCStartWordMass,
        bankTrialSuccessCutWonWordMass, hc] <;> rfl
  | some cut =>
      have hcase :=
        bankTrialSuccessCutModeTrichotomy
          ring root S hclean word cut j hc
      simp only [bankTrialSuccessCutArmedWordMass,
        bankTrialSuccessCutCStartWordMass,
        bankTrialSuccessCutWonWordMass, hc]
      exact (bankTrialSuccessCutModePartition _ hcase).symm

noncomputable def bankTrialSuccessCutArmedMass
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j T : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    bankTrialSuccessCutArmedWordMass ring root S word j)

noncomputable def bankTrialSuccessCutCStartMass
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j T : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    bankTrialSuccessCutCStartWordMass ring root S word j)

noncomputable def bankTrialSuccessCutWonModeMass
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j T : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    bankTrialSuccessCutWonWordMass ring root S word j)

/-- The chronological M_j really splits by root mode on ONE tape. -/
theorem bankTrialSuccessCutModeMassSplit
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (j T : Nat) :
    bankTrialSuccessCutReachMass ring root S j T =
      bankTrialSuccessCutArmedMass ring root S j T +
      bankTrialSuccessCutCStartMass ring root S j T +
      bankTrialSuccessCutWonModeMass ring root S j T := by
  unfold bankTrialSuccessCutReachMass
    bankTrialSuccessCutArmedMass
    bankTrialSuccessCutCStartMass
    bankTrialSuccessCutWonModeMass
  calc
    Prob.scheduleSum n T (fun word =>
        Prob.indicator
          (bankTrialSuccessGoodReturnCutPrefix
            ring root S word j).isSome) =
      Prob.scheduleSum n T (fun word =>
        bankTrialSuccessCutArmedWordMass ring root S word j +
        bankTrialSuccessCutCStartWordMass ring root S word j +
        bankTrialSuccessCutWonWordMass ring root S word j) := by
          apply congrArg (Prob.scheduleSum n T)
          funext word
          exact bankTrialSuccessCutWordModePartition
            ring root S hclean word j
    _ = _ := by
      rw [bankTrialC5ScheduleSumAdd, bankTrialC5ScheduleSumAdd]

/-- A typed recurrence factor.  False means an uncharged CSTART cut. -/
def bankTrialSuccessTypedStageFactor
    (armed : Nat → Bool) : Nat → Nat
  | 0 => 1
  | j + 1 => bankTrialSuccessTypedStageFactor armed j *
      (if armed j then 2 else 1)

/-- Debt is multiplied only by the preceding decision factors. -/
def bankTrialSuccessTypedStageDebt
    (armed : Nat → Bool) (debt : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => bankTrialSuccessTypedStageDebt armed debt j +
      bankTrialSuccessTypedStageFactor armed j * debt j

def bankTrialSuccessArmedStageCount
    (armed : Nat → Bool) : Nat → Nat
  | 0 => 0
  | j + 1 => bankTrialSuccessArmedStageCount armed j +
      (if armed j then 1 else 0)

/-- The common factor is exactly 2 to the number of ARMED cuts. -/
theorem bankTrialSuccessTypedStageFactorPow
    (armed : Nat → Bool) :
    ∀ j, bankTrialSuccessTypedStageFactor armed j =
      2 ^ bankTrialSuccessArmedStageCount armed j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
      calc
        bankTrialSuccessTypedStageFactor armed (j + 1) =
          bankTrialSuccessTypedStageFactor armed j *
            (if armed j then 2 else 1) := rfl
        _ = 2 ^ bankTrialSuccessArmedStageCount armed j *
              (if armed j then 2 else 1) := by rw [ih]
        _ = 2 ^ bankTrialSuccessArmedStageCount armed (j + 1) := by
            cases h : armed j with
            | false =>
                simp only [bankTrialSuccessArmedStageCount, h,
                  Bool.false_eq_true, ite_false, Nat.add_zero,
                  Nat.mul_one]
            | true =>
                simp only [bankTrialSuccessArmedStageCount, h,
                  ite_true, Nat.pow_succ]

/-- Abstract two-type product induction; no terminal leaf is assumed. -/
theorem bankTrialSuccessTypedStageInduction
    (D : Nat) (mass debt : Nat → Nat) (armed : Nat → Bool)
    (hstep : ∀ j, D * mass j ≤
      (if armed j then 2 else 1) *
        D * mass (j + 1) + debt j) :
    ∀ j, D * mass 0 ≤
      bankTrialSuccessTypedStageFactor armed j *
        D * mass j +
      bankTrialSuccessTypedStageDebt armed debt j := by
  intro j
  induction j with
  | zero =>
      simp [bankTrialSuccessTypedStageFactor,
        bankTrialSuccessTypedStageDebt]
  | succ j ih =>
      have hs := Nat.mul_le_mul_left
        (bankTrialSuccessTypedStageFactor armed j) (hstep j)
      calc
        D * mass 0 ≤
          bankTrialSuccessTypedStageFactor armed j *
            D * mass j +
          bankTrialSuccessTypedStageDebt armed debt j := ih
        _ ≤ bankTrialSuccessTypedStageFactor armed j *
              ((if armed j then 2 else 1) *
                D * mass (j + 1) + debt j) +
            bankTrialSuccessTypedStageDebt armed debt j := by
              exact Nat.add_le_add_right
                (by simpa only [Nat.mul_assoc] using hs) _
        _ = bankTrialSuccessTypedStageFactor armed (j + 1) *
              D * mass (j + 1) +
            bankTrialSuccessTypedStageDebt armed debt (j + 1) := by
              simp only [bankTrialSuccessTypedStageFactor,
                bankTrialSuccessTypedStageDebt,
                Nat.mul_add, Nat.mul_assoc, Nat.add_assoc,
                Nat.add_left_comm, Nat.add_comm]

theorem bankTrialSuccessTypedStageInductionPower
    (D : Nat) (mass debt : Nat → Nat) (armed : Nat → Bool)
    (hstep : ∀ j, D * mass j ≤
      (if armed j then 2 else 1) *
        D * mass (j + 1) + debt j) :
    ∀ j, D * mass 0 ≤
      2 ^ bankTrialSuccessArmedStageCount armed j *
        D * mass j +
      bankTrialSuccessTypedStageDebt armed debt j := by
  intro j
  have h := bankTrialSuccessTypedStageInduction
    D mass debt armed hstep j
  rw [bankTrialSuccessTypedStageFactorPow armed j] at h
  exact h

/-- An ideal nonterminal good-return sequence alternates
ARMED, CSTART, ARMED, CSTART, ... .  This is NOT an assertion that
the actual cut tree has this mode sequence after mixed failures. -/
def bankTrialSuccessAlternatingArmed : Nat → Bool
  | 0 => true
  | j + 1 => ! bankTrialSuccessAlternatingArmed j

theorem bankTrialSuccessAlternatingArmedEven (j : Nat) :
    bankTrialSuccessAlternatingArmed (2 * j) = true := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have hs : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
      rw [hs]
      change (! (! bankTrialSuccessAlternatingArmed (2 * j))) = true
      rw [ih]
      rfl

/-- In exactly 2K alternating preterminal cuts, there are K
ARMED head decisions. -/
theorem bankTrialSuccessAlternatingArmedCountEven (K : Nat) :
    bankTrialSuccessArmedStageCount
      bankTrialSuccessAlternatingArmed (2 * K) = K := by
  induction K with
  | zero => rfl
  | succ K ih =>
      have hs : 2 * (K + 1) = (2 * K + 1) + 1 := by omega
      have hodd :
          bankTrialSuccessAlternatingArmed (2 * K + 1) = false := by
        change (! bankTrialSuccessAlternatingArmed (2 * K)) = false
        rw [bankTrialSuccessAlternatingArmedEven K]
        rfl
      calc
        bankTrialSuccessArmedStageCount
            bankTrialSuccessAlternatingArmed (2 * (K + 1)) =
          (bankTrialSuccessArmedStageCount
              bankTrialSuccessAlternatingArmed (2 * K) +
            (if bankTrialSuccessAlternatingArmed (2 * K)
             then 1 else 0)) +
          (if bankTrialSuccessAlternatingArmed (2 * K + 1)
           then 1 else 0) := by
              rw [hs]
              rfl
        _ = K + 1 := by
          rw [ih, bankTrialSuccessAlternatingArmedEven K, hodd]
          rfl

/-- Blindly charging a further even-index ARMED stage yields K+1.
A terminal WON comparator at K must suppress that extra charge. -/
theorem bankTrialSuccessAlternatingArmedCountOdd (K : Nat) :
    bankTrialSuccessArmedStageCount
      bankTrialSuccessAlternatingArmed (2 * K + 1) = K + 1 := by
  calc
    bankTrialSuccessArmedStageCount
        bankTrialSuccessAlternatingArmed (2 * K + 1) =
      bankTrialSuccessArmedStageCount
        bankTrialSuccessAlternatingArmed (2 * K) +
        (if bankTrialSuccessAlternatingArmed (2 * K)
         then 1 else 0) := rfl
    _ = K + 1 := by
      rw [bankTrialSuccessAlternatingArmedCountEven K,
        bankTrialSuccessAlternatingArmedEven K]
      rfl

theorem bankTrialSuccessAlternatingFactorEven (K : Nat) :
    bankTrialSuccessTypedStageFactor
      bankTrialSuccessAlternatingArmed (2 * K) = 2 ^ K := by
  rw [bankTrialSuccessTypedStageFactorPow,
    bankTrialSuccessAlternatingArmedCountEven]

end L3

#print axioms L3.bankTrialSuccessStoppedPrefixesSound
#print axioms L3.bankTrialSuccessStoppedGoodCutAuthenticated
#print axioms L3.bankTrialSuccessStoppedUnitSum
#print axioms L3.bankTrialSuccessCutReachMassFactorization
#print axioms L3.bankTrialSuccessCutReachMassLeTotal
#print axioms L3.bankTrialSuccessCStartCommonFactor
#print axioms L3.bankTrialSuccessCutLocalForwardOfKernel
#print axioms L3.bankTrialSuccessOpaqueStageListSum
#print axioms L3.bankTrialSuccessCutOneStepOfKernel
#print axioms L3.bankTrialSuccessCutOneStepGlobalRarity
#print axioms L3.bankTrialSuccessOpaqueStageInduction
#print axioms L3.bankTrialSuccessCutInductionOfKernel
#print axioms L3.bankTrialSuccessCutArmedStageFactorTwo
#print axioms L3.bankTrialSuccessCutCStartStageFactorOne
#print axioms L3.bankTrialSuccessCutModeTrichotomy
#print axioms L3.bankTrialSuccessCutModePartition
#print axioms L3.bankTrialSuccessCutWordModePartition
#print axioms L3.bankTrialSuccessCutModeMassSplit
#print axioms L3.bankTrialSuccessTypedStageFactorPow
#print axioms L3.bankTrialSuccessTypedStageInduction
#print axioms L3.bankTrialSuccessTypedStageInductionPower
#print axioms L3.bankTrialSuccessAlternatingArmedEven
#print axioms L3.bankTrialSuccessAlternatingArmedCountEven
#print axioms L3.bankTrialSuccessAlternatingArmedCountOdd
#print axioms L3.bankTrialSuccessAlternatingFactorEven

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
The count below is chronological: every i<j
contributes the ARMED indicator at the ACTUAL i-th GOOD cut of the
same finite physical word.  The prefix-stability theorem uses the
existing exact scanner and no fresh scheduler tape.
-/

/-- The number of ARMED roots at earlier authenticated GOOD cuts. -/
noncomputable def bankTrialSuccessCutHistoryArmedCount
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (word : List (Fin n)) (j : Nat) : Nat :=
  bankTrialSuccessStageIndexSum
    (fun i => bankTrialSuccessCutArmedWordMass ring root S word i) j

/-- The requested original-horizon path-weighted mass. -/
noncomputable def bankTrialSuccessCutHistoryWeightedMass
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j T : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    Prob.indicator
      (bankTrialSuccessGoodReturnCutPrefix
        ring root S word j).isSome *
      2 ^ bankTrialSuccessCutHistoryArmedCount
        ring root S word j)

/-- Requested (1): at cut zero every scheduler word is present
with weight 2^0=1.  No kernel hypothesis is needed. -/
theorem bankTrialSuccessCutHistoryWeightedMassZero
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) :
    bankTrialSuccessCutHistoryWeightedMass ring root S 0 T =
      n ^ T := by
  change Prob.scheduleSum n T
    (fun _ : List (Fin n) => 1) = n ^ T
  simpa only [Nat.mul_one] using
    (bankTrialProbabilityScheduleSumConst n T 1)

/-- A later existing GOOD cut implies that every earlier cut exists.
This is the contrapositive of the installed no-cut-above theorem. -/
theorem bankTrialSuccessCutHistoryEarlierExists
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word cut : List (Fin n)) (i j : Nat)
    (hi : i ≤ j)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word j = some cut) :
    ∃ prev : List (Fin n),
      bankTrialSuccessGoodReturnCutPrefix
        ring root S word i = some prev := by
  cases hprev :
      bankTrialSuccessGoodReturnCutPrefix
        ring root S word i with
  | some prev =>
      exact ⟨prev, rfl⟩
  | none =>
      have hnone :=
        bankTrialSuccessGoodReturnCutNoneAbove
          ring root S word i hprev j hi
      rw [hcut] at hnone
      cases hnone

/-- Earlier ARMED indicators are unchanged by appending any suffix
AFTER an authenticated j-th cut. -/
theorem bankTrialSuccessCutHistoryArmedAppend
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (cut suffix : List (Fin n)) (i j : Nat)
    (hi : i ≤ j)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S cut j = some cut) :
    bankTrialSuccessCutArmedWordMass
      ring root S (cut ++ suffix) i =
    bankTrialSuccessCutArmedWordMass
      ring root S cut i := by
  obtain ⟨prev, hprev⟩ :=
    bankTrialSuccessCutHistoryEarlierExists
      ring root S cut cut i j hi hcut
  have hext :=
    bankTrialSuccessGoodReturnCutAppend
      ring root S i cut prev suffix hprev
  simp only [bankTrialSuccessCutArmedWordMass, hprev, hext]

/-- Finite indexed sums respect equality of terms below their bound.
This uses only core Nat and the existing recursive stage sum. -/
theorem bankTrialSuccessCutHistorySumExt
    (f g : Nat → Nat) :
    ∀ j : Nat, (∀ i, i < j → f i = g i) →
      bankTrialSuccessStageIndexSum f j =
      bankTrialSuccessStageIndexSum g j := by
  intro j
  induction j with
  | zero =>
      intro _
      rfl
  | succ j ih =>
      intro h
      change bankTrialSuccessStageIndexSum f j + f j =
        bankTrialSuccessStageIndexSum g j + g j
      rw [ih (fun i hi => h i (by omega)), h j (by omega)]

/-- PREFIX LOCALITY: all earlier mode indicators, hence their sum,
are determined by the authenticated j-th cut prefix. -/
theorem bankTrialSuccessCutHistoryCountAppend
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (cut suffix : List (Fin n)) (j : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S cut j = some cut) :
    bankTrialSuccessCutHistoryArmedCount
      ring root S (cut ++ suffix) j =
    bankTrialSuccessCutHistoryArmedCount
      ring root S cut j := by
  unfold bankTrialSuccessCutHistoryArmedCount
  exact bankTrialSuccessCutHistorySumExt
    (fun i => bankTrialSuccessCutArmedWordMass
      ring root S (cut ++ suffix) i)
    (fun i => bankTrialSuccessCutArmedWordMass
      ring root S cut i)
    j (fun i hi =>
      bankTrialSuccessCutHistoryArmedAppend
        ring root S cut suffix i j
        (by omega) hcut)

/-- The count computed on a full word equals its value on the
actual stopped prefix.  Both are on the same scheduler tape. -/
theorem bankTrialSuccessCutHistoryCountAtCut
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word cut : List (Fin n)) (j : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word j = some cut) :
    bankTrialSuccessCutHistoryArmedCount
      ring root S word j =
    bankTrialSuccessCutHistoryArmedCount
      ring root S cut j := by
  obtain ⟨suffix, hword⟩ :=
    bankTrialSuccessGoodReturnCutIsPrefix
      ring root S word j cut hcut
  have hself :=
    bankTrialSuccessGoodReturnCutSelf
      ring root S word j cut hcut
  rw [hword]
  exact bankTrialSuccessCutHistoryCountAppend
    ring root S cut suffix j hself

/-- The next history count changes by precisely the mode indicator
at the present cut. -/
theorem bankTrialSuccessCutHistoryCountSucc
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word : List (Fin n)) (j : Nat) :
    bankTrialSuccessCutHistoryArmedCount
      ring root S word (j + 1) =
    bankTrialSuccessCutHistoryArmedCount
      ring root S word j +
    bankTrialSuccessCutArmedWordMass
      ring root S word j := by
  rfl

/-- At an existing cut, the last summand is EXACTLY one in
LIVE/ARMED mode and zero otherwise, including WON. -/
theorem bankTrialSuccessCutHistoryModeAtCut
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word cut : List (Fin n)) (j : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word j = some cut) :
    bankTrialSuccessCutArmedWordMass ring root S word j =
      (if BankTrialProbabilityArmedGate
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) then 1 else 0) := by
  simp only [bankTrialSuccessCutArmedWordMass, hcut]

/-- The requested power update.  There is no fair-bit factor
at a CSTART or WON cut. -/
theorem bankTrialSuccessCutHistoryPowerSucc
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word cut : List (Fin n)) (j : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word j = some cut) :
    2 ^ bankTrialSuccessCutHistoryArmedCount
        ring root S word (j + 1) =
      2 ^ bankTrialSuccessCutHistoryArmedCount
        ring root S cut j *
      (if BankTrialProbabilityArmedGate
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) then 2 else 1) := by
  rw [bankTrialSuccessCutHistoryCountSucc,
    bankTrialSuccessCutHistoryModeAtCut
      ring root S word cut j hcut,
    bankTrialSuccessCutHistoryCountAtCut
      ring root S word cut j hcut]
  by_cases hg : BankTrialProbabilityArmedGate
      (bankTrialLocalRun ring root cut (bankTrialLocalStart S))
  · simp only [if_pos hg, Nat.pow_succ]
  · simp only [if_neg hg, Nat.add_zero, Nat.mul_one]

/-- A uniform path-count bound independent of any comparator rows:
each of the j earlier cuts can contribute only zero or one. -/
theorem bankTrialSuccessCutHistoryCountLeIndex
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word : List (Fin n)) :
    ∀ j, bankTrialSuccessCutHistoryArmedCount
      ring root S word j ≤ j := by
  intro j
  induction j with
  | zero =>
      exact Nat.zero_le _
  | succ j ih =>
      have hu : bankTrialSuccessCutArmedWordMass
          ring root S word j ≤ 1 := by
        cases hc : bankTrialSuccessGoodReturnCutPrefix
            ring root S word j with
        | none =>
            simp [bankTrialSuccessCutArmedWordMass, hc]
        | some cut =>
            simp only [bankTrialSuccessCutArmedWordMass, hc]
            split <;> omega
      rw [bankTrialSuccessCutHistoryCountSucc]
      omega

/-- Arithmetic-only rarity inflation: CSTART costs N, but it can
be safely charged 2N in a uniform debt. -/
theorem bankTrialSuccessCutHistoryRarityInflate
    (a b c d : Nat) (h : a ≤ b + c + d) :
    a ≤ (b + 2 * c) + d := by
  omega

/-- Small mode fact; never unfold the stopped cut scanner here. -/
private theorem bankTrialSuccessCutHistoryArmedNotCStart
    {q : Nat} (x : BankTrialLocalState q)
    (harmed : BankTrialProbabilityArmedGate x) :
    bankTrialLiveWaveRootMode x.bank ≠ .CSTART := by
  intro hc
  have hm : bankTrialLiveWaveRootMode x.bank = .ARMED :=
    harmed.2
  rw [hm] at hc
  cases hc

/-- The ARMED penalty branch, stated with an opaque local state. -/
theorem bankTrialSuccessCutHistoryPenaltyArmed
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (t : Nat)
    (harmed : BankTrialProbabilityArmedGate x) :
    bankTrialSuccessCutPenaltyAt ring root S x t =
      bankTrialProbabilityC5WorkerDenominator q *
        bankTrialC5PendingBeforeMass ring root S x t +
      2 * bankTrialProbabilityC5WorkerDenominator q *
        bankTrialC5PendingAfterMass ring root S x t := by
  unfold bankTrialSuccessCutPenaltyAt
  rw [if_neg (bankTrialSuccessCutHistoryArmedNotCStart
    x harmed), if_pos harmed]

/-- The CSTART penalty branch, without unfolding any local run. -/
theorem bankTrialSuccessCutHistoryPenaltyCStart
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (t : Nat)
    (hmode : bankTrialLiveWaveRootMode x.bank = .CSTART) :
    bankTrialSuccessCutPenaltyAt ring root S x t =
      bankTrialProbabilityC5WorkerDenominator q *
        bankTrialC5CStartMass ring root S x t none := by
  unfold bankTrialSuccessCutPenaltyAt
  rw [if_pos hmode]

/-- The only multiplication reassociation needed in CSTART.
All arithmetic arguments are opaque Nat variables. -/
theorem bankTrialSuccessCutHistoryDoubleMul
    (N X : Nat) : 2 * (N * X) = 2 * N * X :=
  (Nat.mul_assoc 2 N X).symm


/-- Exactly the ONE fair-bit factor at ARMED; coefficient ONE at
CSTART; terminal WON is paid separately instead of starting a worker.
The preexisting actual-mode cut trichotomy is used, not an
unproved generic stage classification. -/
theorem bankTrialSuccessCutHistoryLocalStage
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (cut : List (Fin n)) (j t : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S cut j = some cut) :
    bankTrialProbabilityC5WorkerDenominator q * n ^ t ≤
      ((if BankTrialProbabilityArmedGate
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) then 2 else 1) *
        bankTrialProbabilityC5WorkerDenominator q *
        Prob.scheduleSum n t (fun suffix =>
          Prob.indicator
            (bankTrialSuccessFirstGoodReturnPrefix ring root S
              (bankTrialLocalRun ring root cut
                (bankTrialLocalStart S)) [] suffix).isSome) +
        2 * bankTrialProbabilityC5WorkerNumerator q * n ^ t) +
      bankTrialSuccessCutPenaltyAt ring root S
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)) t +
      bankTrialProbabilityC5WorkerDenominator q *
        bankTrialSuccessCutWonAt n
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) t := by
  rcases bankTrialSuccessCutModeTrichotomy
      ring root S hclean cut cut j hcut with
    harmed | hcstart | hwon
  · have hlocal := bankTrialSuccessCutArmedStageFactorTwo
      ring root S hkernel hlarge hclean cut t harmed
    have hpad := Nat.le_trans hlocal
      (Nat.le_add_right _
        (bankTrialProbabilityC5WorkerDenominator q *
          bankTrialSuccessCutWonAt n
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) t))
    have hfactor :
        (if BankTrialProbabilityArmedGate
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) then 2 else 1) = (2 : Nat) :=
      if_pos harmed
    have hpenalty :=
      bankTrialSuccessCutHistoryPenaltyArmed ring root S
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)) t harmed
    rw [hfactor, hpenalty]
    exact hpad
  · have hnota :
        ¬ BankTrialProbabilityArmedGate
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) := by
      intro ha
      have hm := ha.2.symm.trans hcstart.2
      cases hm
    obtain ⟨begun, hlive⟩ := hcstart.1
    have hlocal := bankTrialSuccessCutCStartStageFactorOne
      ring root S hkernel hlarge hclean cut j t
      hcut begun hlive hcstart.2
    have hinflated := bankTrialSuccessCutHistoryRarityInflate
      (bankTrialProbabilityC5WorkerDenominator q * n ^ t)
      (bankTrialProbabilityC5WorkerDenominator q *
        Prob.scheduleSum n t (fun suffix =>
          Prob.indicator
            (bankTrialSuccessFirstGoodReturnPrefix ring root S
              (bankTrialLocalRun ring root cut
                (bankTrialLocalStart S)) [] suffix).isSome))
      (bankTrialProbabilityC5WorkerNumerator q * n ^ t)
      (bankTrialProbabilityC5WorkerDenominator q *
        bankTrialC5CStartMass ring root S
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) t none)
      hlocal
    have hdouble := bankTrialSuccessCutHistoryDoubleMul
      (bankTrialProbabilityC5WorkerNumerator q) (n ^ t)
    rw [hdouble] at hinflated
    have hpad := Nat.le_trans hinflated
      (Nat.le_add_right _
        (bankTrialProbabilityC5WorkerDenominator q *
          bankTrialSuccessCutWonAt n
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) t))
    have hfactor :
        (if BankTrialProbabilityArmedGate
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) then 2 else 1) = (1 : Nat) :=
      if_neg hnota
    have hpenalty :=
      bankTrialSuccessCutHistoryPenaltyCStart ring root S
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)) t hcstart.2
    rw [hfactor, Nat.one_mul, hpenalty]
    exact hpad
  · have hterm :
        bankTrialSuccessCutWonAt n
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) t = n ^ t := by
      unfold bankTrialSuccessCutWonAt
      rw [if_pos hwon]
    rw [hterm]
    exact Nat.le_add_left _ _


/-- Multiply a sharp one-cut estimate by the already accumulated
history weight.  Pure Nat algebra: all advice quantities are opaque. -/
theorem bankTrialSuccessCutHistoryOpaqueScale
    (D N W F X G P Q : Nat)
    (h : D * X ≤ ((F * D * G + 2 * N * X) + P) + D * Q) :
    D * (W * X) ≤
      D * (W * F * G) +
        (2 * N * (W * X) + W * P + D * (W * Q)) := by
  have hs := Nat.mul_le_mul_left W h
  simpa only [Nat.mul_add, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

/-- Weighted sharp stage at one authenticated stopped prefix. -/
theorem bankTrialSuccessCutHistoryLocalScaled
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (cut : List (Fin n)) (j t : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S cut j = some cut) :
    bankTrialProbabilityC5WorkerDenominator q *
      (2 ^ bankTrialSuccessCutHistoryArmedCount
        ring root S cut j * n ^ t) ≤
    bankTrialProbabilityC5WorkerDenominator q *
      (2 ^ bankTrialSuccessCutHistoryArmedCount
        ring root S cut j *
        (if BankTrialProbabilityArmedGate
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) then 2 else 1) *
        Prob.scheduleSum n t (fun suffix =>
          Prob.indicator
            (bankTrialSuccessFirstGoodReturnPrefix ring root S
              (bankTrialLocalRun ring root cut
                (bankTrialLocalStart S)) [] suffix).isSome)) +
    (2 * bankTrialProbabilityC5WorkerNumerator q *
        (2 ^ bankTrialSuccessCutHistoryArmedCount
          ring root S cut j * n ^ t) +
      2 ^ bankTrialSuccessCutHistoryArmedCount
        ring root S cut j *
        bankTrialSuccessCutPenaltyAt ring root S
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) t +
      bankTrialProbabilityC5WorkerDenominator q *
        (2 ^ bankTrialSuccessCutHistoryArmedCount
          ring root S cut j *
          bankTrialSuccessCutWonAt n
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) t)) := by
  exact bankTrialSuccessCutHistoryOpaqueScale
    (bankTrialProbabilityC5WorkerDenominator q)
    (bankTrialProbabilityC5WorkerNumerator q)
    (2 ^ bankTrialSuccessCutHistoryArmedCount ring root S cut j)
    (if BankTrialProbabilityArmedGate
      (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S)) then 2 else 1)
    (n ^ t)
    (Prob.scheduleSum n t (fun suffix =>
      Prob.indicator
        (bankTrialSuccessFirstGoodReturnPrefix ring root S
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) [] suffix).isSome))
    (bankTrialSuccessCutPenaltyAt ring root S
      (bankTrialLocalRun ring root cut (bankTrialLocalStart S)) t)
    (bankTrialSuccessCutWonAt n
      (bankTrialLocalRun ring root cut (bankTrialLocalStart S)) t)
    (bankTrialSuccessCutHistoryLocalStage
      ring root S hkernel hlarge hclean cut j t hcut)

/-- Nat summation of a weighted local stage bound, including its
penalty and terminal padding. This invokes no assumed leaf. -/
theorem bankTrialSuccessCutHistoryOpaqueListSum
    {A : Type} (xs : List A) (D : Nat)
    (source forward debt : A → Nat) :
    (∀ x, x ∈ xs →
      D * source x ≤ D * forward x + debt x) →
    D * (xs.map source).sum ≤
      D * (xs.map forward).sum + (xs.map debt).sum := by
  induction xs with
  | nil =>
      intro _
      simp
  | cons x xs ih =>
      intro h
      have hx := h x (by simp)
      have ht : ∀ y, y ∈ xs →
          D * source y ≤ D * forward y + debt y := by
        intro y hy
        exact h y (by simp [hy])
      have hsum := Nat.add_le_add hx (ih ht)
      simpa only [List.map_cons, List.sum_cons,
        Nat.mul_add, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using hsum

/-- The weighted mass written in the authenticated stop-prefix
coordinates of the ONE original length-T schedule. -/
noncomputable def bankTrialSuccessCutHistoryPrefixMass
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j T : Nat) : Nat :=
  ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
    (bankTrialSuccessGoodReturnCutBool ring root S j)
    T [] (bankTrialLocalStart S)).map (fun cut =>
      2 ^ bankTrialSuccessCutHistoryArmedCount
        ring root S cut j * n ^ (T - cut.length))).sum

/-- The sharp weighted forward numerator in stopped-prefix
coordinates; ARMED contributes 2, CSTART contributes 1. -/
noncomputable def bankTrialSuccessCutHistoryPrefixForward
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j T : Nat) : Nat :=
  ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
    (bankTrialSuccessGoodReturnCutBool ring root S j)
    T [] (bankTrialLocalStart S)).map (fun cut =>
      2 ^ bankTrialSuccessCutHistoryArmedCount
        ring root S cut j *
      (if BankTrialProbabilityArmedGate
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)) then 2 else 1) *
      Prob.scheduleSum n (T - cut.length) (fun suffix =>
        Prob.indicator
          (bankTrialSuccessFirstGoodReturnPrefix ring root S
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) [] suffix).isSome))).sum

/-- Rarity, pending, and WON debt with the PRE-CUT history weight. -/
noncomputable def bankTrialSuccessCutHistoryPrefixDebt
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j T : Nat) : Nat :=
  ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
    (bankTrialSuccessGoodReturnCutBool ring root S j)
    T [] (bankTrialLocalStart S)).map (fun cut =>
      2 * bankTrialProbabilityC5WorkerNumerator q *
        (2 ^ bankTrialSuccessCutHistoryArmedCount
          ring root S cut j * n ^ (T - cut.length)) +
      2 ^ bankTrialSuccessCutHistoryArmedCount
        ring root S cut j *
        bankTrialSuccessCutPenaltyAt ring root S
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) (T - cut.length) +
      bankTrialProbabilityC5WorkerDenominator q *
        (2 ^ bankTrialSuccessCutHistoryArmedCount
          ring root S cut j *
          bankTrialSuccessCutWonAt n
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) (T - cut.length)))).sum

/-- An unconditional, kernel-based sharp weighted-prefix inequality.
The transfer of its two stop-prefix masses to the requested W_j,
W_(j+1) is a separate, not-yet-established Nat-valued factorization. -/
theorem bankTrialSuccessCutHistoryPrefixStepOfKernel
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (j T : Nat) :
    bankTrialProbabilityC5WorkerDenominator q *
      bankTrialSuccessCutHistoryPrefixMass ring root S j T ≤
    bankTrialProbabilityC5WorkerDenominator q *
      bankTrialSuccessCutHistoryPrefixForward ring root S j T +
    bankTrialSuccessCutHistoryPrefixDebt ring root S j T := by
  have hcuts (cut : List (Fin n))
      (hmem : cut ∈
        Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
          (bankTrialSuccessGoodReturnCutBool ring root S j)
          T [] (bankTrialLocalStart S)) :
      bankTrialProbabilityC5WorkerDenominator q *
        (2 ^ bankTrialSuccessCutHistoryArmedCount
          ring root S cut j * n ^ (T - cut.length)) ≤
      bankTrialProbabilityC5WorkerDenominator q *
        (2 ^ bankTrialSuccessCutHistoryArmedCount
          ring root S cut j *
          (if BankTrialProbabilityArmedGate
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) then 2 else 1) *
          Prob.scheduleSum n (T - cut.length) (fun suffix =>
            Prob.indicator
              (bankTrialSuccessFirstGoodReturnPrefix ring root S
                (bankTrialLocalRun ring root cut
                  (bankTrialLocalStart S)) [] suffix).isSome)) +
      (2 * bankTrialProbabilityC5WorkerNumerator q *
          (2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S cut j * n ^ (T - cut.length)) +
        2 ^ bankTrialSuccessCutHistoryArmedCount
          ring root S cut j *
          bankTrialSuccessCutPenaltyAt ring root S
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) (T - cut.length) +
        bankTrialProbabilityC5WorkerDenominator q *
          (2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S cut j *
            bankTrialSuccessCutWonAt n
              (bankTrialLocalRun ring root cut
                (bankTrialLocalStart S)) (T - cut.length))) := by
    exact bankTrialSuccessCutHistoryLocalScaled
      ring root S hkernel hlarge hclean cut j
      (T - cut.length)
      (bankTrialSuccessStoppedGoodCutAuthenticated
        ring root S j T cut hmem)
  have hlist := bankTrialSuccessCutHistoryOpaqueListSum
    (Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
      (bankTrialSuccessGoodReturnCutBool ring root S j)
      T [] (bankTrialLocalStart S))
    (bankTrialProbabilityC5WorkerDenominator q)
    (fun cut =>
      2 ^ bankTrialSuccessCutHistoryArmedCount
        ring root S cut j * n ^ (T - cut.length))
    (fun cut =>
      2 ^ bankTrialSuccessCutHistoryArmedCount
        ring root S cut j *
      (if BankTrialProbabilityArmedGate
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)) then 2 else 1) *
      Prob.scheduleSum n (T - cut.length) (fun suffix =>
        Prob.indicator
          (bankTrialSuccessFirstGoodReturnPrefix ring root S
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) [] suffix).isSome))
    (fun cut =>
      2 * bankTrialProbabilityC5WorkerNumerator q *
        (2 ^ bankTrialSuccessCutHistoryArmedCount
          ring root S cut j * n ^ (T - cut.length)) +
      2 ^ bankTrialSuccessCutHistoryArmedCount
        ring root S cut j *
        bankTrialSuccessCutPenaltyAt ring root S
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) (T - cut.length) +
      bankTrialProbabilityC5WorkerDenominator q *
        (2 ^ bankTrialSuccessCutHistoryArmedCount
          ring root S cut j *
          bankTrialSuccessCutWonAt n
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) (T - cut.length)))
    hcuts
  simpa only [bankTrialSuccessCutHistoryPrefixMass,
    bankTrialSuccessCutHistoryPrefixForward,
    bankTrialSuccessCutHistoryPrefixDebt] using hlist


/-! A reusable NAT-valued stopped-prefix factorization.  Unlike
Prob.stoppedPrefixFactorization's Boolean observer, this records an
arbitrary prefix-dependent weight in Nat without replicating a
scheduler tape or assuming a terminal leaf. -/

/-- First-stop Nat observer: the observed value is taken at the first
stop on the original word, and zero if no stop is reached. -/
def bankTrialSuccessNatStoppedWord {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (A : List (Fin n) → X → Nat → List (Fin n) → Nat) :
    Nat → List (Fin n) → X → List (Fin n) → Nat
  | t, pre, x, [] =>
      if stop pre x then A pre x t [] else 0
  | t, pre, x, e :: w =>
      if stop pre x then A pre x t (e :: w)
      else bankTrialSuccessNatStoppedWord next stop A
        (t - 1) (pre ++ [e]) (next x e) w

/-- Prefix-dependent first-stop Nat mass, as an original scheduler
first-letter recursion. -/
def bankTrialSuccessNatStoppedSum {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (weight : List (Fin n) → X → Nat → Nat) :
    Nat → List (Fin n) → X → Nat
  | 0, pre, x =>
      if stop pre x then weight pre x 0 else 0
  | t + 1, pre, x =>
      if stop pre x then weight pre x (t + 1)
      else (List.ofFn (fun e : Fin n =>
        bankTrialSuccessNatStoppedSum next stop weight t
          (pre ++ [e]) (next x e))).sum

/-- The exact word-to-first-stop recursion for Nat observers. -/
theorem bankTrialSuccessNatStoppedSumFactor
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (A : List (Fin n) → X → Nat → List (Fin n) → Nat) :
    ∀ t pre x,
      Prob.scheduleSum n t (fun w =>
        bankTrialSuccessNatStoppedWord next stop A t pre x w) =
      bankTrialSuccessNatStoppedSum next stop
        (fun pre y k => Prob.scheduleSum n k (fun v => A pre y k v))
        t pre x := by
  intro t
  induction t with
  | zero =>
      intro pre x
      cases hs : stop pre x with
      | false =>
          simp [bankTrialProbabilityScheduleSumZero,
            bankTrialSuccessNatStoppedWord,
            bankTrialSuccessNatStoppedSum, hs]
      | true =>
          simp [bankTrialProbabilityScheduleSumZero,
            bankTrialSuccessNatStoppedWord,
            bankTrialSuccessNatStoppedSum, hs]
  | succ t ih =>
      intro pre x
      cases hs : stop pre x with
      | true =>
          have heq :
              (fun w : List (Fin n) =>
                bankTrialSuccessNatStoppedWord next stop A
                  (t + 1) pre x w) =
              (fun w : List (Fin n) => A pre x (t + 1) w) := by
            funext w
            cases w with
            | nil => simp [bankTrialSuccessNatStoppedWord, hs]
            | cons e tail =>
                simp [bankTrialSuccessNatStoppedWord, hs]
          rw [heq]
          simp [bankTrialSuccessNatStoppedSum, hs]
      | false =>
          rw [bankTrialProbabilityScheduleSumFirst]
          simp only [bankTrialSuccessNatStoppedSum,
            hs, Bool.false_eq_true, if_false]
          apply ofFn_sum_eq
          intro e
          have heq :
              (fun w : List (Fin n) =>
                bankTrialSuccessNatStoppedWord next stop A
                  (t + 1) pre x (e :: w)) =
              (fun w : List (Fin n) =>
                bankTrialSuccessNatStoppedWord next stop A
                  t (pre ++ [e]) (next x e) w) := by
            funext w
            simp [bankTrialSuccessNatStoppedWord, hs]
          rw [heq]
          exact ih (pre ++ [e]) (next x e)

/-- Combinatorial finite flatMap summation; no Finset. -/
theorem bankTrialSuccessNatStoppedFlatMap
    {U V : Type}
    (xs : List U) (ys : U → List V) (f : V → Nat) :
    ((xs.flatMap ys).map f).sum =
      (xs.map (fun x => ((ys x).map f).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- The length correction for one consumed scheduler letter. -/
theorem bankTrialSuccessNatStoppedSuccSub
    (t k : Nat) : (t + 1) - (k + 1) = t - k := by
  omega

/-- Flatten the Nat-weighted first-stop sum over every first letter,
including the accumulated consumed prefix pre. -/
theorem bankTrialSuccessNatStoppedStepSum
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (weight : List (Fin n) → X → Nat → Nat)
    (pre : List (Fin n)) (x : X) (t : Nat)
    (prefixes : Fin n → List (List (Fin n))) :
    (List.ofFn (fun e : Fin n =>
      ((prefixes e).map (fun u =>
        weight ((pre ++ [e]) ++ u)
          (Prob.stoppedTapeRun next u (next x e))
          (t - u.length))).sum)).sum =
    (((List.ofFn (fun e : Fin n => e)).flatMap (fun e =>
      (prefixes e).map (List.cons e))).map (fun u =>
        weight (pre ++ u)
          (Prob.stoppedTapeRun next u x)
          ((t + 1) - u.length))).sum := by
  rw [bankTrialSuccessNatStoppedFlatMap]
  simp only [List.map_ofFn]
  apply ofFn_sum_eq
  intro e
  simp only [List.map_map, Function.comp_def,
    List.length_cons, Nat.succ_eq_add_one,
    bankTrialSuccessNatStoppedSuccSub,
    List.append_assoc, List.singleton_append]
  rfl

/-- Exact conversion from Nat stopped sum to authenticated first-stop
prefixes, each charged in its true remaining scheduler horizon. -/
theorem bankTrialSuccessNatStoppedSumIsList
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (weight : List (Fin n) → X → Nat → Nat) :
    ∀ t pre x,
      bankTrialSuccessNatStoppedSum next stop weight t pre x =
      ((Prob.firstStoppedPrefixes next stop t pre x).map (fun u =>
        weight (pre ++ u)
          (Prob.stoppedTapeRun next u x)
          (t - u.length))).sum := by
  intro t
  induction t with
  | zero =>
      intro pre x
      cases hs : stop pre x with
      | false =>
          simp [bankTrialSuccessNatStoppedSum,
            Prob.firstStoppedPrefixes, hs]
      | true =>
          simp [bankTrialSuccessNatStoppedSum,
            Prob.firstStoppedPrefixes, Prob.stoppedTapeRun, hs]
  | succ t ih =>
      intro pre x
      cases hs : stop pre x with
      | true =>
          simp [bankTrialSuccessNatStoppedSum,
            Prob.firstStoppedPrefixes, Prob.stoppedTapeRun, hs]
      | false =>
          calc
            bankTrialSuccessNatStoppedSum next stop weight
                (t + 1) pre x =
              (List.ofFn (fun e : Fin n =>
                bankTrialSuccessNatStoppedSum next stop weight t
                  (pre ++ [e]) (next x e))).sum := by
                    simp [bankTrialSuccessNatStoppedSum, hs]
            _ = (List.ofFn (fun e : Fin n =>
                  ((Prob.firstStoppedPrefixes next stop t
                    (pre ++ [e]) (next x e)).map (fun u =>
                      weight ((pre ++ [e]) ++ u)
                        (Prob.stoppedTapeRun next u (next x e))
                        (t - u.length))).sum)).sum := by
                    apply ofFn_sum_eq
                    intro e
                    exact ih (pre ++ [e]) (next x e)
            _ = (((List.ofFn (fun e : Fin n => e)).flatMap
                  (fun e =>
                    (Prob.firstStoppedPrefixes next stop t
                      (pre ++ [e]) (next x e)).map (List.cons e))).map
                  (fun u =>
                    weight (pre ++ u)
                      (Prob.stoppedTapeRun next u x)
                      ((t + 1) - u.length))).sum :=
              bankTrialSuccessNatStoppedStepSum next weight pre x t
                (fun e => Prob.firstStoppedPrefixes next stop t
                  (pre ++ [e]) (next x e))
            _ = ((Prob.firstStoppedPrefixes next stop
                  (t + 1) pre x).map (fun u =>
                    weight (pre ++ u)
                      (Prob.stoppedTapeRun next u x)
                      ((t + 1) - u.length))).sum := by
                      simp [Prob.firstStoppedPrefixes, hs]

/-- Nat-valued stopped-tree factorization, including arbitrary
prefix-dependent weights. It is a FINITE combinatorial equality. -/
theorem bankTrialSuccessNatStoppedFactorization
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (A : List (Fin n) → X → Nat → List (Fin n) → Nat)
    (x : X) (T : Nat) :
    Prob.scheduleSum n T (fun w =>
      bankTrialSuccessNatStoppedWord next stop A T [] x w) =
    ((Prob.firstStoppedPrefixes next stop T [] x).map (fun u =>
      Prob.scheduleSum n (T - u.length) (fun suffix =>
        A u (Prob.stoppedTapeRun next u x)
          (T - u.length) suffix))).sum := by
  calc
    Prob.scheduleSum n T (fun w =>
        bankTrialSuccessNatStoppedWord next stop A T [] x w) =
      bankTrialSuccessNatStoppedSum next stop
        (fun pre y k => Prob.scheduleSum n k
          (fun v => A pre y k v)) T [] x :=
      bankTrialSuccessNatStoppedSumFactor next stop A T [] x
    _ = _ := by
      simpa only [List.nil_append] using
        (bankTrialSuccessNatStoppedSumIsList next stop
          (fun pre y k => Prob.scheduleSum n k
            (fun v => A pre y k v)) T [] x)


/-! Concrete Nat observer identification for the ACTUAL GOOD-return
scanner.  These lemmas are Nat analogues of the installed Boolean
StaticStoppedAtCut/StaticStoppedNone, but retain the consumed prefix
inside the observation. -/

/-- At the first authenticated cut, a prefix-aware Nat observer is
evaluated on the actual remainder of the SAME scheduler word. -/
theorem bankTrialSuccessCutHistoryNatAtCut
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (A : List (Fin n) → BankTrialLocalState q →
      List (Fin n) → Nat)
    (j : Nat) :
    ∀ (used suffix pre : List (Fin n))
      (z : BankTrialLocalState q) (T : Nat),
      z = bankTrialLocalRun ring root pre
        (bankTrialLocalStart S) →
      bankTrialSuccessGoodReturnCutPrefix ring root S
        (pre ++ used) j = some (pre ++ used) →
      bankTrialSuccessNatStoppedWord
          (bankTrialLocalNext ring root)
          (bankTrialSuccessGoodReturnCutBool ring root S j)
          (fun pre x _ remaining => A pre x remaining)
          T pre z (used ++ suffix) =
        A (pre ++ used)
          (bankTrialLocalRun ring root (pre ++ used)
            (bankTrialLocalStart S)) suffix := by
  intro used
  induction used with
  | nil =>
      intro suffix pre z T hz hcut
      have hbase :
          bankTrialSuccessGoodReturnCutPrefix ring root S
            pre j = some pre := by
        simpa only [List.append_nil] using hcut
      have hstop :
          bankTrialSuccessGoodReturnCutBool ring root S j
            pre z = true := by
        simp [bankTrialSuccessGoodReturnCutBool, hbase]
      have hread :
          bankTrialSuccessNatStoppedWord
              (bankTrialLocalNext ring root)
              (bankTrialSuccessGoodReturnCutBool ring root S j)
              (fun pre x _ remaining => A pre x remaining)
              T pre z suffix = A pre z suffix := by
        cases suffix with
        | nil =>
            simp [bankTrialSuccessNatStoppedWord, hstop]
        | cons e tail =>
            simp [bankTrialSuccessNatStoppedWord, hstop]
      simpa only [List.nil_append, List.append_nil, hz] using hread
  | cons e tail ih =>
      intro suffix pre z T hz hcut
      have hbig :
          bankTrialSuccessGoodReturnCutBool ring root S j
            (pre ++ (e :: tail))
            (Prob.stoppedTapeRun (bankTrialLocalNext ring root)
              (pre ++ (e :: tail)) (bankTrialLocalStart S)) =
            true := by
        simp [bankTrialSuccessGoodReturnCutBool, hcut]
      have hstopFalse :
          bankTrialSuccessGoodReturnCutBool ring root S j
            pre z = false := by
        cases hs :
            bankTrialSuccessGoodReturnCutBool ring root S j
              pre z with
        | false => rfl
        | true =>
            have hsmall :
                bankTrialSuccessGoodReturnCutBool ring root S j
                  pre
                  (Prob.stoppedTapeRun
                    (bankTrialLocalNext ring root)
                    pre (bankTrialLocalStart S)) = true := by
              simpa only [bankTrialSuccessGoodReturnCutBool]
                using hs
            have hnil :=
              bankTrialSuccessGoodReturnCutPrefixFree
                ring root S j pre (e :: tail) hsmall hbig
            cases hnil
      have hznext :
          bankTrialLocalNext ring root z e =
            bankTrialLocalRun ring root (pre ++ [e])
              (bankTrialLocalStart S) := by
        rw [bankTrialLocalRunAppend, ← hz]
        rfl
      have hnextCut :
          bankTrialSuccessGoodReturnCutPrefix ring root S
            ((pre ++ [e]) ++ tail) j =
              some ((pre ++ [e]) ++ tail) := by
        simpa only [List.append_assoc, List.singleton_append]
          using hcut
      have htail :=
        ih suffix (pre ++ [e])
          (bankTrialLocalNext ring root z e) (T - 1)
          hznext hnextCut
      simpa [bankTrialSuccessNatStoppedWord, hstopFalse,
        List.cons_append, List.append_assoc,
        List.singleton_append] using htail

/-- Full-word version of the Nat stopped observer at the j-th cut. -/
theorem bankTrialSuccessCutHistoryNatOfGoodCut
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (A : List (Fin n) → BankTrialLocalState q →
      List (Fin n) → Nat)
    (word cut : List (Fin n)) (j T : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix ring root S
      word j = some cut) :
    bankTrialSuccessNatStoppedWord (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        (fun pre x _ suffix => A pre x suffix)
        T [] (bankTrialLocalStart S) word =
      A cut (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S)) (word.drop cut.length) := by
  obtain ⟨suffix, hword⟩ :=
    bankTrialSuccessGoodReturnCutIsPrefix
      ring root S word j cut hcut
  have hself :=
    bankTrialSuccessGoodReturnCutSelf
      ring root S word j cut hcut
  have hbase :
      bankTrialSuccessGoodReturnCutPrefix ring root S
        ([] ++ cut) j = some ([] ++ cut) := by
    simpa only [List.nil_append] using hself
  have hstop :=
    bankTrialSuccessCutHistoryNatAtCut
      ring root S A j cut suffix [] (bankTrialLocalStart S)
      T rfl hbase
  rw [hword, bankTrialSuccessDropPrefixAppend]
  simpa only [List.nil_append] using hstop

/-- When the j-th cut is absent, no Nat first-stop observer fires. -/
theorem bankTrialSuccessCutHistoryNatNone
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (A : List (Fin n) → BankTrialLocalState q →
      List (Fin n) → Nat)
    (j : Nat) :
    ∀ (word pre : List (Fin n))
      (z : BankTrialLocalState q) (T : Nat),
      z = bankTrialLocalRun ring root pre
        (bankTrialLocalStart S) →
      bankTrialSuccessGoodReturnCutPrefix ring root S
        (pre ++ word) j = none →
      bankTrialSuccessNatStoppedWord (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        (fun pre x _ suffix => A pre x suffix)
        T pre z word = 0 := by
  intro word
  induction word with
  | nil =>
      intro pre z T hz hnone
      have hstopFalse :
          bankTrialSuccessGoodReturnCutBool ring root S j
            pre z = false := by
        cases hs : bankTrialSuccessGoodReturnCutBool
            ring root S j pre z with
        | false => rfl
        | true =>
            have hc :
                bankTrialSuccessGoodReturnCutPrefix ring root S
                  pre j = some pre :=
              of_decide_eq_true
                (show decide
                  (bankTrialSuccessGoodReturnCutPrefix ring root S
                    pre j = some pre) = true from hs)
            have hn :
                bankTrialSuccessGoodReturnCutPrefix ring root S
                  pre j = none := by
              simpa only [List.append_nil] using hnone
            rw [hc] at hn
            cases hn
      simp [bankTrialSuccessNatStoppedWord, hstopFalse]
  | cons e tail ih =>
      intro pre z T hz hnone
      have hstopFalse :
          bankTrialSuccessGoodReturnCutBool ring root S j
            pre z = false := by
        cases hs : bankTrialSuccessGoodReturnCutBool
            ring root S j pre z with
        | false => rfl
        | true =>
            have hc :
                bankTrialSuccessGoodReturnCutPrefix ring root S
                  pre j = some pre :=
              of_decide_eq_true
                (show decide
                  (bankTrialSuccessGoodReturnCutPrefix ring root S
                    pre j = some pre) = true from hs)
            have hfull :=
              bankTrialSuccessGoodReturnCutAppend
                ring root S j pre pre (e :: tail) hc
            rw [hfull] at hnone
            cases hnone
      have hznext :
          bankTrialLocalNext ring root z e =
            bankTrialLocalRun ring root (pre ++ [e])
              (bankTrialLocalStart S) := by
        rw [bankTrialLocalRunAppend, ← hz]
        rfl
      have hnextNone :
          bankTrialSuccessGoodReturnCutPrefix ring root S
            ((pre ++ [e]) ++ tail) j = none := by
        simpa only [List.append_assoc, List.singleton_append]
          using hnone
      have htail := ih (pre ++ [e])
        (bankTrialLocalNext ring root z e)
        (T - 1) hznext hnextNone
      simpa [bankTrialSuccessNatStoppedWord, hstopFalse]
        using htail

/-- Pointwise identification of the original W_j integrand with
the first-stop Nat scanner at cut j. -/
theorem bankTrialSuccessCutHistoryCurrentWordExact
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j T : Nat) (word : List (Fin n)) :
    bankTrialSuccessNatStoppedWord (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        (fun pre _ _ _ =>
          2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S pre j)
        T [] (bankTrialLocalStart S) word =
      Prob.indicator
        (bankTrialSuccessGoodReturnCutPrefix
          ring root S word j).isSome *
      2 ^ bankTrialSuccessCutHistoryArmedCount
        ring root S word j := by
  cases hcut :
      bankTrialSuccessGoodReturnCutPrefix
        ring root S word j with
  | none =>
      have hn := bankTrialSuccessCutHistoryNatNone
        ring root S (fun pre _ _ =>
          2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S pre j)
        j word [] (bankTrialLocalStart S) T rfl
        (by simpa only [List.nil_append] using hcut)
      simpa [Prob.indicator, hcut] using hn
  | some cut =>
      have hs := bankTrialSuccessCutHistoryNatOfGoodCut
        ring root S (fun pre _ _ =>
          2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S pre j)
        word cut j T hcut
      have hcount := bankTrialSuccessCutHistoryCountAtCut
        ring root S word cut j hcut
      simpa [Prob.indicator, hcut, hcount] using hs

/-- Generic finite-list sum extensionality, used for the two
exact factorization identities. -/
theorem bankTrialSuccessCutHistoryMapSumExt
    {A : Type} (xs : List A) (f g : A → Nat)
    (h : ∀ x, f x = g x) :
    (xs.map f).sum = (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [h x, ih]

/-- First requested identification: W_j is exactly the weighted
sum of authenticated j-th stopped prefixes on the ORIGINAL tape. -/
theorem bankTrialSuccessCutHistoryWeightedMassFactorization
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j T : Nat) :
    bankTrialSuccessCutHistoryWeightedMass ring root S j T =
      bankTrialSuccessCutHistoryPrefixMass ring root S j T := by
  have heq :
      (fun word : List (Fin n) =>
        Prob.indicator
          (bankTrialSuccessGoodReturnCutPrefix
            ring root S word j).isSome *
        2 ^ bankTrialSuccessCutHistoryArmedCount
          ring root S word j) =
      (fun word : List (Fin n) =>
        bankTrialSuccessNatStoppedWord (bankTrialLocalNext ring root)
          (bankTrialSuccessGoodReturnCutBool ring root S j)
          (fun pre _ _ _ =>
            2 ^ bankTrialSuccessCutHistoryArmedCount
              ring root S pre j)
          T [] (bankTrialLocalStart S) word) := by
    funext word
    exact (bankTrialSuccessCutHistoryCurrentWordExact
      ring root S j T word).symm
  unfold bankTrialSuccessCutHistoryWeightedMass
  rw [heq]
  calc
    Prob.scheduleSum n T (fun word =>
        bankTrialSuccessNatStoppedWord
          (bankTrialLocalNext ring root)
          (bankTrialSuccessGoodReturnCutBool ring root S j)
          (fun pre _ _ _ =>
            2 ^ bankTrialSuccessCutHistoryArmedCount
              ring root S pre j)
          T [] (bankTrialLocalStart S) word) =
      ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        T [] (bankTrialLocalStart S)).map (fun cut =>
        Prob.scheduleSum n (T - cut.length) (fun _ =>
          2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S cut j))).sum :=
      bankTrialSuccessNatStoppedFactorization
        (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        (fun pre _ _ _ =>
          2 ^ bankTrialSuccessCutHistoryArmedCount ring root S pre j)
        (bankTrialLocalStart S) T
    _ = bankTrialSuccessCutHistoryPrefixMass
        ring root S j T := by
      unfold bankTrialSuccessCutHistoryPrefixMass
      exact bankTrialSuccessCutHistoryMapSumExt
        (Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
          (bankTrialSuccessGoodReturnCutBool ring root S j)
          T [] (bankTrialLocalStart S))
        (fun cut =>
          Prob.scheduleSum n (T - cut.length) (fun _ =>
            2 ^ bankTrialSuccessCutHistoryArmedCount
              ring root S cut j))
        (fun cut =>
          2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S cut j * n ^ (T - cut.length))
        (fun cut => by
          calc
            Prob.scheduleSum n (T - cut.length) (fun _ =>
                2 ^ bankTrialSuccessCutHistoryArmedCount
                  ring root S cut j) =
              n ^ (T - cut.length) *
                2 ^ bankTrialSuccessCutHistoryArmedCount
                  ring root S cut j :=
              bankTrialProbabilityScheduleSumConst n
                (T - cut.length) _
            _ = _ := Nat.mul_comm _ _)


/-- Pointwise factor update at the NEXT good return, including
the exact original scheduler suffix. The two outcomes of the first
post-cut scanner exhaust the actual next GOOD cut. -/
theorem bankTrialSuccessCutHistoryNextWordExact
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j T : Nat) (word : List (Fin n)) :
    bankTrialSuccessNatStoppedWord (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        (fun pre x _ suffix =>
          2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S pre j *
          (if BankTrialProbabilityArmedGate x then 2 else 1) *
          Prob.indicator
            (bankTrialSuccessFirstGoodReturnPrefix ring root S
              x [] suffix).isSome)
        T [] (bankTrialLocalStart S) word =
      Prob.indicator
        (bankTrialSuccessGoodReturnCutPrefix
          ring root S word (j + 1)).isSome *
      2 ^ bankTrialSuccessCutHistoryArmedCount
        ring root S word (j + 1) := by
  cases hcut :
      bankTrialSuccessGoodReturnCutPrefix
        ring root S word j with
  | none =>
      have hn := bankTrialSuccessCutHistoryNatNone
        ring root S (fun pre x suffix =>
          2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S pre j *
          (if BankTrialProbabilityArmedGate x then 2 else 1) *
          Prob.indicator
            (bankTrialSuccessFirstGoodReturnPrefix
              ring root S x [] suffix).isSome)
        j word [] (bankTrialLocalStart S) T rfl
        (by simpa only [List.nil_append] using hcut)
      have hnext := bankTrialSuccessGoodReturnCutNoneSuccessor
        ring root S word j hcut
      simpa [Prob.indicator, hnext] using hn
  | some cut =>
      have hs := bankTrialSuccessCutHistoryNatOfGoodCut
        ring root S (fun pre x suffix =>
          2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S pre j *
          (if BankTrialProbabilityArmedGate x then 2 else 1) *
          Prob.indicator
            (bankTrialSuccessFirstGoodReturnPrefix
              ring root S x [] suffix).isSome)
        word cut j T hcut
      cases hscan :
          bankTrialSuccessFirstGoodReturnPrefix ring root S
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S))
            [] (word.drop cut.length) with
      | none =>
          have hnext :
              bankTrialSuccessGoodReturnCutPrefix
                ring root S word (j + 1) = none := by
            simp only [bankTrialSuccessGoodReturnCutPrefix,
              hcut, hscan]
          simpa [Prob.indicator, hscan, hnext] using hs
      | some segment =>
          have hnext :
              bankTrialSuccessGoodReturnCutPrefix
                ring root S word (j + 1) =
                  some (cut ++ segment) := by
            simp only [bankTrialSuccessGoodReturnCutPrefix,
              hcut, hscan]
          have hfactor := bankTrialSuccessCutHistoryPowerSucc
            ring root S word cut j hcut
          simpa [Prob.indicator, hscan, hnext, hfactor] using hs

/-- The generic Nat first-stop factorization specialized to the
existing BANK local run. The only conversion is the already proved
stoppedTapeRun/localRun equality, applied pointwise under map. -/
theorem bankTrialSuccessNatStoppedFactorizationLocal
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (stop : List (Fin n) → BankTrialLocalState q → Bool)
    (A : List (Fin n) → BankTrialLocalState q →
      Nat → List (Fin n) → Nat)
    (x : BankTrialLocalState q) (T : Nat) :
    Prob.scheduleSum n T (fun word =>
      bankTrialSuccessNatStoppedWord
        (bankTrialLocalNext ring root) stop A T [] x word) =
    ((Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root) stop T [] x).map (fun cut =>
      Prob.scheduleSum n (T - cut.length) (fun suffix =>
        A cut (bankTrialLocalRun ring root cut x)
          (T - cut.length) suffix))).sum := by
  calc
    Prob.scheduleSum n T (fun word =>
        bankTrialSuccessNatStoppedWord
          (bankTrialLocalNext ring root) stop A
          T [] x word) =
      ((Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root) stop T [] x).map (fun cut =>
        Prob.scheduleSum n (T - cut.length) (fun suffix =>
          A cut
            (Prob.stoppedTapeRun
              (bankTrialLocalNext ring root) cut x)
            (T - cut.length) suffix))).sum :=
      bankTrialSuccessNatStoppedFactorization
        (bankTrialLocalNext ring root) stop A x T
    _ = _ := by
      exact bankTrialSuccessCutHistoryMapSumExt
        (Prob.firstStoppedPrefixes
          (bankTrialLocalNext ring root) stop T [] x)
        (fun cut =>
          Prob.scheduleSum n (T - cut.length) (fun suffix =>
            A cut
              (Prob.stoppedTapeRun
                (bankTrialLocalNext ring root) cut x)
              (T - cut.length) suffix))
        (fun cut =>
          Prob.scheduleSum n (T - cut.length) (fun suffix =>
            A cut (bankTrialLocalRun ring root cut x)
              (T - cut.length) suffix))
        (fun cut => by
          rw [bankTrialSuccessStoppedRunEqLocal ring root cut x])


/-- The SECOND required identification: after a good return,
the next full-word path weight includes one new factor two only
when the preceding cut was ARMED. -/
theorem bankTrialSuccessCutHistoryWeightedNextFactorization
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j T : Nat) :
    bankTrialSuccessCutHistoryWeightedMass ring root S (j + 1) T =
      bankTrialSuccessCutHistoryPrefixForward
        ring root S j T := by
  have heq :
      (fun word : List (Fin n) =>
        Prob.indicator
          (bankTrialSuccessGoodReturnCutPrefix
            ring root S word (j + 1)).isSome *
        2 ^ bankTrialSuccessCutHistoryArmedCount
          ring root S word (j + 1)) =
      (fun word : List (Fin n) =>
        bankTrialSuccessNatStoppedWord (bankTrialLocalNext ring root)
          (bankTrialSuccessGoodReturnCutBool ring root S j)
          (fun pre x _ suffix =>
            2 ^ bankTrialSuccessCutHistoryArmedCount
              ring root S pre j *
            (if BankTrialProbabilityArmedGate x then 2 else 1) *
            Prob.indicator
              (bankTrialSuccessFirstGoodReturnPrefix
                ring root S x [] suffix).isSome)
          T [] (bankTrialLocalStart S) word) := by
    funext word
    exact (bankTrialSuccessCutHistoryNextWordExact
      ring root S j T word).symm
  unfold bankTrialSuccessCutHistoryWeightedMass
  rw [heq]
  calc
    Prob.scheduleSum n T (fun word =>
        bankTrialSuccessNatStoppedWord
          (bankTrialLocalNext ring root)
          (bankTrialSuccessGoodReturnCutBool ring root S j)
          (fun pre x _ suffix =>
            2 ^ bankTrialSuccessCutHistoryArmedCount
              ring root S pre j *
            (if BankTrialProbabilityArmedGate x then 2 else 1) *
            Prob.indicator
              (bankTrialSuccessFirstGoodReturnPrefix
                ring root S x [] suffix).isSome)
          T [] (bankTrialLocalStart S) word) =
      ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        T [] (bankTrialLocalStart S)).map (fun cut =>
        Prob.scheduleSum n (T - cut.length) (fun suffix =>
          2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S cut j *
          (if BankTrialProbabilityArmedGate
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) then 2 else 1) *
          Prob.indicator
            (bankTrialSuccessFirstGoodReturnPrefix
              ring root S
              (bankTrialLocalRun ring root cut
                (bankTrialLocalStart S))
              [] suffix).isSome))).sum :=
      bankTrialSuccessNatStoppedFactorizationLocal
        ring root
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        (fun pre x _ suffix =>
          2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S pre j *
          (if BankTrialProbabilityArmedGate x then 2 else 1) *
          Prob.indicator
            (bankTrialSuccessFirstGoodReturnPrefix
              ring root S x [] suffix).isSome)
        (bankTrialLocalStart S) T
    _ = bankTrialSuccessCutHistoryPrefixForward
        ring root S j T := by
      unfold bankTrialSuccessCutHistoryPrefixForward
      exact bankTrialSuccessCutHistoryMapSumExt
        (Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
          (bankTrialSuccessGoodReturnCutBool ring root S j)
          T [] (bankTrialLocalStart S))
        (fun cut =>
          Prob.scheduleSum n (T - cut.length) (fun suffix =>
            2 ^ bankTrialSuccessCutHistoryArmedCount
              ring root S cut j *
            (if BankTrialProbabilityArmedGate
              (bankTrialLocalRun ring root cut
                (bankTrialLocalStart S)) then 2 else 1) *
            Prob.indicator
              (bankTrialSuccessFirstGoodReturnPrefix ring root S
                (bankTrialLocalRun ring root cut
                  (bankTrialLocalStart S)) [] suffix).isSome))
        (fun cut =>
          2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S cut j *
          (if BankTrialProbabilityArmedGate
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) then 2 else 1) *
          Prob.scheduleSum n (T - cut.length) (fun suffix =>
            Prob.indicator
              (bankTrialSuccessFirstGoodReturnPrefix ring root S
                (bankTrialLocalRun ring root cut
                  (bankTrialLocalStart S)) [] suffix).isSome))
        (fun cut => by
          simpa only [Nat.mul_assoc] using
            (bankTrialSuccessScheduleSumScale n (T - cut.length)
              (2 ^ bankTrialSuccessCutHistoryArmedCount
                ring root S cut j *
              (if BankTrialProbabilityArmedGate
                (bankTrialLocalRun ring root cut
                  (bankTrialLocalStart S)) then 2 else 1))
              (fun suffix =>
                Prob.indicator
                  (bankTrialSuccessFirstGoodReturnPrefix ring root S
                    (bankTrialLocalRun ring root cut
                      (bankTrialLocalStart S)) [] suffix).isSome)))

/-- Requested (2), with an explicit actual-path weighted debt.
The coefficient on the following word's mass is EXACTLY ONE. -/
theorem bankTrialSuccessCutHistoryWeightedStepOfKernel
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (j T : Nat) :
    bankTrialProbabilityC5WorkerDenominator q *
      bankTrialSuccessCutHistoryWeightedMass ring root S j T ≤
    bankTrialProbabilityC5WorkerDenominator q *
      bankTrialSuccessCutHistoryWeightedMass ring root S
        (j + 1) T +
    bankTrialSuccessCutHistoryPrefixDebt ring root S j T := by
  have hstep := bankTrialSuccessCutHistoryPrefixStepOfKernel
    ring root S hkernel hlarge hclean j T
  rw [← bankTrialSuccessCutHistoryWeightedMassFactorization
    ring root S j T,
    ← bankTrialSuccessCutHistoryWeightedNextFactorization
      ring root S j T] at hstep
  exact hstep

/-- Pure Nat telescope for a one-coefficient weighted recurrence.
No machine-level terminal inference enters this lemma. -/
theorem bankTrialSuccessCutHistoryOpaqueTelescope
    (D : Nat) (mass debt : Nat → Nat)
    (hstep : ∀ i, D * mass i ≤
      D * mass (i + 1) + debt i) :
    ∀ j, D * mass 0 ≤
      D * mass j + bankTrialSuccessStageIndexSum debt j := by
  intro j
  induction j with
  | zero =>
      simp [bankTrialSuccessStageIndexSum]
  | succ j ih =>
      calc
        D * mass 0 ≤
          D * mass j +
            bankTrialSuccessStageIndexSum debt j := ih
        _ ≤ (D * mass (j + 1) + debt j) +
            bankTrialSuccessStageIndexSum debt j :=
              Nat.add_le_add_right (hstep j) _
        _ = D * mass (j + 1) +
            bankTrialSuccessStageIndexSum debt (j + 1) := by
              change
                (D * mass (j + 1) + debt j) +
                  bankTrialSuccessStageIndexSum debt j =
                D * mass (j + 1) +
                  (bankTrialSuccessStageIndexSum debt j + debt j)
              omega

/-- Completed (1)+(2) telescope to any chronological cut j.
The later identification of W_j with completed-head mass and
the sharp bound on total weighted debt are distinct obligations. -/
theorem bankTrialSuccessCutHistoryWeightedTelescopeOfKernel
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hkernel : BankTrialC5WorkerExcursionKernel
      (O := BankTrialC5ActualOrigin n q)
      (starts := bankTrialC5ActualStarts ring root S)
      (post := fun o => o.after)
      (returned := bankTrialC5ActualReturned)
      (badExit := bankTrialC5ActualBadExit)
      (timeout := bankTrialC5ActualTimeout ring root)
      (increment := fun o => o.increment)
      (heads := fun o => o.heads) ring root S)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (j T : Nat) :
    bankTrialProbabilityC5WorkerDenominator q * n ^ T ≤
      bankTrialProbabilityC5WorkerDenominator q *
        bankTrialSuccessCutHistoryWeightedMass ring root S j T +
      bankTrialSuccessStageIndexSum
        (fun i => bankTrialSuccessCutHistoryPrefixDebt
          ring root S i T) j := by
  have hstep (i : Nat) :
      bankTrialProbabilityC5WorkerDenominator q *
        bankTrialSuccessCutHistoryWeightedMass ring root S i T ≤
      bankTrialProbabilityC5WorkerDenominator q *
        bankTrialSuccessCutHistoryWeightedMass
          ring root S (i + 1) T +
      bankTrialSuccessCutHistoryPrefixDebt ring root S i T :=
    bankTrialSuccessCutHistoryWeightedStepOfKernel
      ring root S hkernel hlarge hclean i T
  have htel := bankTrialSuccessCutHistoryOpaqueTelescope
    (bankTrialProbabilityC5WorkerDenominator q)
    (fun i => bankTrialSuccessCutHistoryWeightedMass
      ring root S i T)
    (fun i => bankTrialSuccessCutHistoryPrefixDebt
      ring root S i T)
    hstep j
  rw [bankTrialSuccessCutHistoryWeightedMassZero] at htel
  exact htel


end L3
#print axioms L3.bankTrialSuccessCutHistoryWeightedMassZero
#print axioms L3.bankTrialSuccessCutHistoryEarlierExists
#print axioms L3.bankTrialSuccessCutHistoryArmedAppend
#print axioms L3.bankTrialSuccessCutHistorySumExt
#print axioms L3.bankTrialSuccessCutHistoryCountAppend
#print axioms L3.bankTrialSuccessCutHistoryCountAtCut
#print axioms L3.bankTrialSuccessCutHistoryCountSucc
#print axioms L3.bankTrialSuccessCutHistoryModeAtCut
#print axioms L3.bankTrialSuccessCutHistoryPowerSucc
#print axioms L3.bankTrialSuccessCutHistoryCountLeIndex
#print axioms L3.bankTrialSuccessCutHistoryRarityInflate
#print axioms L3.bankTrialSuccessCutHistoryLocalStage
#print axioms L3.bankTrialSuccessCutHistoryOpaqueScale
#print axioms L3.bankTrialSuccessCutHistoryLocalScaled
#print axioms L3.bankTrialSuccessCutHistoryOpaqueListSum
#print axioms L3.bankTrialSuccessCutHistoryPrefixStepOfKernel
#print axioms L3.bankTrialSuccessNatStoppedSumFactor
#print axioms L3.bankTrialSuccessNatStoppedFlatMap
#print axioms L3.bankTrialSuccessNatStoppedSuccSub
#print axioms L3.bankTrialSuccessNatStoppedStepSum
#print axioms L3.bankTrialSuccessNatStoppedSumIsList
#print axioms L3.bankTrialSuccessNatStoppedFactorization
#print axioms L3.bankTrialSuccessCutHistoryNatAtCut
#print axioms L3.bankTrialSuccessCutHistoryNatOfGoodCut
#print axioms L3.bankTrialSuccessCutHistoryNatNone
#print axioms L3.bankTrialSuccessCutHistoryCurrentWordExact
#print axioms L3.bankTrialSuccessCutHistoryMapSumExt
#print axioms L3.bankTrialSuccessCutHistoryWeightedMassFactorization
#print axioms L3.bankTrialSuccessCutHistoryNextWordExact
#print axioms L3.bankTrialSuccessCutHistoryWeightedNextFactorization
#print axioms L3.bankTrialSuccessCutHistoryWeightedStepOfKernel
#print axioms L3.bankTrialSuccessCutHistoryOpaqueTelescope
#print axioms L3.bankTrialSuccessCutHistoryWeightedTelescopeOfKernel
#print axioms L3.bankTrialSuccessCutHistoryPenaltyArmed
#print axioms L3.bankTrialSuccessCutHistoryPenaltyCStart
#print axioms L3.bankTrialSuccessCutHistoryDoubleMul
#print axioms L3.bankTrialSuccessNatStoppedFactorizationLocal

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-!
The real head count is bankTrialLiveHeadCount.  The existing
bankTrialC5ActualAllWordsHeadCap proves its bound by K on
every CLEAN physical scheduler word.  This block proves that
the FIRST authenticated good cut pays a head and that after any
authenticated terminal WON cut there can be no further good cut,
hence no additional ARMED charge.

It does NOT assert that every intermediate ARMED good cut has
a distinct new head between it and its next good return.  That
physical first-good-segment injection remains the missing K1 row.
No conditional theorem with that row as an assumption appears.
-/

/-- A terminal local observer cannot emit a new actual worker
origin, because the census requires an old LIVE phase. -/
theorem bankTrialSuccessTerminalNoWorkerOrigins
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (z : BankTrialLocalState q) (e : Fin n)
    (ht : bankTrialLocalTerminal z) :
    bankTrialC5ActualStarts ring root S z e = [] := by
  unfold bankTrialC5ActualStarts
  split
  · rename_i hguard
    obtain ⟨_, _, _, ⟨begun, nextBegun, hphase, _⟩, _⟩ :=
      hguard
    rcases ht with hwon | hlost
    · rw [hwon] at hphase
      cases hphase
    · rw [hlost] at hphase
      cases hphase
  · rfl

/-- The first-origin scanner cannot produce a new GOOD result
from either absorbing terminal state, on any physical suffix. -/
theorem bankTrialSuccessTerminalPostHeadNone
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (z : BankTrialLocalState q)
    (ht : bankTrialLocalTerminal z) :
    ∀ w : List (Fin n),
      bankTrialC5PostHeadFirstExit ring root S w z = none := by
  intro w
  induction w with
  | nil =>
      rfl
  | cons e tail ih =>
      have hnone :=
        bankTrialSuccessTerminalNoWorkerOrigins
          ring root S z e ht
      have hframe :=
        bankTrialLocalTerminalAbsorbs ring root e z ht
      change
        (match bankTrialC5ActualStarts ring root S z e with
         | [] =>
             bankTrialC5PostHeadFirstExit ring root S tail
               (bankTrialLocalNext ring root z e)
         | o :: _ =>
             bankTrialC5WorkerFirstExit ring root o tail
               (bankTrialLocalNext ring root z e)) = none
      rw [hnone, hframe]
      exact ih

/-- The recursive first GOOD-prefix recognizer is also empty
on every suffix of a terminal seed, for any accumulator. -/
theorem bankTrialSuccessTerminalFirstGoodNone
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (z : BankTrialLocalState q)
    (ht : bankTrialLocalTerminal z) :
    ∀ (remaining acc : List (Fin n)),
      bankTrialSuccessFirstGoodReturnPrefix
        ring root S z acc remaining = none := by
  intro remaining
  induction remaining with
  | nil =>
      intro acc
      have hnone := bankTrialSuccessTerminalPostHeadNone
        ring root S z ht acc
      change
        (if bankTrialC5PostHeadFirstExit ring root S acc z =
            some true then some acc else none) = none
      rw [hnone]
      rfl
  | cons e tail ih =>
      intro acc
      have hnone := bankTrialSuccessTerminalPostHeadNone
        ring root S z ht acc
      change
        (if bankTrialC5PostHeadFirstExit ring root S acc z =
            some true then some acc
          else bankTrialSuccessFirstGoodReturnPrefix
            ring root S z (acc ++ [e]) tail) = none
      rw [hnone]
      exact ih (acc ++ [e])

/-- No successor GOOD cut exists once the j-th authenticated
cut is a physical WON state. The word need not end at the cut. -/
theorem bankTrialSuccessWonGoodCutNextNone
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word cut : List (Fin n)) (j : Nat)
    (hcut :
      bankTrialSuccessGoodReturnCutPrefix
        ring root S word j = some cut)
    (hwon :
      (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S)).phase = .won) :
    bankTrialSuccessGoodReturnCutPrefix
      ring root S word (j + 1) = none := by
  have hfirst :
      bankTrialSuccessFirstGoodReturnPrefix
        ring root S
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S))
        [] (word.drop cut.length) = none :=
    bankTrialSuccessTerminalFirstGoodNone
      ring root S
      (bankTrialLocalRun ring root cut (bankTrialLocalStart S))
      (Or.inl hwon) (word.drop cut.length) []
  simp only [bankTrialSuccessGoodReturnCutPrefix, hcut, hfirst]

/-- If a good-return cut is missing, every subsequent ARMED
indicator is zero and its accumulated count is frozen. -/
theorem bankTrialSuccessHistoryCountFrozenAfterMissing
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word : List (Fin n)) (j : Nat)
    (hmiss :
      bankTrialSuccessGoodReturnCutPrefix
        ring root S word j = none) :
    ∀ i : Nat, j ≤ i →
      bankTrialSuccessCutHistoryArmedCount
        ring root S word i =
      bankTrialSuccessCutHistoryArmedCount
        ring root S word j := by
  intro i
  induction i with
  | zero =>
      intro hi
      have hj : j = 0 := by omega
      subst j
      have hzero :
          bankTrialSuccessGoodReturnCutPrefix
            ring root S word 0 = some [] := rfl
      have hbad := hzero.symm.trans hmiss
      cases hbad
  | succ i ih =>
      intro hi
      by_cases hbefore : j ≤ i
      · have hnone :=
          bankTrialSuccessGoodReturnCutNoneAbove
            ring root S word j hmiss i hbefore
        have hindicator :
            bankTrialSuccessCutArmedWordMass
              ring root S word i = 0 := by
          simp only [bankTrialSuccessCutArmedWordMass, hnone]
        rw [bankTrialSuccessCutHistoryCountSucc, hindicator,
          Nat.add_zero]
        exact ih hbefore
      · have heq : j = i + 1 := by omega
        rw [heq]

/-- Consequently a WON cut freezes the earlier stage-history
weight on every subsequent cut index of the SAME word. -/
theorem bankTrialSuccessWonHistoryCountFrozen
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word cut : List (Fin n)) (j i : Nat)
    (hcut :
      bankTrialSuccessGoodReturnCutPrefix
        ring root S word j = some cut)
    (hwon :
      (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S)).phase = .won)
    (hi : j + 1 ≤ i) :
    bankTrialSuccessCutHistoryArmedCount
      ring root S word i =
    bankTrialSuccessCutHistoryArmedCount
      ring root S word (j + 1) := by
  exact bankTrialSuccessHistoryCountFrozenAfterMissing
    ring root S word (j + 1)
    (bankTrialSuccessWonGoodCutNextNone
      ring root S word cut j hcut hwon) i hi

/-- K1 holds unconditionally on the early chronological range
j<=K, even if the cut is absent. This is deliberately NOT the
requested unrestricted machine-level K1 statement. -/
theorem bankTrialSuccessHistoryEarlyArmedBound
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word : List (Fin n)) (j : Nat)
    (hj : j ≤ (compileAdvice q).K) :
    bankTrialSuccessCutHistoryArmedCount
      ring root S word j ≤ (compileAdvice q).K := by
  exact Nat.le_trans
    (bankTrialSuccessCutHistoryCountLeIndex
      ring root S word j) hj

/-- At the first authentic GOOD cut, the one ARMED charge
of the CLEAN initial cut is backed by a real physical HEAD.
This is the base case of the missing full count-to-head
induction; no invented head-count equality is assumed. -/
theorem bankTrialSuccessFirstGoodCutArmedPaid
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (word cut : List (Fin n))
    (hcut :
      bankTrialSuccessGoodReturnCutPrefix
        ring root S word 1 = some cut) :
    bankTrialSuccessCutHistoryArmedCount
      ring root S word 1 ≤
      bankTrialLiveHeadCount ring root cut
        (bankTrialLocalStart S) := by
  have hpaid :=
    bankTrialSuccessNonzeroGoodReturnCutHeadsPositive
      ring root S hsp hlarge hwidth hclean
      word cut 0 hcut
  have hgate :
      BankTrialProbabilityArmedGate (bankTrialLocalStart S) :=
    ⟨⟨false, rfl⟩, hclean.2.1⟩
  have hone :
      bankTrialSuccessCutHistoryArmedCount
        ring root S word 1 = 1 := by
    change
      0 + (if BankTrialProbabilityArmedGate
        (bankTrialLocalStart S) then 1 else 0) = 1
    rw [if_pos hgate]
  rw [hone]
  omega

end L3

#print axioms L3.bankTrialSuccessTerminalNoWorkerOrigins
#print axioms L3.bankTrialSuccessTerminalPostHeadNone
#print axioms L3.bankTrialSuccessTerminalFirstGoodNone
#print axioms L3.bankTrialSuccessWonGoodCutNextNone
#print axioms L3.bankTrialSuccessHistoryCountFrozenAfterMissing
#print axioms L3.bankTrialSuccessWonHistoryCountFrozen
#print axioms L3.bankTrialSuccessHistoryEarlyArmedBound
#print axioms L3.bankTrialSuccessFirstGoodCutArmedPaid

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-!
K1-HEAD-INJECTION.

The two paths covered below are:
* ARMED, first outgoing HEAD, no worker -> CSTART, then
  comparator origin and its GOOD return;
* ARMED, first outgoing HEAD launches IWAIT, then its
  GOOD return to CSTART.
On the next cycle CSTART comparator GOOD returns to ARMED
without an additional HEAD.  Hence the induction charges only
ARMED good cuts, not all good cuts.
-/

/-- A non-LIVE observer cannot become LIVE by one service. -/
private theorem bankTrialSuccessNonliveNext
    {n q : Nat} (ring : DirectedRing n)
    (root e : Fin n) (z : BankTrialLocalState q)
    (h : ∀ begun : Bool, z.phase ≠ .live begun) :
    ∀ begun : Bool,
      (bankTrialLocalNext ring root z e).phase ≠ .live begun := by
  intro begun
  cases z with
  | mk B phase =>
      cases phase with
      | live old =>
          exact False.elim (h old rfl)
      | recovery =>
          simp only [bankTrialLocalNext]
          split <;> (try split) <;> simp
      | won =>
          simp [bankTrialLocalNext]
      | lost =>
          simp [bankTrialLocalNext]

/-- An actual worker origin requires a LIVE old state. -/
private theorem bankTrialSuccessNonliveNoOrigin
    {n q : Nat} (ring : DirectedRing n)
    (root e : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (z : BankTrialLocalState q)
    (h : ∀ begun : Bool, z.phase ≠ .live begun) :
    bankTrialC5ActualStarts ring root S z e = [] := by
  unfold bankTrialC5ActualStarts
  split
  · rename_i hg
    obtain ⟨begun, nextBegun, hlive, _⟩ := hg.2.2.2.1
    exact False.elim (h begun hlive)
  · rfl

/-- Once the observer is in RECOVERY or terminal, the
first-origin scanner can never classify a new GOOD return. -/
private theorem bankTrialSuccessNonlivePostHeadNone
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    ∀ (w : List (Fin n)) (z : BankTrialLocalState q),
      (∀ begun : Bool, z.phase ≠ .live begun) →
      bankTrialC5PostHeadFirstExit ring root S w z = none := by
  intro w
  induction w with
  | nil =>
      intro z h
      rfl
  | cons e tail ih =>
      intro z h
      have hs := bankTrialSuccessNonliveNoOrigin
        ring root e S z h
      have hn := bankTrialSuccessNonliveNext
        ring root e z h
      change
        (match bankTrialC5ActualStarts ring root S z e with
        | [] =>
            bankTrialC5PostHeadFirstExit ring root S tail
              (bankTrialLocalNext ring root z e)
        | o :: _ =>
            bankTrialC5WorkerFirstExit ring root o tail
              (bankTrialLocalNext ring root z e)) = none
      rw [hs]
      exact ih (bankTrialLocalNext ring root z e) hn

/-- There is no new origin at a non-outgoing edge. -/
private theorem bankTrialSuccessAwayFromRootNoOrigin
    {n q : Nat} (ring : DirectedRing n)
    (root e : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (z : BankTrialLocalState q) (he : e ≠ root) :
    bankTrialC5ActualStarts ring root S z e = [] := by
  unfold bankTrialC5ActualStarts
  split
  · rename_i hg
    exact False.elim (he hg.2.2.1)
  · rfl

/-- Physical obstruction to a false GOOD return: on any
CLEAN-reachable ARMED cut with authentic credit, a suffix
containing zero *new* HEADS cannot have a GOOD first-origin
classification.  An incoming first incident enters recovery,
and every nonincident letter preserves the ARMED gate. -/
private theorem bankTrialSuccessArmedZeroHeadsNoGood
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S) :
    ∀ (w pre : List (Fin n))
      (z : BankTrialLocalState q) (begun : Bool),
      z = bankTrialLocalRun ring root pre
        (bankTrialLocalStart S) →
      z.phase = .live begun →
      bankTrialLiveWaveRootMode z.bank = .ARMED →
      (begun = false ∨ 0 < bankTrialLiveCarryValue z.bank) →
      bankTrialLiveHeadCount ring root w z = 0 →
      bankTrialC5PostHeadFirstExit ring root S w z = none := by
  intro w
  induction w with
  | nil =>
      intro pre z begun hz hlive hm hcredit hzero
      rfl
  | cons e tail ih =>
      intro pre z begun hz hlive hm hcredit hzero
      have hgate : BankTrialProbabilityArmedGate z :=
        ⟨⟨begun, hlive⟩, hm⟩
      by_cases he : e = root
      · have hpositive :
            (if BankTrialProbabilityArmedGate z ∧ e = root
              then 1 else 0) = 1 := if_pos ⟨hgate, he⟩
        change
          (if BankTrialProbabilityArmedGate z ∧ e = root
            then 1 else 0) +
          bankTrialLiveHeadCount ring root tail
            (bankTrialLocalNext ring root z e) = 0 at hzero
        rw [hpositive] at hzero
        omega
      · have hno := bankTrialSuccessAwayFromRootNoOrigin
          ring root e S z he
        by_cases hi : ring.rightNeighbor e = root
        · have hstart := bankTrialSuccessReachableArmedStart
            ring root S hlarge hclean pre z hz hgate
          have hf : z.bank.success = false :=
            hstart.2.2.2.1
          have hshape :
              z = (⟨z.bank, .live begun⟩ :
                BankTrialLocalState q) := by
            cases z with
            | mk B phase =>
                change phase = .live begun at hlive
                cases hlive
                rfl
          have hrec :
              (bankTrialLocalNext ring root z e).phase =
                .recovery := by
            rw [hshape]
            exact congrArg BankTrialLocalState.phase
              (bankTrialProbabilityIncomingArmedEntersRecovery
                ring root e z.bank begun hf hm he hi)
          have hnon :
              ∀ b : Bool,
                (bankTrialLocalNext ring root z e).phase ≠
                  .live b := by
            intro b
            rw [hrec]
            intro hbad
            cases hbad
          change
            (match bankTrialC5ActualStarts ring root S z e with
            | [] =>
                bankTrialC5PostHeadFirstExit ring root S tail
                  (bankTrialLocalNext ring root z e)
            | o :: _ =>
                bankTrialC5WorkerFirstExit ring root o tail
                  (bankTrialLocalNext ring root z e)) = none
          rw [hno]
          exact bankTrialSuccessNonlivePostHeadNone
            ring root S tail (bankTrialLocalNext ring root z e)
            hnon
        · obtain ⟨nextBegun, hp, hmode, hcreditNext⟩ :=
            bankTrialSuccessArmedNonincidentCreditNext
              ring root e S hlarge hclean pre z begun
              hz hlive hm hcredit he hi
          have hzNext :
              bankTrialLocalNext ring root z e =
                bankTrialLocalRun ring root (pre ++ [e])
                  (bankTrialLocalStart S) := by
            rw [bankTrialLocalRunAppend, ← hz]
            rfl
          have hnot :
              ¬ (BankTrialProbabilityArmedGate z ∧ e = root) := by
            intro h
            exact he h.2
          have hzeroTail :
              bankTrialLiveHeadCount ring root tail
                (bankTrialLocalNext ring root z e) = 0 := by
            simpa only [bankTrialLiveHeadCount,
              if_neg hnot, Nat.zero_add] using hzero
          have hrest :=
            ih (pre ++ [e]) (bankTrialLocalNext ring root z e)
              nextBegun hzNext hp hmode hcreditNext hzeroTail
          change
            (match bankTrialC5ActualStarts ring root S z e with
            | [] =>
                bankTrialC5PostHeadFirstExit ring root S tail
                  (bankTrialLocalNext ring root z e)
            | o :: _ =>
                bankTrialC5WorkerFirstExit ring root o tail
                  (bankTrialLocalNext ring root z e)) = none
          rw [hno]
          exact hrest

/-- The first GOOD prefix is recognized by the scanner
on precisely its returned segment. -/
private theorem bankTrialSuccessFirstGoodSelfScan
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (z : BankTrialLocalState q) :
    ∀ (remaining acc found : List (Fin n)),
      bankTrialSuccessFirstGoodReturnPrefix
        ring root S z acc remaining = some found →
      bankTrialC5PostHeadFirstExit ring root S found z =
        some true := by
  intro remaining
  induction remaining with
  | nil =>
      intro acc found hfound
      by_cases hg :
          bankTrialC5PostHeadFirstExit ring root S acc z =
            some true
      · have heq : acc = found := Option.some.inj (by
          simpa only [bankTrialSuccessFirstGoodReturnPrefix,
            if_pos hg] using hfound)
        rw [← heq]
        exact hg
      · simp only [bankTrialSuccessFirstGoodReturnPrefix,
          if_neg hg] at hfound
        cases hfound
  | cons e tail ih =>
      intro acc found hfound
      by_cases hg :
          bankTrialC5PostHeadFirstExit ring root S acc z =
            some true
      · have heq : acc = found := Option.some.inj (by
          simpa only [bankTrialSuccessFirstGoodReturnPrefix,
            if_pos hg] using hfound)
        rw [← heq]
        exact hg
      · have htail :
            bankTrialSuccessFirstGoodReturnPrefix
              ring root S z (acc ++ [e]) tail = some found := by
          simpa only [bankTrialSuccessFirstGoodReturnPrefix,
            if_neg hg] using hfound
        exact ih (acc ++ [e]) found htail

/-- Invert two adjacent authentic GOOD cuts to obtain their
actual intervening word on the original scheduler tape. -/
theorem bankTrialSuccessAdjacentGoodSegment
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word cut nextCut : List (Fin n)) (i : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word i = some cut)
    (hnext : bankTrialSuccessGoodReturnCutPrefix
      ring root S word (i + 1) = some nextCut) :
    ∃ segment : List (Fin n),
      bankTrialSuccessFirstGoodReturnPrefix ring root S
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S))
        [] (word.drop cut.length) = some segment ∧
      nextCut = cut ++ segment := by
  simp only [bankTrialSuccessGoodReturnCutPrefix, hcut] at hnext
  cases hscan :
      bankTrialSuccessFirstGoodReturnPrefix ring root S
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S))
        [] (word.drop cut.length) with
  | none =>
      simp only [hscan] at hnext
      cases hnext
  | some segment =>
      have heq : cut ++ segment = nextCut := by
        have hsome : some (cut ++ segment) = some nextCut := by
          simpa only [hscan] using hnext
        exact Option.some.inj hsome
      exact ⟨segment, rfl, heq.symm⟩

/-- Every adjacent GOOD cut is a later physical prefix,
so HEAD count never decreases.  This handles a CSTART cut
as well as a failed ARMED gate without requiring a HEAD. -/
theorem bankTrialSuccessAdjacentGoodHeadsMono
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word cut nextCut : List (Fin n)) (i : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word i = some cut)
    (hnext : bankTrialSuccessGoodReturnCutPrefix
      ring root S word (i + 1) = some nextCut) :
    bankTrialLiveHeadCount ring root cut
      (bankTrialLocalStart S) ≤
    bankTrialLiveHeadCount ring root nextCut
      (bankTrialLocalStart S) := by
  obtain ⟨segment, _, heq⟩ :=
    bankTrialSuccessAdjacentGoodSegment
      ring root S word cut nextCut i hcut hnext
  rw [heq, bankTrialLiveHeadCountAppend]
  omega

/-- An authenticated ARMED cut has the disjunction needed for
the physical zero-HEAD exclusion: it is the unbegun CLEAN cut,
or a positive-index cut with positive authentic carry. -/
private theorem bankTrialSuccessArmedGoodCutCredit
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (word cut : List (Fin n)) (i : Nat)
    (z : BankTrialLocalState q)
    (hz : z = bankTrialLocalRun ring root cut
      (bankTrialLocalStart S))
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word i = some cut)
    (hgate : BankTrialProbabilityArmedGate z) :
    ∃ begun : Bool,
      z.phase = .live begun ∧
      (begun = false ∨
        0 < bankTrialLiveCarryValue z.bank) := by
  obtain ⟨⟨begun, hlive⟩, hm⟩ := hgate
  refine ⟨begun, hlive, ?_⟩
  cases i with
  | zero =>
      have hc : ([] : List (Fin n)) = cut :=
        Option.some.inj (by
          simpa only [bankTrialSuccessGoodReturnCutPrefix]
            using hcut)
      have hzStart : z = bankTrialLocalStart S := by
        rw [← hc] at hz
        simpa only [bankTrialLocalRun] using hz
      have hb : begun = false := by
        rw [hzStart] at hlive
        cases begun with
        | false =>
            rfl
        | true =>
            change BankTrialLocalPhase.live false =
              .live true at hlive
            cases hlive
      exact Or.inl hb
  | succ j =>
      have hself :=
        bankTrialSuccessGoodReturnCutSelf
          ring root S word (j + 1) cut hcut
      have hstop :
          bankTrialSuccessGoodReturnCutBool
            ring root S (j + 1) cut
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) = true := by
        change decide
          (bankTrialSuccessGoodReturnCutPrefix
            ring root S cut (j + 1) = some cut) = true
        simp [hself]
      have hliveCut :
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)).phase = .live begun := by
        rw [← hz]
        exact hlive
      have hpos :=
        bankTrialSuccessNonzeroArmedCutCarryPositive
          ring root S hsp hlarge hwidth hclean
          cut j begun hstop hliveCut
      rw [hz]
      exact Or.inr hpos

/-- THE REQUESTED PHYSICAL STEP. The scanner cannot find the
next GOOD return with zero new HEADS when the old cut is ARMED.
A workerless HEAD is counted at the outgoing root service
even though it emits no increment worker. -/
theorem bankTrialSuccessAdjacentArmedGoodHeadStrict
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (word cut nextCut : List (Fin n)) (i : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word i = some cut)
    (hnext : bankTrialSuccessGoodReturnCutPrefix
      ring root S word (i + 1) = some nextCut)
    (hgate : BankTrialProbabilityArmedGate
      (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S))) :
    bankTrialLiveHeadCount ring root cut
      (bankTrialLocalStart S) + 1 ≤
    bankTrialLiveHeadCount ring root nextCut
      (bankTrialLocalStart S) := by
  obtain ⟨segment, hscan, heq⟩ :=
    bankTrialSuccessAdjacentGoodSegment
      ring root S word cut nextCut i hcut hnext
  have hself :=
    bankTrialSuccessFirstGoodSelf ring root S
      (bankTrialLocalRun ring root cut (bankTrialLocalStart S))
      (word.drop cut.length) segment hscan
  have hgood :
      bankTrialC5PostHeadFirstExit ring root S segment
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)) = some true :=
    bankTrialSuccessFirstGoodSelfScan ring root S
      (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S))
      segment [] segment hself
  obtain ⟨begun, hlive, hcredit⟩ :=
    bankTrialSuccessArmedGoodCutCredit
      ring root S hsp hlarge hwidth hclean
      word cut i
      (bankTrialLocalRun ring root cut (bankTrialLocalStart S))
      rfl hcut hgate
  have hpositive :
      0 < bankTrialLiveHeadCount ring root segment
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)) := by
    by_cases hz :
        bankTrialLiveHeadCount ring root segment
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) = 0
    · have hnone := bankTrialSuccessArmedZeroHeadsNoGood
        ring root S hlarge hclean
        segment cut
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)) begun
        rfl hlive hgate.2 hcredit hz
      rw [hgood] at hnone
      cases hnone
    · omega
  rw [heq, bankTrialLiveHeadCountAppend]
  omega

/-- The failure of the ARMED gate needs no new HEAD:
the history does not gain a unit, and the physical count
is monotone across the same two prefixes. -/
theorem bankTrialSuccessAdjacentClosedGateHistoryStep
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word cut nextCut : List (Fin n)) (i : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word i = some cut)
    (hnext : bankTrialSuccessGoodReturnCutPrefix
      ring root S word (i + 1) = some nextCut)
    (hclosed : ¬ BankTrialProbabilityArmedGate
      (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S)))
    (hpaid : bankTrialSuccessCutHistoryArmedCount
      ring root S word i ≤
      bankTrialLiveHeadCount ring root cut
        (bankTrialLocalStart S)) :
    bankTrialSuccessCutHistoryArmedCount
      ring root S word (i + 1) ≤
      bankTrialLiveHeadCount ring root nextCut
        (bankTrialLocalStart S) := by
  rw [bankTrialSuccessCutHistoryCountSucc,
    bankTrialSuccessCutHistoryModeAtCut
      ring root S word cut i hcut, if_neg hclosed, Nat.add_zero]
  exact Nat.le_trans hpaid
    (bankTrialSuccessAdjacentGoodHeadsMono
      ring root S word cut nextCut i hcut hnext)

/-- K1: chronological ARMED good-cut charges inject into
distinct physical HEAD decisions, on the very same tape. -/
theorem bankTrialSuccessEveryGoodCutArmedPaid
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (word : List (Fin n)) :
    ∀ (j : Nat) (cut : List (Fin n)),
      bankTrialSuccessGoodReturnCutPrefix
        ring root S word j = some cut →
      bankTrialSuccessCutHistoryArmedCount
        ring root S word j ≤
      bankTrialLiveHeadCount ring root cut
        (bankTrialLocalStart S) := by
  intro j
  induction j with
  | zero =>
      intro cut hcut
      change 0 ≤ bankTrialLiveHeadCount ring root cut
        (bankTrialLocalStart S)
      exact Nat.zero_le _
  | succ j ih =>
      intro cut hcut
      obtain ⟨prev, hprev⟩ :=
        bankTrialSuccessCutHistoryEarlierExists
          ring root S word cut j (j + 1)
          (by omega) hcut
      have hpaid := ih prev hprev
      by_cases hgate : BankTrialProbabilityArmedGate
          (bankTrialLocalRun ring root prev
            (bankTrialLocalStart S))
      · have hstrict :=
          bankTrialSuccessAdjacentArmedGoodHeadStrict
            ring root S hsp hlarge hwidth hclean
            word prev cut j hprev hcut hgate
        rw [bankTrialSuccessCutHistoryCountSucc,
          bankTrialSuccessCutHistoryModeAtCut
            ring root S word prev j hprev, if_pos hgate]
        omega
      · exact bankTrialSuccessAdjacentClosedGateHistoryStep
          ring root S word prev cut j
          hprev hcut hgate hpaid

/-- K1 followed by the proved installed all-words C5 HEAD cap. -/
theorem bankTrialSuccessEveryGoodCutArmedCap
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (word cut : List (Fin n)) (j : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word j = some cut) :
    bankTrialSuccessCutHistoryArmedCount
      ring root S word j ≤ (compileAdvice q).K := by
  exact Nat.le_trans
    (bankTrialSuccessEveryGoodCutArmedPaid
      ring root S hsp hlarge hwidth hclean
      word j cut hcut)
    (bankTrialC5ActualAllWordsHeadCap
      ring root S hsp hlarge hwidth hclean cut)

end L3

#print axioms L3.bankTrialSuccessAdjacentGoodSegment
#print axioms L3.bankTrialSuccessAdjacentGoodHeadsMono
#print axioms L3.bankTrialSuccessAdjacentArmedGoodHeadStrict
#print axioms L3.bankTrialSuccessAdjacentClosedGateHistoryStep
#print axioms L3.bankTrialSuccessEveryGoodCutArmedPaid
#print axioms L3.bankTrialSuccessEveryGoodCutArmedCap

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Opaque arithmetic; in the power argument the entire power is an
uninterpreted Nat, rather than an expression normalized by omega. -/
theorem bankTrialSuccessOpaqueDoubleUpper (x : Nat) :
    x ≤ x * 2 := by
  omega

theorem bankTrialSuccessTwoPowerMonotone :
    ∀ (a b : Nat), a ≤ b → 2 ^ a ≤ 2 ^ b := by
  intro a b
  induction b with
  | zero =>
      intro hab
      have ha : a = 0 := by omega
      subst a
      exact Nat.le_refl _
  | succ b ih =>
      intro hab
      by_cases hle : a ≤ b
      · exact Nat.le_trans (ih hle)
          (by rw [Nat.pow_succ]; exact bankTrialSuccessOpaqueDoubleUpper (2 ^ b))
      · have ha : a = b + 1 := by omega
        rw [ha]
        exact Nat.le_refl _

/-- What K1 actually implies at the original physical horizon:
the history-weighted j-th GOOD-cut mass is at most 2^K times
the UNWEIGHTED j-th GOOD-cut mass.  This does not say that
the j-th cut is a completed-K-head event. -/
theorem bankTrialSuccessWeightedMassReachCap
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (j T : Nat) :
    bankTrialSuccessCutHistoryWeightedMass ring root S j T ≤
      2 ^ (compileAdvice q).K *
        bankTrialSuccessCutReachMass ring root S j T := by
  unfold bankTrialSuccessCutHistoryWeightedMass
    bankTrialSuccessCutReachMass
  rw [← bankTrialSuccessScheduleSumScale]
  apply bankTrialProbabilityScheduleSumMono n T
  intro word
  cases hcut :
      bankTrialSuccessGoodReturnCutPrefix ring root S word j with
  | none =>
      simp [Prob.indicator, hcut]
  | some cut =>
      have hcount :=
        bankTrialSuccessEveryGoodCutArmedCap
          ring root S hsp hlarge hwidth hclean
          word cut j hcut
      have hpower := bankTrialSuccessTwoPowerMonotone
        (bankTrialSuccessCutHistoryArmedCount
          ring root S word j) (compileAdvice q).K hcount
      simpa [Prob.indicator, hcut] using hpower

/-- List-sum scaling, proved without Finset. -/
theorem bankTrialSuccessListMapScale
    {A : Type} (xs : List A) (c : Nat) (f : A → Nat) :
    (xs.map (fun x => c * f x)).sum =
      c * (xs.map f).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

/-- The rarity component of the existing PrefixDebt definition
is EXACTLY 2*N*W_j, not N*M_j. -/
theorem bankTrialSuccessRarityDebtExact
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j T : Nat) :
    ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
      (bankTrialSuccessGoodReturnCutBool ring root S j)
      T [] (bankTrialLocalStart S)).map (fun cut =>
        2 * bankTrialProbabilityC5WorkerNumerator q *
          (2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S cut j * n ^ (T - cut.length)))).sum =
      2 * bankTrialProbabilityC5WorkerNumerator q *
        bankTrialSuccessCutHistoryWeightedMass ring root S j T := by
  rw [bankTrialSuccessCutHistoryWeightedMassFactorization
    ring root S j T]
  unfold bankTrialSuccessCutHistoryPrefixMass
  exact bankTrialSuccessListMapScale
    (Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
      (bankTrialSuccessGoodReturnCutBool ring root S j)
      T [] (bankTrialLocalStart S))
    (2 * bankTrialProbabilityC5WorkerNumerator q)
    (fun cut =>
      2 ^ bankTrialSuccessCutHistoryArmedCount
        ring root S cut j * n ^ (T - cut.length))

/-- The unconditional rarity bound obtained from the existing
K1 cap, before any new head-conditioned rarity theorem.
Its coefficient is 2^(K+1)*N, not N. -/
theorem bankTrialSuccessRarityDebtKOneUpper
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (j T : Nat) :
    ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
      (bankTrialSuccessGoodReturnCutBool ring root S j)
      T [] (bankTrialLocalStart S)).map (fun cut =>
        2 * bankTrialProbabilityC5WorkerNumerator q *
          (2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S cut j * n ^ (T - cut.length)))).sum ≤
      (2 * bankTrialProbabilityC5WorkerNumerator q *
        2 ^ (compileAdvice q).K) * n ^ T := by
  have hweighted :
      bankTrialSuccessCutHistoryWeightedMass
        ring root S j T ≤ 2 ^ (compileAdvice q).K * n ^ T :=
    Nat.le_trans
      (bankTrialSuccessWeightedMassReachCap
        ring root S hsp hlarge hwidth hclean j T)
      (Nat.mul_le_mul_left (2 ^ (compileAdvice q).K)
        (bankTrialSuccessCutReachMassLeTotal
          ring root S j T))
  calc
    ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
      (bankTrialSuccessGoodReturnCutBool ring root S j)
      T [] (bankTrialLocalStart S)).map (fun cut =>
        2 * bankTrialProbabilityC5WorkerNumerator q *
          (2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S cut j * n ^ (T - cut.length)))).sum =
        2 * bankTrialProbabilityC5WorkerNumerator q *
          bankTrialSuccessCutHistoryWeightedMass ring root S j T :=
      bankTrialSuccessRarityDebtExact ring root S j T
    _ ≤ 2 * bankTrialProbabilityC5WorkerNumerator q *
          (2 ^ (compileAdvice q).K * n ^ T) :=
      Nat.mul_le_mul_left _ hweighted
    _ = (2 * bankTrialProbabilityC5WorkerNumerator q *
          2 ^ (compileAdvice q).K) * n ^ T := by
      simp only [Nat.mul_assoc]

/-- Multiply the existing telescope by T and replace W_j by
an upper bound.  All arithmetic arguments are opaque Nats. -/
theorem bankTrialSuccessOpaqueForwardFromDebt
    (D T X W C E : Nat)
    (htelescope : D * X ≤ D * W + E)
    (hcap : W ≤ C) :
    D * T * X ≤ D * T * C + T * E := by
  have hscaled := Nat.mul_le_mul_left T htelescope
  have hcapScaled := Nat.mul_le_mul_left (D * T) hcap
  calc
    D * T * X = T * (D * X) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ T * (D * W + E) := hscaled
    _ = D * T * W + T * E := by
      simp only [Nat.mul_add, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ D * T * C + T * E :=
      Nat.add_le_add_right hcapScaled (T * E)

/-- Unconditional actual-data forward inequality obtained from K1
and the installed actual excursion kernel.  The exact remaining
debt is retained rather than being silently replaced by the
smaller C5 target budget. -/
theorem bankTrialSuccessForwardCutReachWithExactDebt
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (j T : Nat) :
    bankTrialProbabilityC5WorkerDenominator q * T * n ^ T ≤
      bankTrialProbabilityC5WorkerDenominator q * T *
        (2 ^ (compileAdvice q).K *
          bankTrialSuccessCutReachMass ring root S j T) +
      T * bankTrialSuccessStageIndexSum
        (fun i => bankTrialSuccessCutHistoryPrefixDebt
          ring root S i T) j := by
  have hkernel :=
    bankTrialC5ActualWorkerExcursionKernelHolds
      ring root S hsp hlarge hwidth hclean
  exact bankTrialSuccessOpaqueForwardFromDebt
    (bankTrialProbabilityC5WorkerDenominator q)
    T (n ^ T)
    (bankTrialSuccessCutHistoryWeightedMass ring root S j T)
    (2 ^ (compileAdvice q).K *
      bankTrialSuccessCutReachMass ring root S j T)
    (bankTrialSuccessStageIndexSum
      (fun i => bankTrialSuccessCutHistoryPrefixDebt
        ring root S i T) j)
    (bankTrialSuccessCutHistoryWeightedTelescopeOfKernel
      ring root S hkernel hlarge hclean j T)
    (bankTrialSuccessWeightedMassReachCap
      ring root S hsp hlarge hwidth hclean j T)

/-- The explicitly requested stopping index j=2K+1, still
with the ACTUAL telescope debt, not an invented small budget. -/
theorem bankTrialSuccessForwardAtStartCapWithExactDebt
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (T : Nat) :
    bankTrialProbabilityC5WorkerDenominator q * T * n ^ T ≤
      bankTrialProbabilityC5WorkerDenominator q * T *
        (2 ^ (compileAdvice q).K *
          bankTrialSuccessCutReachMass ring root S
            (2 * (compileAdvice q).K + 1) T) +
      T * bankTrialSuccessStageIndexSum
        (fun i => bankTrialSuccessCutHistoryPrefixDebt
          ring root S i T) (2 * (compileAdvice q).K + 1) := by
  exact bankTrialSuccessForwardCutReachWithExactDebt
    ring root S hsp hlarge hwidth hclean
    (2 * (compileAdvice q).K + 1) T

/-- At a WON cut the terminal contribution in PrefixDebt
is a full D times history-weighted suffix cylinder. -/
theorem bankTrialSuccessWonDebtWeightExact
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (cut : List (Fin n)) (j t : Nat)
    (hwon : (bankTrialLocalRun ring root cut
      (bankTrialLocalStart S)).phase = .won) :
    bankTrialProbabilityC5WorkerDenominator q *
      (2 ^ bankTrialSuccessCutHistoryArmedCount
        ring root S cut j *
        bankTrialSuccessCutWonAt n
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) t) =
    bankTrialProbabilityC5WorkerDenominator q *
      (2 ^ bankTrialSuccessCutHistoryArmedCount
        ring root S cut j * n ^ t) := by
  rw [bankTrialSuccessCutWonAt, if_pos hwon]

/-- A concrete Nat countermodel to the unjustified inference
that K1 and the unweighted mass bound pay the rarity at
coefficient N instead of coefficient 2^(K+1)*N. -/
theorem bankTrialSuccessAbstractRarityBudgetCounterexample :
    ¬ (∀ (K N W M X : Nat),
      W ≤ 2 ^ K * M →
      M ≤ X →
      2 * N * W ≤ N * X) := by
  intro h
  have hw : (2 : Nat) ≤ 2 ^ (1 : Nat) * 1 := by
    change 2 ≤ 2
    exact Nat.le_refl _
  have hm : (1 : Nat) ≤ 1 := Nat.le_refl _
  have hbad := h 1 1 2 1 1 hw hm
  omega

/-- A separate numeric countermodel to dropping the terminal
WON debt from a valid stopped-prefix recurrence. -/
theorem bankTrialSuccessAbstractWonDebtCounterexample :
    ¬ (∀ (D X F R : Nat),
      D * X ≤ D * F + R + D * X →
      D * X ≤ D * F + R) := by
  intro h
  have hp : (1 : Nat) * 1 ≤ 1 * 0 + 0 + 1 * 1 := by omega
  have hbad := h 1 1 0 0 hp
  omega

/-!
K2 NOT CLOSED.

For j=2*K+1, the telescope is now instantiated with actual kernel
and K1, but it gives the j-th GOOD-cut reach mass, not the
completed-K-head mass.  K1 says historyArmedCount <= physical
head count <= K. It does NOT imply that an extant j-th GOOD cut
has the K adapted fair-head decisions required by
bankTrialProbabilityC5CompletedHeadWord.

More importantly, bankTrialSuccessCutHistoryPrefixDebt has three
summands at each stopped prefix:
  (a) 2*N*(2^history*n^remaining),
  (b) 2^history*pendingPenalty,
  (c) D*(2^history*WonAt).
The last term equals D*2^history*n^remaining on a WON cut, and
bankTrialSuccessWonGoodCutNextNone proves that this word is ABSENT
from all later weighted cut masses.  It cannot be charged as
worker rarity or pending Markov mass; it must instead be moved
once to the final completed-head cylinder, with a separate proof
of the completed-head predicate.

The first term sums EXACTLY to 2*N*W_i.  K1 and the cut-reach
bound alone give 2^(K+1)*N*n^T PER CUT, versus the required
N*n^T per cut in hforward.  The abstract rarity counterexample
formalizes that this factor cannot be removed merely by Nat
algebra.  A new head-conditioned, fair-bit-compensated rarity
estimate is necessary.  The raw pre-cut pending debt additionally
requires a single-horizon disjoint/Markov transfer.

Hence neither bankTrialSuccessForwardEstimateHolds nor its
completed-head-mass-lower corollary is asserted: doing so from
the currently installed facts would introduce an unproved leaf.
-/

end L3

#print axioms L3.bankTrialSuccessOpaqueDoubleUpper
#print axioms L3.bankTrialSuccessTwoPowerMonotone
#print axioms L3.bankTrialSuccessWeightedMassReachCap
#print axioms L3.bankTrialSuccessListMapScale
#print axioms L3.bankTrialSuccessRarityDebtExact
#print axioms L3.bankTrialSuccessRarityDebtKOneUpper
#print axioms L3.bankTrialSuccessOpaqueForwardFromDebt
#print axioms L3.bankTrialSuccessForwardCutReachWithExactDebt
#print axioms L3.bankTrialSuccessForwardAtStartCapWithExactDebt
#print axioms L3.bankTrialSuccessWonDebtWeightExact
#print axioms L3.bankTrialSuccessAbstractRarityBudgetCounterexample
#print axioms L3.bankTrialSuccessAbstractWonDebtCounterexample

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
The core of (U) is a physical first-incident inclusion for the
*post-head* scanner (not just the pre-head stage classifier).
No arbitrary restarted tape, fairness axiom, or stage leaf is used.
-/

/-- A first outgoing incident is unchanged by appending a suffix. -/
private theorem bankTrialSuccessFirstIncidentHeadAppend
    {n : Nat} (outgoing incoming : Fin n) :
    ∀ (u v : List (Fin n)),
      bankTrialProbabilityFirstIncidentOrientation
        outgoing incoming u = some true →
      bankTrialProbabilityFirstIncidentOrientation
        outgoing incoming (u ++ v) = some true := by
  intro u
  induction u with
  | nil =>
      intro v h
      simp only [bankTrialProbabilityFirstIncidentOrientation] at h
      cases h
  | cons e tail ih =>
      intro v h
      by_cases he : e = outgoing
      · simp [bankTrialProbabilityFirstIncidentOrientation, he]
      · by_cases hi : e = incoming
        · have hio : ¬ incoming = outgoing := fun h' => he (hi.trans h')
          have hf :
            bankTrialProbabilityFirstIncidentOrientation
              outgoing incoming (e :: tail) = some false := by
                simp [bankTrialProbabilityFirstIncidentOrientation,
                  he, hi, hio]
          rw [hf] at h
          cases h
        · have ht :
            bankTrialProbabilityFirstIncidentOrientation
              outgoing incoming tail = some true := by
            simpa only [bankTrialProbabilityFirstIncidentOrientation,
              if_neg he, if_neg hi] using h
          have hrest := ih v ht
          simpa only [List.cons_append,
            bankTrialProbabilityFirstIncidentOrientation,
            if_neg he, if_neg hi] using hrest

/-- At a reachable ARMED cut with the physical carry certificate,
a GOOD first-origin return must have a first outgoing root
incident.  An incoming first incident causes RECOVERY, so no
later actual worker origin can be classified GOOD by this scan. -/
private theorem bankTrialSuccessArmedPostHeadGoodFirstIncident
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S) :
    ∀ (w pre : List (Fin n))
      (z : BankTrialLocalState q) (begun : Bool),
      z = bankTrialLocalRun ring root pre (bankTrialLocalStart S) →
      z.phase = .live begun →
      bankTrialLiveWaveRootMode z.bank = .ARMED →
      (begun = false ∨ 0 < bankTrialLiveCarryValue z.bank) →
      bankTrialC5PostHeadFirstExit ring root S w z = some true →
      bankTrialProbabilityFirstIncidentOrientation
        root (ring.leftNeighbor root) w = some true := by
  intro w
  induction w with
  | nil =>
      intro pre z begun hz hlive hm hcredit hgood
      simp only [bankTrialC5PostHeadFirstExit] at hgood
      cases hgood
  | cons e tail ih =>
      intro pre z begun hz hlive hm hcredit hgood
      by_cases he : e = root
      · simp [bankTrialProbabilityFirstIncidentOrientation, he]
      · have hno := bankTrialSuccessAwayFromRootNoOrigin
          ring root e S z he
        by_cases hi : ring.rightNeighbor e = root
        · have hgate : BankTrialProbabilityArmedGate z :=
            ⟨⟨begun, hlive⟩, hm⟩
          have hstart :=
            bankTrialSuccessReachableArmedStart
              ring root S hlarge hclean pre z hz hgate
          have hf : z.bank.success = false :=
            hstart.2.2.2.1
          have hshape :
              z = (⟨z.bank, .live begun⟩ :
                BankTrialLocalState q) := by
            cases z with
            | mk B phase =>
                change phase = .live begun at hlive
                cases hlive
                rfl
          have hrec :
              (bankTrialLocalNext ring root z e).phase =
                .recovery := by
            rw [hshape]
            exact congrArg BankTrialLocalState.phase
              (bankTrialProbabilityIncomingArmedEntersRecovery
                ring root e z.bank begun hf hm he hi)
          have hnon :
              ∀ b : Bool,
                (bankTrialLocalNext ring root z e).phase ≠
                  .live b := by
            intro b
            rw [hrec]
            intro hbad
            cases hbad
          have hnone :
              bankTrialC5PostHeadFirstExit ring root S
                (e :: tail) z = none := by
            change
              (match bankTrialC5ActualStarts ring root S z e with
              | [] =>
                  bankTrialC5PostHeadFirstExit ring root S tail
                    (bankTrialLocalNext ring root z e)
              | o :: _ =>
                  bankTrialC5WorkerFirstExit ring root o tail
                    (bankTrialLocalNext ring root z e)) = none
            rw [hno]
            exact bankTrialSuccessNonlivePostHeadNone
              ring root S tail (bankTrialLocalNext ring root z e)
              hnon
          rw [hnone] at hgood
          cases hgood
        · have hleft : e ≠ ring.leftNeighbor root := by
            intro hleft
            exact hi ((bankTrialSuccessIncomingIffLeft
              ring root e).mpr hleft)
          have hgoodTail :
              bankTrialC5PostHeadFirstExit ring root S tail
                (bankTrialLocalNext ring root z e) =
                  some true := by
            change
              (match bankTrialC5ActualStarts ring root S z e with
              | [] =>
                  bankTrialC5PostHeadFirstExit ring root S tail
                    (bankTrialLocalNext ring root z e)
              | o :: _ =>
                  bankTrialC5WorkerFirstExit ring root o tail
                    (bankTrialLocalNext ring root z e)) =
                some true at hgood
            rw [hno] at hgood
            exact hgood
          obtain ⟨nextBegun, hp, hmode, hcreditNext⟩ :=
            bankTrialSuccessArmedNonincidentCreditNext
              ring root e S hlarge hclean pre z begun
              hz hlive hm hcredit he hi
          have hzNext :
              bankTrialLocalNext ring root z e =
                bankTrialLocalRun ring root (pre ++ [e])
                  (bankTrialLocalStart S) := by
            rw [bankTrialLocalRunAppend, ← hz]
            rfl
          have htail := ih (pre ++ [e])
            (bankTrialLocalNext ring root z e) nextBegun
            hzNext hp hmode hcreditNext hgoodTail
          simpa only [bankTrialProbabilityFirstIncidentOrientation,
            if_neg he, if_neg hleft] using htail

/-- Transfer the first-outgoing-incidence certificate from the
first recognized GOOD segment to the whole physical suffix. -/
theorem bankTrialSuccessArmedFirstGoodHeadFirst
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (z : BankTrialLocalState q)
    (begun : Bool)
    (hz : z = bankTrialLocalRun ring root pre (bankTrialLocalStart S))
    (hlive : z.phase = .live begun)
    (hm : bankTrialLiveWaveRootMode z.bank = .ARMED)
    (hcredit : begun = false ∨
      0 < bankTrialLiveCarryValue z.bank)
    (word found : List (Fin n))
    (hfound : bankTrialSuccessFirstGoodReturnPrefix
      ring root S z [] word = some found) :
    bankTrialProbabilityFirstIncidentOrientation
      root (ring.leftNeighbor root) word = some true := by
  obtain ⟨taken, suffix, hword, hfoundEq, hshort⟩ :=
    bankTrialSuccessFirstGoodRecognizedPrefix
      ring root S z word [] found hfound
  have htaken : found = taken := by
    simpa only [List.nil_append] using hfoundEq
  rw [htaken] at hshort
  have hpost :
      bankTrialC5PostHeadFirstExit ring root S taken z =
        some true :=
    bankTrialSuccessFirstGoodSelfScan
      ring root S z taken [] taken hshort
  have hfirst :=
    bankTrialSuccessArmedPostHeadGoodFirstIncident
      ring root S hlarge hclean
      taken pre z begun hz hlive hm hcredit hpost
  rw [hword]
  exact bankTrialSuccessFirstIncidentHeadAppend
    root (ring.leftNeighbor root) taken suffix hfirst

/-- The actual first-GOOD numerator on an ARMED cut is a
SUBSET of the original-clock first-outgoing-incident cylinder. -/
theorem bankTrialSuccessArmedFirstGoodMassLeHead
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (z : BankTrialLocalState q)
    (begun : Bool)
    (hz : z = bankTrialLocalRun ring root pre (bankTrialLocalStart S))
    (hlive : z.phase = .live begun)
    (hm : bankTrialLiveWaveRootMode z.bank = .ARMED)
    (hcredit : begun = false ∨
      0 < bankTrialLiveCarryValue z.bank)
    (T : Nat) :
    Prob.scheduleSum n T (fun word =>
      Prob.indicator
        (bankTrialSuccessFirstGoodReturnPrefix
          ring root S z [] word).isSome) ≤
      bankTrialProbabilityFirstIncidentMass
        root (ring.leftNeighbor root) true T := by
  unfold bankTrialProbabilityFirstIncidentMass
  apply bankTrialProbabilityScheduleSumMono n T
  intro word
  cases hscan :
      bankTrialSuccessFirstGoodReturnPrefix
        ring root S z [] word with
  | none =>
      simp [Prob.indicator, hscan]
  | some found =>
      have hfirst := bankTrialSuccessArmedFirstGoodHeadFirst
        ring root S hlarge hclean
        pre z begun hz hlive hm hcredit word found hscan
      simp [Prob.indicator, hscan, hfirst]

/-- Pure, opaque Nat accounting for the two equal incident masses.
The fourth-stage pending mass contains the after-head remainder. -/
theorem bankTrialSuccessOpaqueFairFirstHead
    (H A G B R Q P X : Nat)
    (hfair : A = H)
    (hhead : H = (G + B) + R)
    (hpend : P = Q + R)
    (hpartition : A + G + B + P = X) :
    2 * H ≤ X := by
  omega

/-- Fairness at a reachable ARMED stage, with the finite no-incident
remainder retained rather than silently discarded. -/
theorem bankTrialSuccessArmedFirstHeadDoubleLeTotal
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (z : BankTrialLocalState q)
    (hreach : z = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hgate : BankTrialProbabilityArmedGate z)
    (T : Nat) :
    2 * bankTrialProbabilityFirstIncidentMass
      root (ring.leftNeighbor root) true T ≤ n ^ T := by
  exact bankTrialSuccessOpaqueFairFirstHead
    (bankTrialProbabilityFirstIncidentMass
      root (ring.leftNeighbor root) true T)
    (bankTrialC5StageMass ring root S z T .tail)
    (bankTrialC5StageMass ring root S z T .good)
    (bankTrialC5StageMass ring root S z T .bad)
    (bankTrialC5PendingAfterMass ring root S z T)
    (bankTrialC5PendingBeforeMass ring root S z T)
    (bankTrialC5StageMass ring root S z T .pending)
    (n ^ T)
    (bankTrialC5StageTailHeadFair ring root S z
      hlarge hclean pre hreach hgate T)
    (bankTrialC5HeadMassSplit ring root S z T)
    (bankTrialC5PendingMassSplit ring root S z T)
    (bankTrialC5FourStageMassPartition ring root S z T)

/-- At every authenticated ARMED cut the extra factor two is paid
by one physical first-outgoing head. This is the local (U) leaf,
without conditional assumptions or an invented independence law. -/
theorem bankTrialSuccessArmedFirstGoodDoubleLeTotal
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (z : BankTrialLocalState q)
    (begun : Bool)
    (hz : z = bankTrialLocalRun ring root pre (bankTrialLocalStart S))
    (hlive : z.phase = .live begun)
    (hm : bankTrialLiveWaveRootMode z.bank = .ARMED)
    (hcredit : begun = false ∨
      0 < bankTrialLiveCarryValue z.bank)
    (T : Nat) :
    2 * Prob.scheduleSum n T (fun word =>
      Prob.indicator
        (bankTrialSuccessFirstGoodReturnPrefix
          ring root S z [] word).isSome) ≤ n ^ T := by
  calc
    2 * Prob.scheduleSum n T (fun word =>
      Prob.indicator
        (bankTrialSuccessFirstGoodReturnPrefix
          ring root S z [] word).isSome) ≤
      2 * bankTrialProbabilityFirstIncidentMass
        root (ring.leftNeighbor root) true T :=
      Nat.mul_le_mul_left 2
        (bankTrialSuccessArmedFirstGoodMassLeHead
          ring root S hlarge hclean pre z begun
          hz hlive hm hcredit T)
    _ ≤ n ^ T :=
      bankTrialSuccessArmedFirstHeadDoubleLeTotal
        ring root S hlarge hclean pre z hz
        ⟨⟨begun, hlive⟩, hm⟩ T

/-- Regardless of the seed mode, any one suffix event is bounded
by the whole physical length-t cylinder. -/
theorem bankTrialSuccessFirstGoodMassLeTotal
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (z : BankTrialLocalState q) (T : Nat) :
    Prob.scheduleSum n T (fun word =>
      Prob.indicator
        (bankTrialSuccessFirstGoodReturnPrefix
          ring root S z [] word).isSome) ≤ n ^ T := by
  calc
    Prob.scheduleSum n T (fun word =>
      Prob.indicator
        (bankTrialSuccessFirstGoodReturnPrefix
          ring root S z [] word).isSome) ≤
      Prob.scheduleSum n T (fun _ => 1) := by
        apply bankTrialProbabilityScheduleSumMono n T
        intro word
        cases h :
            (bankTrialSuccessFirstGoodReturnPrefix
              ring root S z [] word).isSome <;>
          simp [Prob.indicator, h]
    _ = n ^ T := by
      simpa only [Nat.mul_one] using
        (bankTrialProbabilityScheduleSumConst n T 1)

/-- The exact prefix-forward term cannot exceed the corresponding
pre-cut weight times all suffixes.  The credit hypothesis is
obtained from the authenticated cut and the existing physical K1
prefix-certificate proof, not assumed. -/
theorem bankTrialSuccessCutWeightedOneStepLe
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (cut : List (Fin n)) (j t : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S cut j = some cut) :
    (2 ^ bankTrialSuccessCutHistoryArmedCount
      ring root S cut j *
      (if BankTrialProbabilityArmedGate
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)) then 2 else 1) *
      Prob.scheduleSum n t (fun suffix =>
        Prob.indicator
          (bankTrialSuccessFirstGoodReturnPrefix ring root S
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) [] suffix).isSome)) ≤
    2 ^ bankTrialSuccessCutHistoryArmedCount
      ring root S cut j * n ^ t := by
  by_cases hg : BankTrialProbabilityArmedGate
      (bankTrialLocalRun ring root cut (bankTrialLocalStart S))
  · obtain ⟨begun, hlive, hcredit⟩ :=
      bankTrialSuccessArmedGoodCutCredit
        ring root S hsp hlarge hwidth hclean
        cut cut j
        (bankTrialLocalRun ring root cut (bankTrialLocalStart S))
        rfl hcut hg
    have hdouble :=
      bankTrialSuccessArmedFirstGoodDoubleLeTotal
        ring root S hlarge hclean cut
        (bankTrialLocalRun ring root cut (bankTrialLocalStart S))
        begun rfl hlive hg.2 hcredit t
    have hscaled :=
      Nat.mul_le_mul_left
        (2 ^ bankTrialSuccessCutHistoryArmedCount
          ring root S cut j) hdouble
    rw [if_pos hg]
    simpa only [Nat.mul_assoc] using hscaled
  · have hsingle :=
      bankTrialSuccessFirstGoodMassLeTotal
        ring root S
        (bankTrialLocalRun ring root cut (bankTrialLocalStart S)) t
    have hscaled :=
      Nat.mul_le_mul_left
        (2 ^ bankTrialSuccessCutHistoryArmedCount
          ring root S cut j) hsingle
    rw [if_neg hg]
    simpa only [Nat.mul_one] using hscaled

/-- Finite map-sum monotonicity, no Finset or Batteries. -/
theorem bankTrialSuccessMapSumMonotone
    {A : Type} (xs : List A) (f g : A → Nat)
    (h : ∀ x, x ∈ xs → f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil =>
      exact Nat.le_refl _
  | cons x xs ih =>
      have hx : f x ≤ g x := h x (by simp)
      have hrest : ∀ y, y ∈ xs → f y ≤ g y := by
        intro y hy
        exact h y (by simp [hy])
      have hsum := Nat.add_le_add hx (ih hrest)
      simpa only [List.map_cons, List.sum_cons] using hsum

/-- (U) Head-conditioned weighted-mass monotonicity. It uses
the ACTUAL j-th first-stopped-prefix decomposition on the
same finite scheduler tape and a fair first-incident cylinder
on each authenticated ARMED cut. -/
theorem bankTrialSuccessWeightedMassNextLeCurrent
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (j T : Nat) :
    bankTrialSuccessCutHistoryWeightedMass ring root S
      (j + 1) T ≤
    bankTrialSuccessCutHistoryWeightedMass ring root S j T := by
  rw [bankTrialSuccessCutHistoryWeightedNextFactorization
      ring root S j T,
    bankTrialSuccessCutHistoryWeightedMassFactorization
      ring root S j T]
  unfold bankTrialSuccessCutHistoryPrefixForward
    bankTrialSuccessCutHistoryPrefixMass
  apply bankTrialSuccessMapSumMonotone
  intro cut hmem
  exact bankTrialSuccessCutWeightedOneStepLe
    ring root S hsp hlarge hwidth hclean
    cut j (T - cut.length)
    (bankTrialSuccessStoppedGoodCutAuthenticated
      ring root S j T cut hmem)

/-- Consequence of (U), sharper than the crude K1 bound:
the weight in any chronological stage is at most one full
original physical scheduler cylinder, uniformly in j. -/
theorem bankTrialSuccessWeightedMassLeTotalOfFair
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (T : Nat) :
    ∀ j : Nat,
      bankTrialSuccessCutHistoryWeightedMass
        ring root S j T ≤ n ^ T := by
  intro j
  induction j with
  | zero =>
      rw [bankTrialSuccessCutHistoryWeightedMassZero]
      exact Nat.le_refl _
  | succ j ih =>
      exact Nat.le_trans
        (bankTrialSuccessWeightedMassNextLeCurrent
          ring root S hsp hlarge hwidth hclean j T) ih

/-- A WON good cut is absorbing: the actual complete scheduler
word ends in WON, even if its first WON cut occurred earlier. -/
theorem bankTrialSuccessWonGoodCutFullWordWon
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word cut : List (Fin n)) (j : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word j = some cut)
    (hwon :
      (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S)).phase = .won) :
    (bankTrialLocalRun ring root word
      (bankTrialLocalStart S)).phase = .won := by
  obtain ⟨suffix, hword⟩ :=
    bankTrialSuccessGoodReturnCutIsPrefix
      ring root S word j cut hcut
  rw [hword, bankTrialLocalRunAppend]
  rw [bankTrialLocalRunTerminalAbsorbs
    ring root suffix
    (bankTrialLocalRun ring root cut (bankTrialLocalStart S))
    (Or.inl hwon)]
  exact hwon

/-- Consequently the same WON-cut word has no OLD ARMED incoming
incident. This is the entire unconditional portion of the
head-event certificate already available from the G11 rows. -/
theorem bankTrialSuccessWonGoodCutNoArmedIncoming
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (word cut : List (Fin n)) (j : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word j = some cut)
    (hwon :
      (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S)).phase = .won) :
    BankTrialNoArmedIncoming ring root word
      (bankTrialLocalStart S) := by
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hn : 2 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    omega
  exact bankTrialProbabilityCleanWinNoArmedIncoming
    ring root hn S hclean word
    (bankTrialSuccessWonGoodCutFullWordWon
      ring root S word cut j hcut hwon)

/-!
(W) REMAINS OPEN / concrete proof obstruction.

For a WON good-cut prefix we have proved its full-word terminal
alternative and the full-word NoArmedIncoming predicate, but
CompletedHeadWord also requires

    bankTrialProbabilityHeadEvent ring root word
      (compileAdvice q).K (bankTrialLocalStart S).

By bankTrialHeadEventOfCount this would follow from the distinct
numeric provenance fact

    (compileAdvice q).K ≤
      bankTrialLiveHeadCount ring root word
        (bankTrialLocalStart S).

The BankTrialC5CompletedHeadInvariant has only LIVE-state
carry and strict-ARMED head-count properties. These hypotheses
are vacuous at the WON endpoint. Its proved soundness theorem goes
in the opposite direction: CompletedHeadWord -> WON. The missing
reverse numeric provenance for WON is precisely the head-count
component of BankTrialLiveWinningLedger (BankTrialProbability.lean,
around line 1547); it is not supplied by K1 or by the actual C5
worker-start cap. Thus no completed-head cylinder bound for WON
debt, and no hforward or mass-lower corollary, is claimed here.

Even if (U) proves W_i <= n^T, the exact rarity contribution in
PrefixDebt is 2*N*W_i, giving 2*N*n^T PER STAGE, whereas the
requested hforward has N*n^T per stage. One still needs a
head-conditioned rarity argument with the factor-two reduction,
not ordinary weighted-mass monotonicity alone.
-/

end L3

#print axioms L3.bankTrialSuccessArmedFirstGoodHeadFirst
#print axioms L3.bankTrialSuccessArmedFirstGoodMassLeHead
#print axioms L3.bankTrialSuccessOpaqueFairFirstHead
#print axioms L3.bankTrialSuccessArmedFirstHeadDoubleLeTotal
#print axioms L3.bankTrialSuccessArmedFirstGoodDoubleLeTotal
#print axioms L3.bankTrialSuccessFirstGoodMassLeTotal
#print axioms L3.bankTrialSuccessCutWeightedOneStepLe
#print axioms L3.bankTrialSuccessMapSumMonotone
#print axioms L3.bankTrialSuccessWeightedMassNextLeCurrent
#print axioms L3.bankTrialSuccessWeightedMassLeTotalOfFair
#print axioms L3.bankTrialSuccessWonGoodCutFullWordWon
#print axioms L3.bankTrialSuccessWonGoodCutNoArmedIncoming

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
Actual CLEAN-start winning-head provenance and the
finite stopped-prefix terminal accounting.
-/

/-- The existing unconditional G11 comparison genealogy and
carry ledger imply K physically paid heads on EVERY genuine
CLEAN-start winning word.  No forged LIVE snapshot is used. -/
theorem bankTrialSuccessCleanWinningHeadCountLower
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (word : List (Fin n))
    (hwon : (bankTrialLocalRun ring root word
      (bankTrialLocalStart S)).phase = .won) :
    (compileAdvice q).K ≤
      bankTrialLiveHeadCount ring root word
        (bankTrialLocalStart S) := by
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hn : 2 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    omega
  have hq : 3 ≤ q := by
    have hs : (compileAdvice q).useSmall =
      decide (q ≤ qStar) := rfl
    rw [hs] at hsp
    have hnot : ¬ q ≤ qStar := of_decide_eq_false hsp
    change ¬ q ≤ 79 at hnot
    omega
  have htheta :
      (compileAdvice q).K ≤ bankTrialLiveThetaBinary q := by
    rw [bankTrialProbabilityThetaBinaryEqualsK q hq]
    exact Nat.le_refl _
  obtain ⟨pre, suffix, B, begun, hword, hpre, hm, ht⟩ :=
    bankTrialProbabilityCleanWinGuardTrace
      ring root hn S hclean word hwon
  have hcredit := bankTrialProbabilityCleanWordsComparatorCredit
    ring root hw S hclean htheta pre
  rw [hpre] at hcredit
  have hcarry := bankTrialProbabilityLockedCarryCleanWords
    ring root hw S hclean pre
  rw [hpre] at hcarry
  have hk :
      (compileAdvice q).K ≤
        bankTrialLiveHeadCount ring root pre
          (bankTrialLocalStart S) :=
    Nat.le_trans (hcredit begun rfl hm ht) (hcarry begun rfl)
  have hmono :
      bankTrialLiveHeadCount ring root pre
        (bankTrialLocalStart S) ≤
      bankTrialLiveHeadCount ring root word
        (bankTrialLocalStart S) := by
    rw [hword, bankTrialLiveHeadCountAppend]
    omega
  exact Nat.le_trans hk hmono

/-- The gated K-HEAD recursive event follows from the actual
winning trace: counted heads plus no LIVE/ARMED incoming port. -/
theorem bankTrialSuccessCleanWinningHeadEvent
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (word : List (Fin n))
    (hwon : (bankTrialLocalRun ring root word
      (bankTrialLocalStart S)).phase = .won) :
    bankTrialProbabilityHeadEvent ring root word
      (compileAdvice q).K (bankTrialLocalStart S) := by
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hn : 2 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    omega
  exact bankTrialHeadEventOfCount ring root word
    (compileAdvice q).K (bankTrialLocalStart S)
    (bankTrialProbabilityCleanWinNoArmedIncoming
      ring root hn S hclean word hwon)
    (bankTrialSuccessCleanWinningHeadCountLower
      ring root S hsp hlarge hclean word hwon)

/-- (W), for ALL original-clock words: an authenticated GOOD
prefix in WON entails the literal CompletedHeadWord predicate.
This is stronger than a statement about the stopped prefix alone. -/
theorem bankTrialSuccessWonGoodCutCompletedHeadWord
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (word cut : List (Fin n)) (j : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word j = some cut)
    (hwon : (bankTrialLocalRun ring root cut
      (bankTrialLocalStart S)).phase = .won) :
    bankTrialProbabilityC5CompletedHeadWord ring root S word := by
  have hfull := bankTrialSuccessWonGoodCutFullWordWon
    ring root S word cut j hcut hwon
  change
    bankTrialProbabilityHeadEvent ring root word
        (compileAdvice q).K (bankTrialLocalStart S) ∧
      ((bankTrialLocalRun ring root word
        (bankTrialLocalStart S)).phase = .won ∨
       ∃ begun : Bool,
        (bankTrialLocalRun ring root word
          (bankTrialLocalStart S)).phase = .live begun ∧
        bankTrialLiveWaveRootMode
          (bankTrialLocalRun ring root word
            (bankTrialLocalStart S)).bank = .ARMED)
  exact ⟨bankTrialSuccessCleanWinningHeadEvent
      ring root S hsp hlarge hclean word hfull, Or.inl hfull⟩

/-- An actual WON good-cut index is the UNIQUE last-good ordinal
on that word, because the next good cut cannot exist. -/
theorem bankTrialSuccessWonCutIndexIsOrdinal
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word : List (Fin n)) (j : Nat)
    (hwon : bankTrialSuccessCutWonWordMass
      ring root S word j = 1) :
    bankTrialSuccessGoodReturnOrdinal ring root S word = j := by
  cases hcut :
      bankTrialSuccessGoodReturnCutPrefix ring root S word j with
  | none =>
      simp only [bankTrialSuccessCutWonWordMass, hcut] at hwon
      cases hwon
  | some cut =>
      by_cases hw :
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)).phase = .won
      · exact bankTrialSuccessOrdinalOfAdjacentCuts
          ring root S word cut j hcut
          (bankTrialSuccessWonGoodCutNextNone
            ring root S word cut j hcut hw)
      · simp only [bankTrialSuccessCutWonWordMass, hcut,
          if_neg hw] at hwon
        cases hwon

/-- Per-word WON charge: only its unique good-return ordinal
can be charged, and K1 caps its preceding history multiplier. -/
theorem bankTrialSuccessWonWordWeightLeCompletion
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (word : List (Fin n)) (j : Nat) :
    bankTrialSuccessCutWonWordMass ring root S word j *
      2 ^ bankTrialSuccessCutHistoryArmedCount
        ring root S word j ≤
      (if j = bankTrialSuccessGoodReturnOrdinal
          ring root S word then
        2 ^ (compileAdvice q).K *
          (if bankTrialProbabilityC5CompletedHeadWord
            ring root S word then 1 else 0)
       else 0) := by
  cases hcut :
      bankTrialSuccessGoodReturnCutPrefix ring root S word j with
  | none =>
      simp only [bankTrialSuccessCutWonWordMass,
        hcut, Nat.zero_mul]
      exact Nat.zero_le _
  | some cut =>
      by_cases hwon :
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)).phase = .won
      · have hindex :
            j = bankTrialSuccessGoodReturnOrdinal
              ring root S word :=
          (bankTrialSuccessWonCutIndexIsOrdinal
            ring root S word j
            (by simp only [bankTrialSuccessCutWonWordMass,
              hcut, if_pos hwon])).symm
        have hcompleted :=
          bankTrialSuccessWonGoodCutCompletedHeadWord
            ring root S hsp hlarge hclean word cut j hcut hwon
        have hcount :=
          bankTrialSuccessEveryGoodCutArmedCap
            ring root S hsp hlarge hwidth hclean
            word cut j hcut
        have hpower := bankTrialSuccessTwoPowerMonotone
          (bankTrialSuccessCutHistoryArmedCount
            ring root S word j)
          (compileAdvice q).K hcount
        simpa only [bankTrialSuccessCutWonWordMass,
          hcut, if_pos hwon, Nat.one_mul,
          if_pos hindex, if_pos hcompleted, Nat.mul_one]
          using hpower
      · simp only [bankTrialSuccessCutWonWordMass, hcut,
          if_neg hwon, Nat.zero_mul]
        exact Nat.zero_le _

/-- Core Nat, one nonzero ordinal can be charged only once.
No Finset or large-number evaluation. -/
theorem bankTrialSuccessStageIndexSingleChargeCap
    (ordinal c : Nat) :
    ∀ J : Nat,
      bankTrialSuccessStageIndexSum
        (fun i => if i = ordinal then c else 0) J ≤ c := by
  intro J
  induction J with
  | zero =>
      exact Nat.zero_le _
  | succ k ih =>
      change
        bankTrialSuccessStageIndexSum
          (fun i => if i = ordinal then c else 0) k +
          (if k = ordinal then c else 0) ≤ c
      by_cases he : k = ordinal
      · have hzero :
            bankTrialSuccessStageIndexSum
              (fun i => if i = ordinal then c else 0) k = 0 := by
          calc
            _ = bankTrialSuccessStageIndexSum
                (fun _ => 0) k :=
              bankTrialSuccessCutHistorySumExt
                (fun i => if i = ordinal then c else 0)
                (fun _ => 0) k
                (fun i hi => by rw [if_neg (by omega)])
            _ = 0 := bankTrialSuccessStageIndexSumZero k
        rw [hzero, if_pos he, Nat.zero_add]
        exact Nat.le_refl _
      · rw [if_neg he, Nat.add_zero]
        exact ih

/-- ALL WON good-cut word charges across an arbitrary range
are bounded by one completed-head word with multiplier 2^K. -/
theorem bankTrialSuccessWonWordAllCutsBound
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (word : List (Fin n)) (J : Nat) :
    bankTrialSuccessStageIndexSum (fun j =>
      bankTrialSuccessCutWonWordMass ring root S word j *
        2 ^ bankTrialSuccessCutHistoryArmedCount
          ring root S word j) J ≤
      2 ^ (compileAdvice q).K *
        (if bankTrialProbabilityC5CompletedHeadWord
          ring root S word then 1 else 0) := by
  exact Nat.le_trans
    (bankTrialSuccessStageIndexSumMono
      (fun j =>
        bankTrialSuccessCutWonWordMass ring root S word j *
          2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S word j)
      (fun j => if j = bankTrialSuccessGoodReturnOrdinal
        ring root S word then
        2 ^ (compileAdvice q).K *
          (if bankTrialProbabilityC5CompletedHeadWord
            ring root S word then 1 else 0)
        else 0)
      (fun j =>
        bankTrialSuccessWonWordWeightLeCompletion
          ring root S hsp hlarge hwidth hclean word j) J)
    (bankTrialSuccessStageIndexSingleChargeCap
      (bankTrialSuccessGoodReturnOrdinal ring root S word)
      (2 ^ (compileAdvice q).K *
        (if bankTrialProbabilityC5CompletedHeadWord
          ring root S word then 1 else 0)) J)

/-- The original-n-edge horizon mass of all disjoint WON-cut
charges. No probability independence is used. -/
theorem bankTrialSuccessWonWordAllCutsMassBound
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (J T : Nat) :
    bankTrialSuccessStageIndexSum (fun j =>
      Prob.scheduleSum n T (fun word =>
        bankTrialSuccessCutWonWordMass ring root S word j *
          2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S word j)) J ≤
      2 ^ (compileAdvice q).K *
        bankTrialProbabilityC5CompletedHeadMass
          ring root S T := by
  rw [bankTrialSuccessStageIndexSumSchedule]
  calc
    Prob.scheduleSum n T (fun word =>
        bankTrialSuccessStageIndexSum (fun j =>
          bankTrialSuccessCutWonWordMass ring root S word j *
            2 ^ bankTrialSuccessCutHistoryArmedCount
              ring root S word j) J) ≤
      Prob.scheduleSum n T (fun word =>
        2 ^ (compileAdvice q).K *
          (if bankTrialProbabilityC5CompletedHeadWord
            ring root S word then 1 else 0)) := by
      apply bankTrialProbabilityScheduleSumMono n T
      intro word
      exact bankTrialSuccessWonWordAllCutsBound
        ring root S hsp hlarge hwidth hclean word J
    _ = 2 ^ (compileAdvice q).K *
          bankTrialProbabilityC5CompletedHeadMass
            ring root S T := by
      unfold bankTrialProbabilityC5CompletedHeadMass
      exact bankTrialSuccessScheduleSumScale n T
        (2 ^ (compileAdvice q).K)
        (fun word =>
          if bankTrialProbabilityC5CompletedHeadWord
            ring root S word then 1 else 0)

/-- Isolate the exact stop-prefix terminal portion of PrefixDebt,
without the common worker denominator. -/
noncomputable def bankTrialSuccessWonPrefixHistoryMass
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j T : Nat) : Nat :=
  ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
    (bankTrialSuccessGoodReturnCutBool ring root S j)
    T [] (bankTrialLocalStart S)).map (fun cut =>
      2 ^ bankTrialSuccessCutHistoryArmedCount
        ring root S cut j *
      bankTrialSuccessCutWonAt n
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)) (T - cut.length))).sum

/-- A Nat first-stop scanner reports exactly the WON-cut
indicator times the PRE-CUT path weight on the SAME full word. -/
theorem bankTrialSuccessWonNatStoppedWordExact
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j T : Nat) (word : List (Fin n)) :
    bankTrialSuccessNatStoppedWord
      (bankTrialLocalNext ring root)
      (bankTrialSuccessGoodReturnCutBool ring root S j)
      (fun pre z _ _ =>
        2 ^ bankTrialSuccessCutHistoryArmedCount
          ring root S pre j *
        (if z.phase = .won then 1 else 0))
      T [] (bankTrialLocalStart S) word =
    bankTrialSuccessCutWonWordMass ring root S word j *
      2 ^ bankTrialSuccessCutHistoryArmedCount
        ring root S word j := by
  cases hcut :
      bankTrialSuccessGoodReturnCutPrefix ring root S word j with
  | none =>
      have hnone := bankTrialSuccessCutHistoryNatNone
        ring root S
        (fun pre z _ =>
          2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S pre j *
          (if z.phase = .won then 1 else 0))
        j word [] (bankTrialLocalStart S) T rfl
        (by simpa only [List.nil_append] using hcut)
      simpa only [bankTrialSuccessCutWonWordMass,
        hcut, Nat.zero_mul] using hnone
  | some cut =>
      have hsome := bankTrialSuccessCutHistoryNatOfGoodCut
        ring root S
        (fun pre z _ =>
          2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S pre j *
          (if z.phase = .won then 1 else 0))
        word cut j T hcut
      have hcount := bankTrialSuccessCutHistoryCountAtCut
        ring root S word cut j hcut
      by_cases hw :
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)).phase = .won
      · simpa only [bankTrialSuccessCutWonWordMass,
          hcut, if_pos hw, Nat.mul_one, Nat.one_mul,
          hcount] using hsome
      · simpa only [bankTrialSuccessCutWonWordMass,
          hcut, if_neg hw, Nat.mul_zero, Nat.zero_mul]
          using hsome

/-- The terminal stop-prefix cylinders equal the exact-length-T
full-word WON-cut charge.  This is the same Nat-valued stopped
prefix factorization previously used for W_j. -/
theorem bankTrialSuccessWonPrefixHistoryFactorization
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j T : Nat) :
    bankTrialSuccessWonPrefixHistoryMass ring root S j T =
      Prob.scheduleSum n T (fun word =>
        bankTrialSuccessCutWonWordMass ring root S word j *
          2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S word j) := by
  unfold bankTrialSuccessWonPrefixHistoryMass
  calc
    ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        T [] (bankTrialLocalStart S)).map (fun cut =>
        2 ^ bankTrialSuccessCutHistoryArmedCount
          ring root S cut j *
        bankTrialSuccessCutWonAt n
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) (T - cut.length))).sum =
      ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        T [] (bankTrialLocalStart S)).map (fun cut =>
        Prob.scheduleSum n (T - cut.length) (fun _ =>
          2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S cut j *
          (if (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)).phase = .won then 1 else 0)))).sum := by
      apply bankTrialSuccessCutHistoryMapSumExt
      intro cut
      rw [bankTrialProbabilityScheduleSumConst]
      by_cases hw :
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)).phase = .won
      · simp only [bankTrialSuccessCutWonAt,
          if_pos hw, Nat.mul_one]
        exact Nat.mul_comm _ _
      · simp only [bankTrialSuccessCutWonAt,
          if_neg hw, Nat.mul_zero]
    _ = Prob.scheduleSum n T (fun word =>
        bankTrialSuccessNatStoppedWord
          (bankTrialLocalNext ring root)
          (bankTrialSuccessGoodReturnCutBool ring root S j)
          (fun pre z _ _ =>
            2 ^ bankTrialSuccessCutHistoryArmedCount
              ring root S pre j *
            (if z.phase = .won then 1 else 0))
          T [] (bankTrialLocalStart S) word) :=
      (bankTrialSuccessNatStoppedFactorizationLocal
        ring root
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        (fun pre z _ _ =>
          2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S pre j *
          (if z.phase = .won then 1 else 0))
        (bankTrialLocalStart S) T).symm
    _ = Prob.scheduleSum n T (fun word =>
        bankTrialSuccessCutWonWordMass ring root S word j *
          2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S word j) := by
      apply congrArg (Prob.scheduleSum n T)
      funext word
      exact bankTrialSuccessWonNatStoppedWordExact
        ring root S j T word

/-- The terminal WON component, summed over ALL cut stages,
is paid just ONCE by 2^K times the completed-head mass. -/
theorem bankTrialSuccessWonPrefixHistoryBudget
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (J T : Nat) :
    bankTrialSuccessStageIndexSum (fun j =>
      bankTrialSuccessWonPrefixHistoryMass
        ring root S j T) J ≤
      2 ^ (compileAdvice q).K *
        bankTrialProbabilityC5CompletedHeadMass
          ring root S T := by
  have heq :
      (fun j => bankTrialSuccessWonPrefixHistoryMass
        ring root S j T) =
      (fun j => Prob.scheduleSum n T (fun word =>
        bankTrialSuccessCutWonWordMass ring root S word j *
          2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S word j)) := by
    funext j
    exact bankTrialSuccessWonPrefixHistoryFactorization
      ring root S j T
  rw [heq]
  exact bankTrialSuccessWonWordAllCutsMassBound
    ring root S hsp hlarge hwidth hclean J T

/-- The other two exact components of the old prefix debt:
pre-cut weighted pending and per-stage rarity. -/
noncomputable def bankTrialSuccessPendingPrefixHistoryMass
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j T : Nat) : Nat :=
  ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
    (bankTrialSuccessGoodReturnCutBool ring root S j)
    T [] (bankTrialLocalStart S)).map (fun cut =>
      2 ^ bankTrialSuccessCutHistoryArmedCount
        ring root S cut j *
      bankTrialSuccessCutPenaltyAt ring root S
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)) (T - cut.length))).sum

/-- A literal finite-list triple additivity lemma, core Nat only. -/
theorem bankTrialSuccessMapSumTriple
    {A : Type} (xs : List A) (f g h : A → Nat) :
    (xs.map (fun x => f x + g x + h x)).sum =
      (xs.map f).sum + (xs.map g).sum +
        (xs.map h).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Exact (a)+(b)+(c) debt identity, with no estimate hidden:
rarity = 2*N*W_j, pending remains a stopped-prefix mass,
and WON is a D-scaled stopped-prefix mass. -/
theorem bankTrialSuccessPrefixDebtComponents
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j T : Nat) :
    bankTrialSuccessCutHistoryPrefixDebt ring root S j T =
      2 * bankTrialProbabilityC5WorkerNumerator q *
        bankTrialSuccessCutHistoryWeightedMass ring root S j T +
      bankTrialSuccessPendingPrefixHistoryMass ring root S j T +
      bankTrialProbabilityC5WorkerDenominator q *
        bankTrialSuccessWonPrefixHistoryMass ring root S j T := by
  have hsplit := bankTrialSuccessMapSumTriple
    (Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
      (bankTrialSuccessGoodReturnCutBool ring root S j)
      T [] (bankTrialLocalStart S))
    (fun cut =>
      2 * bankTrialProbabilityC5WorkerNumerator q *
        (2 ^ bankTrialSuccessCutHistoryArmedCount
          ring root S cut j * n ^ (T - cut.length)))
    (fun cut =>
      2 ^ bankTrialSuccessCutHistoryArmedCount
        ring root S cut j *
      bankTrialSuccessCutPenaltyAt ring root S
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)) (T - cut.length))
    (fun cut =>
      bankTrialProbabilityC5WorkerDenominator q *
        (2 ^ bankTrialSuccessCutHistoryArmedCount
          ring root S cut j *
          bankTrialSuccessCutWonAt n
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) (T - cut.length)))
  rw [bankTrialSuccessRarityDebtExact ring root S j T,
    bankTrialSuccessListMapScale] at hsplit
  simpa only [bankTrialSuccessCutHistoryPrefixDebt,
    bankTrialSuccessPendingPrefixHistoryMass,
    bankTrialSuccessWonPrefixHistoryMass] using hsplit

/-- Core indexed-sum triple additivity, no Finset. -/
theorem bankTrialSuccessStageIndexSumTriple
    (f g h : Nat → Nat) :
    ∀ J : Nat,
      bankTrialSuccessStageIndexSum
        (fun j => f j + g j + h j) J =
        bankTrialSuccessStageIndexSum f J +
        bankTrialSuccessStageIndexSum g J +
        bankTrialSuccessStageIndexSum h J := by
  intro J
  induction J with
  | zero => rfl
  | succ j ih =>
      change
        bankTrialSuccessStageIndexSum
          (fun i => f i + g i + h i) j +
          (f j + g j + h j) =
        (bankTrialSuccessStageIndexSum f j + f j) +
        (bankTrialSuccessStageIndexSum g j + g j) +
        (bankTrialSuccessStageIndexSum h j + h j)
      rw [ih]
      simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Core indexed-sum scaling. -/
theorem bankTrialSuccessStageIndexSumScale
    (c : Nat) (f : Nat → Nat) :
    ∀ J : Nat,
      bankTrialSuccessStageIndexSum
        (fun j => c * f j) J =
        c * bankTrialSuccessStageIndexSum f J := by
  intro J
  induction J with
  | zero => rfl
  | succ j ih =>
      change
        bankTrialSuccessStageIndexSum
          (fun i => c * f i) j + c * f j =
        c * (bankTrialSuccessStageIndexSum f j + f j)
      rw [ih, Nat.mul_add]

/-- Core indexed-sum constant formula. -/
theorem bankTrialSuccessStageIndexSumConstant
    (c : Nat) :
    ∀ J : Nat,
      bankTrialSuccessStageIndexSum (fun _ => c) J =
        J * c := by
  intro J
  induction J with
  | zero => exact (Nat.zero_mul c).symm
  | succ j ih =>
      change
        bankTrialSuccessStageIndexSum (fun _ => c) j + c =
          (j + 1) * c
      rw [ih, Nat.add_mul, Nat.one_mul]

/-- The sum of all rarity parts is bounded using (U).  Exactly
2*N per cut appears: (U) does not erase the leading 2. -/
theorem bankTrialSuccessRarityAllCutsByFair
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (J T : Nat) :
    bankTrialSuccessStageIndexSum (fun j =>
      2 * bankTrialProbabilityC5WorkerNumerator q *
        bankTrialSuccessCutHistoryWeightedMass
          ring root S j T) J ≤
      (J * (2 * bankTrialProbabilityC5WorkerNumerator q)) *
        n ^ T := by
  calc
    bankTrialSuccessStageIndexSum (fun j =>
        2 * bankTrialProbabilityC5WorkerNumerator q *
          bankTrialSuccessCutHistoryWeightedMass
            ring root S j T) J ≤
      bankTrialSuccessStageIndexSum (fun _ =>
        2 * bankTrialProbabilityC5WorkerNumerator q *
          n ^ T) J :=
      bankTrialSuccessStageIndexSumMono _ _
        (fun j => Nat.mul_le_mul_left _
          (bankTrialSuccessWeightedMassLeTotalOfFair
            ring root S hsp hlarge hwidth hclean T j)) J
    _ = (J * (2 * bankTrialProbabilityC5WorkerNumerator q)) *
          n ^ T := by
      rw [bankTrialSuccessStageIndexSumConstant]
      simp only [Nat.mul_assoc]

/-- The complete finite sum of the exact prefix debts, with
rarity paid via U and WON paid via W. Only the RAW pending sum
remains unbounded by the global Markov term. -/
theorem bankTrialSuccessAllCutsDebtBound
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (J T : Nat) :
    bankTrialSuccessStageIndexSum
      (fun j => bankTrialSuccessCutHistoryPrefixDebt
        ring root S j T) J ≤
      ((J * (2 * bankTrialProbabilityC5WorkerNumerator q)) *
        n ^ T +
       bankTrialSuccessStageIndexSum
         (fun j => bankTrialSuccessPendingPrefixHistoryMass
           ring root S j T) J) +
       bankTrialProbabilityC5WorkerDenominator q *
         (2 ^ (compileAdvice q).K *
           bankTrialProbabilityC5CompletedHeadMass
             ring root S T) := by
  have hfun :
      (fun j => bankTrialSuccessCutHistoryPrefixDebt
        ring root S j T) =
      (fun j =>
        2 * bankTrialProbabilityC5WorkerNumerator q *
          bankTrialSuccessCutHistoryWeightedMass
            ring root S j T +
        bankTrialSuccessPendingPrefixHistoryMass ring root S j T +
        bankTrialProbabilityC5WorkerDenominator q *
          bankTrialSuccessWonPrefixHistoryMass
            ring root S j T) := by
    funext j
    exact bankTrialSuccessPrefixDebtComponents
      ring root S j T
  rw [hfun, bankTrialSuccessStageIndexSumTriple]
  exact Nat.add_le_add
    (Nat.add_le_add
      (bankTrialSuccessRarityAllCutsByFair
        ring root S hsp hlarge hwidth hclean J T)
      (Nat.le_refl _))
    (by
      rw [bankTrialSuccessStageIndexSumScale]
      exact Nat.mul_le_mul_left _
        (bankTrialSuccessWonPrefixHistoryBudget
          ring root S hsp hlarge hwidth hclean J T))

/-- Unconditional FORWARD estimate with the actual coefficients.
The remainder is the explicit weighted pending stopped-prefix sum;
the advertised hforward has a smaller rarity coefficient and no
such raw remainder. No conditional or assumed leaf occurs here. -/
theorem bankTrialSuccessForwardWithRawPending
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (J T : Nat) :
    bankTrialProbabilityC5WorkerDenominator q *
      T * n ^ T ≤
      bankTrialProbabilityC5WorkerDenominator q *
        T * (2 ^ (compileAdvice q).K *
          bankTrialSuccessCutReachMass ring root S J T) +
      T * (((J * (2 * bankTrialProbabilityC5WorkerNumerator q)) *
          n ^ T +
        bankTrialSuccessStageIndexSum
          (fun j => bankTrialSuccessPendingPrefixHistoryMass
            ring root S j T) J) +
        bankTrialProbabilityC5WorkerDenominator q *
          (2 ^ (compileAdvice q).K *
            bankTrialProbabilityC5CompletedHeadMass
              ring root S T)) := by
  have hforward := bankTrialSuccessForwardCutReachWithExactDebt
    ring root S hsp hlarge hwidth hclean J T
  have hdebt := bankTrialSuccessAllCutsDebtBound
    ring root S hsp hlarge hwidth hclean J T
  exact Nat.le_trans hforward
    (Nat.add_le_add_left
      (Nat.mul_le_mul_left T hdebt)
      (bankTrialProbabilityC5WorkerDenominator q *
        T * (2 ^ (compileAdvice q).K *
          bankTrialSuccessCutReachMass ring root S J T)))

/-- The requested fixed start-cap index j=2K+1.  The rarity
coefficient here is 2*(2K+1)*N, versus the old hforward
coefficient (2K+1)*N. -/
theorem bankTrialSuccessForwardAtStartCapWithRawPending
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (T : Nat) :
    bankTrialProbabilityC5WorkerDenominator q *
      T * n ^ T ≤
      bankTrialProbabilityC5WorkerDenominator q *
        T * (2 ^ (compileAdvice q).K *
          bankTrialSuccessCutReachMass ring root S
            (2 * (compileAdvice q).K + 1) T) +
      T * (((2 * (compileAdvice q).K + 1) *
          (2 * bankTrialProbabilityC5WorkerNumerator q) *
          n ^ T +
        bankTrialSuccessStageIndexSum
          (fun j => bankTrialSuccessPendingPrefixHistoryMass
            ring root S j T)
          (2 * (compileAdvice q).K + 1)) +
        bankTrialProbabilityC5WorkerDenominator q *
          (2 ^ (compileAdvice q).K *
            bankTrialProbabilityC5CompletedHeadMass
              ring root S T)) := by
  exact bankTrialSuccessForwardWithRawPending
    ring root S hsp hlarge hwidth hclean
    (2 * (compileAdvice q).K + 1) T

/-!
The genuine (W) leaf is now closed by
bankTrialSuccessWonGoodCutCompletedHeadWord.

The terminal WON contribution has additionally been transferred
ONCE, not once per stage, in
bankTrialSuccessWonPrefixHistoryBudget. This uses a unique
last-good ordinal and Nat first-stop factorization on one
original n-edge scheduler tape.

The hforward target is NOT asserted. The exact difference from the
displayed C5Rows.lean hforward is:
  * rarity: 2*(2K+1)*N here versus (2K+1)*N there;
  * the raw weighted pending sum still needs an unconditional
    final-horizon ordinal/Markov bound;
  * the surviving reach mass at j=2K+1 still needs to be
    identified with completed-head mass (or shown empty).
Our valid forward statement also keeps the terminal completed
mass as an additive term, and does not pretend it equals the
surviving j-th cut mass. No unsound cancellation was performed.

No missing statement has been installed as an axiom or hypothesis.
-/

end L3

#print axioms L3.bankTrialSuccessCleanWinningHeadCountLower
#print axioms L3.bankTrialSuccessCleanWinningHeadEvent
#print axioms L3.bankTrialSuccessWonGoodCutCompletedHeadWord
#print axioms L3.bankTrialSuccessWonCutIndexIsOrdinal
#print axioms L3.bankTrialSuccessWonWordWeightLeCompletion
#print axioms L3.bankTrialSuccessStageIndexSingleChargeCap
#print axioms L3.bankTrialSuccessWonWordAllCutsBound
#print axioms L3.bankTrialSuccessWonWordAllCutsMassBound
#print axioms L3.bankTrialSuccessWonNatStoppedWordExact
#print axioms L3.bankTrialSuccessWonPrefixHistoryFactorization
#print axioms L3.bankTrialSuccessWonPrefixHistoryBudget
#print axioms L3.bankTrialSuccessMapSumTriple
#print axioms L3.bankTrialSuccessPrefixDebtComponents
#print axioms L3.bankTrialSuccessStageIndexSumTriple
#print axioms L3.bankTrialSuccessStageIndexSumScale
#print axioms L3.bankTrialSuccessStageIndexSumConstant
#print axioms L3.bankTrialSuccessRarityAllCutsByFair
#print axioms L3.bankTrialSuccessAllCutsDebtBound
#print axioms L3.bankTrialSuccessForwardWithRawPending
#print axioms L3.bankTrialSuccessForwardAtStartCapWithRawPending

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-! Doubled C.1 margin, saturated cut, coarse C.6, horizon. -/

/-- Arithmetic on opaque Nats; the enormous base powers never
enter omega. -/
private theorem bankTrialSuccessStrictOfSuccBound
    (a b : Nat) (h : a + 1 ≤ b) : a < b := by
  omega

private theorem bankTrialSuccessOpaqueDoubleCount
    (k r : Nat) (hk : k < r) :
    2 * k + 1 ≤ 2 * r + 1 := by
  omega

private theorem bankTrialSuccessOpaqueRatioCoefficient
    (x : Nat) : 4 * (2 * x + 1) ≤ 8 * (x + 1) := by
  omega

/-- The b=17 doubled base certificate. -/
private theorem bankTrialSuccessDoubledBase :
    2048 * (2 ^ 18 + 1) * 2 ^ 36 * 4 ^ 211 <
      5 ^ 211 := by
  have h :
      2048 * (2 ^ 18 + 1) * 2 ^ 36 * 4 ^ 211 + 1 ≤
        5 ^ 211 := Nat.le_of_ble_eq_true rfl
  exact bankTrialSuccessStrictOfSuccBound _ _ h

private theorem bankTrialSuccessDoubledRatioConstant :
    8 * 4 ^ 11 < 5 ^ 11 := by
  have h : 8 * 4 ^ 11 + 1 ≤ 5 ^ 11 :=
    Nat.le_of_ble_eq_true rfl
  exact bankTrialSuccessStrictOfSuccBound _ _ h

private theorem bankTrialSuccessDoubledRatio (b : Nat) :
    4 * (2 ^ (b + 2) + 1) * 4 ^ 11 <
      (2 ^ (b + 1) + 1) * 5 ^ 11 := by
  have hpow :
      2 ^ (b + 2) = 2 * 2 ^ (b + 1) := by
    rw [show b + 2 = (b + 1) + 1 by omega, Nat.pow_succ]
    exact Nat.mul_comm _ _
  have hcoef :
      4 * (2 ^ (b + 2) + 1) ≤
        8 * (2 ^ (b + 1) + 1) := by
    rw [hpow]
    exact bankTrialSuccessOpaqueRatioCoefficient
      (2 ^ (b + 1))
  have hpositive : 0 < 2 ^ (b + 1) + 1 :=
    Nat.zero_lt_succ _
  calc
    4 * (2 ^ (b + 2) + 1) * 4 ^ 11 ≤
        (8 * (2 ^ (b + 1) + 1)) * 4 ^ 11 :=
      Nat.mul_le_mul_right _ hcoef
    _ = (8 * 4 ^ 11) * (2 ^ (b + 1) + 1) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ < 5 ^ 11 * (2 ^ (b + 1) + 1) :=
      Nat.mul_lt_mul_of_pos_right
        bankTrialSuccessDoubledRatioConstant hpositive
    _ = (2 ^ (b + 1) + 1) * 5 ^ 11 := Nat.mul_comm _ _

private def bankTrialSuccessDoubledNumerator (b : Nat) : Nat :=
  2048 * (2 ^ (b + 1) + 1) *
    2 ^ (2 * b + 2) * 4 ^ (11 * b + 24)

private theorem bankTrialSuccessDoubledStep (b : Nat)
    (hb : bankTrialSuccessDoubledNumerator b <
      5 ^ (11 * b + 24)) :
    bankTrialSuccessDoubledNumerator (b + 1) <
      5 ^ (11 * (b + 1) + 24) := by
  have htwo :
      2 ^ (2 * (b + 1) + 2) =
        2 ^ (2 * b + 2) * 4 := by
    rw [show 2 * (b + 1) + 2 = (2 * b + 2) + 2 by omega,
      Nat.pow_add]
  have hfour :
      4 ^ (11 * (b + 1) + 24) =
        4 ^ (11 * b + 24) * 4 ^ 11 := by
    rw [show 11 * (b + 1) + 24 =
      (11 * b + 24) + 11 by omega, Nat.pow_add]
  have hfive :
      5 ^ (11 * (b + 1) + 24) =
        5 ^ (11 * b + 24) * 5 ^ 11 := by
    rw [show 11 * (b + 1) + 24 =
      (11 * b + 24) + 11 by omega, Nat.pow_add]
  calc
    bankTrialSuccessDoubledNumerator (b + 1) =
        (2048 * 2 ^ (2 * b + 2) * 4 ^ (11 * b + 24)) *
          (4 * (2 ^ (b + 2) + 1) * 4 ^ 11) := by
      unfold bankTrialSuccessDoubledNumerator
      rw [show b + 1 + 1 = b + 2 by omega, htwo, hfour]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (2048 * 2 ^ (2 * b + 2) * 4 ^ (11 * b + 24)) *
          ((2 ^ (b + 1) + 1) * 5 ^ 11) :=
      Nat.mul_le_mul_left _
        (Nat.le_of_lt (bankTrialSuccessDoubledRatio b))
    _ = bankTrialSuccessDoubledNumerator b * 5 ^ 11 := by
      unfold bankTrialSuccessDoubledNumerator
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ < 5 ^ (11 * b + 24) * 5 ^ 11 :=
      Nat.mul_lt_mul_of_pos_right hb
        (Nat.pow_pos (by omega))
    _ = 5 ^ (11 * (b + 1) + 24) := hfive.symm

/-- Terminal observers cannot emit further worker origins. -/
private theorem bankTrialSuccessTerminalOriginsZero
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (z : BankTrialLocalState q)
    (ht : bankTrialLocalTerminal z)
    (suffix : List (Fin n)) :
    Prob.originsWord (bankTrialLocalNext ring root)
      bankTrialLocalTerminal (bankTrialC5ActualStarts ring root S)
      z suffix = 0 := by
  cases suffix with
  | nil => rfl
  | cons e tail =>
      simp only [Prob.originsWord, if_pos ht]


/-- Closed counterexample to the originally proposed opaque
forward-collection inequality. The premises hold at small
natural numbers but the target would assert 6 <= 5. -/
theorem bankTrialSuccessOpaqueForwardCollectCounterexample :
    ¬ (∀ (D T X P E R J N Q B : Nat),
      D * T * X ≤
        D * T * (P * R) +
          T * (((J * (2 * N) * X + Q) + D * (P * E))) →
      R ≤ E →
      T * Q ≤ P * D * B * X →
      E ≤ X →
      D * T * X ≤
        D * T * (P * E) +
          (J * (2 * N) * T + P * D * (B + 1)) * X) := by
  intro h
  have hbad := h 1 3 2 1 1 1 0 0 0 0
    (by decide) (by decide) (by decide) (by decide)
  change (6 : Nat) ≤ 5 at hbad
  omega


private theorem bankTrialSuccessDoubledAll (b : Nat)
    (hb : 17 ≤ b) :
    bankTrialSuccessDoubledNumerator b <
      5 ^ (11 * b + 24) := by
  have haux : ∀ k : Nat,
      bankTrialSuccessDoubledNumerator (17 + k) <
        5 ^ (11 * (17 + k) + 24) := by
    intro k
    induction k with
    | zero =>
        change 2048 * (2 ^ 18 + 1) * 2 ^ 36 * 4 ^ 211 <
          5 ^ 211
        exact bankTrialSuccessDoubledBase
    | succ k ih =>
        have hs := bankTrialSuccessDoubledStep (17 + k) ih
        simpa only [Nat.add_succ] using hs
  obtain ⟨k, hk⟩ : ∃ k : Nat, b = 17 + k :=
    ⟨b - 17, by omega⟩
  rw [hk]
  exact haux k


/-- P1, the ACTUAL doubled worker margin:
2048 (2K+1) N < D. -/
theorem bankTrialSuccessDoubledWorkerBudget (q : Nat)
    (hsp : (compileAdvice q).useSmall = false)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b) :
    2048 * (2 * (compileAdvice q).K + 1) *
      bankTrialProbabilityC5WorkerNumerator q <
      bankTrialProbabilityC5WorkerDenominator q := by
  have hbase := bankTrialSuccessDoubledAll
    (compileAdvice q).b
    (Counter.resetColdWatchdogSpatialWidth q hsp)
  have hcount :
      2 * (compileAdvice q).K + 1 ≤
        2 ^ ((compileAdvice q).b + 1) + 1 := by
    rw [Nat.pow_succ]
    simpa only [Nat.mul_comm] using
      (bankTrialSuccessOpaqueDoubleCount
        (compileAdvice q).K
        (2 ^ (compileAdvice q).b) hwidth)
  calc
    2048 * (2 * (compileAdvice q).K + 1) *
        bankTrialProbabilityC5WorkerNumerator q ≤
      2048 * (2 ^ ((compileAdvice q).b + 1) + 1) *
        bankTrialProbabilityC5WorkerNumerator q :=
      Nat.mul_le_mul_right _
        (Nat.mul_le_mul_left 2048 hcount)
    _ < bankTrialProbabilityC5WorkerDenominator q := by
      unfold bankTrialProbabilityC5WorkerNumerator
        bankTrialProbabilityC5WorkerDenominator
      simpa only [bankTrialSuccessDoubledNumerator,
        Nat.mul_assoc] using hbase

/-! P3: count distinct actual worker origins across authentic cuts. -/

private theorem bankTrialSuccessOriginsAppend
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    ∀ (pre suffix : List (Fin n)) (z : BankTrialLocalState q),
      Prob.originsWord (bankTrialLocalNext ring root)
        bankTrialLocalTerminal (bankTrialC5ActualStarts ring root S)
        z (pre ++ suffix) =
      Prob.originsWord (bankTrialLocalNext ring root)
        bankTrialLocalTerminal (bankTrialC5ActualStarts ring root S)
        z pre +
      Prob.originsWord (bankTrialLocalNext ring root)
        bankTrialLocalTerminal (bankTrialC5ActualStarts ring root S)
        (bankTrialLocalRun ring root pre z) suffix := by
  intro pre
  induction pre with
  | nil =>
      intro suffix z
      simp only [List.nil_append, Prob.originsWord,
        bankTrialLocalRun, Nat.zero_add]
  | cons e tail ih =>
      intro suffix z
      by_cases ht : bankTrialLocalTerminal z
      · have hfix := bankTrialLocalRunTerminalAbsorbs
          ring root (e :: tail) z ht
        simp only [List.cons_append, Prob.originsWord,
          if_pos ht, hfix, Nat.zero_add]
        exact (bankTrialSuccessTerminalOriginsZero
          ring root S z ht suffix).symm
      · simp only [List.cons_append, Prob.originsWord,
          if_neg ht, bankTrialLocalRun]
        rw [ih suffix (bankTrialLocalNext ring root z e),
          Nat.add_assoc]


/-- A GOOD first-origin report necessarily materialized at
least one actual worker origin on the scanned suffix. -/
private theorem bankTrialSuccessPostHeadGoodHasOrigin
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    ∀ (word : List (Fin n)) (z : BankTrialLocalState q),
      bankTrialC5PostHeadFirstExit ring root S word z =
        some true →
      1 ≤ Prob.originsWord (bankTrialLocalNext ring root)
        bankTrialLocalTerminal (bankTrialC5ActualStarts ring root S)
        z word := by
  intro word
  induction word with
  | nil =>
      intro z hgood
      simp only [bankTrialC5PostHeadFirstExit] at hgood
      cases hgood
  | cons e tail ih =>
      intro z hgood
      have hnot : ¬ bankTrialLocalTerminal z := by
        intro ht
        have hn := bankTrialSuccessTerminalPostHeadNone
          ring root S z ht (e :: tail)
        rw [hgood] at hn
        cases hn
      cases hs : bankTrialC5ActualStarts ring root S z e with
      | nil =>
          have htail :
              bankTrialC5PostHeadFirstExit ring root S tail
                (bankTrialLocalNext ring root z e) =
                  some true := by
            simpa only [bankTrialC5PostHeadFirstExit, hs]
              using hgood
          have hrec := ih (bankTrialLocalNext ring root z e) htail
          simpa only [Prob.originsWord, if_neg hnot, hs,
            List.length_nil, Nat.zero_add] using hrec
      | cons o others =>
          simp only [Prob.originsWord, if_neg hnot, hs,
            List.length_cons]
          omega

/-- The chronological j-th GOOD return has paid at least j
distinct actual materialized worker origins. -/
theorem bankTrialSuccessGoodCutOriginsLower
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word : List (Fin n)) :
    ∀ (j : Nat) (cut : List (Fin n)),
      bankTrialSuccessGoodReturnCutPrefix
        ring root S word j = some cut →
      j ≤ bankTrialC5ActualPrefixOrigins ring root S cut := by
  intro j
  induction j with
  | zero =>
      intro cut _
      exact Nat.zero_le _
  | succ j ih =>
      intro cut hcut
      obtain ⟨prev, hprev⟩ :=
        bankTrialSuccessCutHistoryEarlierExists
          ring root S word cut j (j + 1)
          (by omega) hcut
      obtain ⟨segment, hscan, heq⟩ :=
        bankTrialSuccessAdjacentGoodSegment
          ring root S word prev cut j hprev hcut
      have hpost := bankTrialSuccessFirstGoodSelfScan
        ring root S
        (bankTrialLocalRun ring root prev (bankTrialLocalStart S))
        (word.drop prev.length) [] segment hscan
      have hnew := bankTrialSuccessPostHeadGoodHasOrigin
        ring root S segment
        (bankTrialLocalRun ring root prev (bankTrialLocalStart S))
        hpost
      have hold := ih prev hprev
      have hconcat := bankTrialSuccessOriginsAppend
        ring root S prev segment (bankTrialLocalStart S)
      rw [heq]
      change j + 1 ≤
        bankTrialC5ActualPrefixOrigins ring root S
          (prev ++ segment)
      rw [show bankTrialC5ActualPrefixOrigins
          ring root S (prev ++ segment) =
            bankTrialC5ActualPrefixOrigins ring root S prev +
            Prob.originsWord (bankTrialLocalNext ring root)
              bankTrialLocalTerminal
              (bankTrialC5ActualStarts ring root S)
              (bankTrialLocalRun ring root prev
                (bankTrialLocalStart S)) segment from hconcat]
      omega

theorem bankTrialSuccessStartCapGoodCutWon
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (word cut : List (Fin n))
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word (2 * (compileAdvice q).K + 1) =
        some cut) :
    (bankTrialLocalRun ring root cut
      (bankTrialLocalStart S)).phase = .won := by
  have hcount := bankTrialSuccessGoodCutOriginsLower
    ring root S word (2 * (compileAdvice q).K + 1) cut hcut
  have hcharge := bankTrialC5ActualPrefixChargeOfModeEntry
    ring root S hclean
    (bankTrialC5ActualLiveModeEntryHolds
      ring root S hlarge hclean) cut
  have hheads := bankTrialC5ActualAllWordsHeadCap
    ring root S hsp hlarge hwidth hclean cut
  rcases bankTrialSuccessCutModeTrichotomy
      ring root S hclean word cut
      (2 * (compileAdvice q).K + 1) hcut with
    harmed | hcstart | hwon
  · have hstrict := bankTrialSuccessReachableArmedHeadStrict
      ring root S hsp hlarge hwidth hclean cut harmed
    have horigins := hcharge.1
    omega
  · obtain ⟨⟨begun, hlive⟩, hmode⟩ := hcstart
    have hstrong := hcharge.2 begun hlive (Or.inr hmode)
    omega
  · exact hwon


/-- P3: the 2K+1-st GOOD-cut reach cylinder is contained
pointwise in completed K-HEAD words on the ORIGINAL tape. -/
theorem bankTrialSuccessStartCapReachLeCompleted
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (T : Nat) :
    bankTrialSuccessCutReachMass ring root S
        (2 * (compileAdvice q).K + 1) T ≤
      bankTrialProbabilityC5CompletedHeadMass ring root S T := by
  unfold bankTrialSuccessCutReachMass
    bankTrialProbabilityC5CompletedHeadMass
  apply bankTrialProbabilityScheduleSumMono n T
  intro word
  cases hc :
      bankTrialSuccessGoodReturnCutPrefix
        ring root S word (2 * (compileAdvice q).K + 1) with
  | none =>
      simp [Prob.indicator, hc]
  | some cut =>
      have hwon := bankTrialSuccessStartCapGoodCutWon
        ring root S hsp hlarge hwidth hclean word cut hc
      have hcompleted :=
        bankTrialSuccessWonGoodCutCompletedHeadWord
          ring root S hsp hlarge hclean word cut
          (2 * (compileAdvice q).K + 1) hc hwon
      simp [Prob.indicator, hc, hcompleted]

/-! P2: a coarser but fully sufficient C.6 charge.  We keep
the factor 3 for the two ARMED pending indicators instead
of requiring a pointwise disjointness lemma. -/

private theorem bankTrialSuccessPendingBoolTriple
    (D : Nat) (a b : Bool) :
    D * Prob.indicator a + 2 * D * Prob.indicator b ≤
      (3 * D) * Prob.indicator (a || b) := by
  cases a <;> cases b <;> simp [Prob.indicator] <;> omega

/-- A stage-local pending penalty is at most three worker
denominators times its actual physical pending-event mass.
This holds in ALL modes, with CSTART taking priority. -/
theorem bankTrialSuccessCutPenaltyLePendingMass
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (z : BankTrialLocalState q) (t : Nat) :
    bankTrialSuccessCutPenaltyAt ring root S z t ≤
      (3 * bankTrialProbabilityC5WorkerDenominator q) *
        Prob.scheduleSum n t (fun suffix =>
          Prob.indicator
            (bankTrialSuccessGoodReturnStagePendingAt
              ring root S z suffix)) := by
  by_cases hc : bankTrialLiveWaveRootMode z.bank = .CSTART
  · have hle :
        bankTrialProbabilityC5WorkerDenominator q ≤
          3 * bankTrialProbabilityC5WorkerDenominator q := by
      omega
    have hmul := Nat.mul_le_mul_right
      (Prob.scheduleSum n t (fun suffix =>
        Prob.indicator
          (bankTrialC5CStartPendingBool ring root S z suffix)))
      hle
    simpa only [bankTrialSuccessCutPenaltyAt, if_pos hc,
      bankTrialC5CStartMass,
      bankTrialSuccessGoodReturnStagePendingAt]
      using hmul
  · by_cases hg : BankTrialProbabilityArmedGate z
    · have hword (suffix : List (Fin n)) :
          bankTrialProbabilityC5WorkerDenominator q *
            Prob.indicator
              (bankTrialC5PendingBeforeBool ring root S z suffix) +
          2 * bankTrialProbabilityC5WorkerDenominator q *
            Prob.indicator
              (bankTrialC5PendingAfterBool ring root S z suffix) ≤
          (3 * bankTrialProbabilityC5WorkerDenominator q) *
            Prob.indicator
              (bankTrialC5PendingBeforeBool ring root S z suffix ||
                bankTrialC5PendingAfterBool ring root S z suffix) :=
        bankTrialSuccessPendingBoolTriple
          (bankTrialProbabilityC5WorkerDenominator q)
          (bankTrialC5PendingBeforeBool ring root S z suffix)
          (bankTrialC5PendingAfterBool ring root S z suffix)
      have hsum := bankTrialProbabilityScheduleSumMono
        n t _ _ hword
      rw [bankTrialC5ScheduleSumAdd,
        bankTrialSuccessScheduleSumScale,
        bankTrialSuccessScheduleSumScale,
        bankTrialSuccessScheduleSumScale] at hsum
      simpa only [bankTrialSuccessCutPenaltyAt,
        if_neg hc, if_pos hg,
        bankTrialC5PendingBeforeMass,
        bankTrialC5PendingAfterMass,
        bankTrialSuccessGoodReturnStagePendingAt]
        using hsum
    · simp only [bankTrialSuccessCutPenaltyAt,
        if_neg hc, if_neg hg]
      exact Nat.zero_le _

/-- At each authenticated j-th first-stop prefix, the K1
history factor can be bounded before charging pending. -/
private theorem bankTrialSuccessPendingStoppedCutCharge
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (cut : List (Fin n)) (j t : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S cut j = some cut) :
    2 ^ bankTrialSuccessCutHistoryArmedCount ring root S cut j *
      bankTrialSuccessCutPenaltyAt ring root S
        (bankTrialLocalRun ring root cut (bankTrialLocalStart S)) t ≤
    (2 ^ (compileAdvice q).K *
      (3 * bankTrialProbabilityC5WorkerDenominator q)) *
      Prob.scheduleSum n t (fun suffix =>
        Prob.indicator (bankTrialSuccessGoodReturnStagePendingAt
          ring root S
          (bankTrialLocalRun ring root cut (bankTrialLocalStart S))
          suffix)) := by
  have hk := bankTrialSuccessEveryGoodCutArmedCap
    ring root S hsp hlarge hwidth hclean cut cut j hcut
  have hp := bankTrialSuccessTwoPowerMonotone
    (bankTrialSuccessCutHistoryArmedCount ring root S cut j)
    (compileAdvice q).K hk
  have hlocal := bankTrialSuccessCutPenaltyLePendingMass
    ring root S
    (bankTrialLocalRun ring root cut (bankTrialLocalStart S)) t
  calc
    2 ^ bankTrialSuccessCutHistoryArmedCount ring root S cut j *
        bankTrialSuccessCutPenaltyAt ring root S
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) t ≤
      2 ^ bankTrialSuccessCutHistoryArmedCount ring root S cut j *
        ((3 * bankTrialProbabilityC5WorkerDenominator q) *
          Prob.scheduleSum n t (fun suffix =>
            Prob.indicator (bankTrialSuccessGoodReturnStagePendingAt
              ring root S (bankTrialLocalRun ring root cut
                (bankTrialLocalStart S)) suffix))) :=
      Nat.mul_le_mul_left _ hlocal
    _ ≤ 2 ^ (compileAdvice q).K *
        ((3 * bankTrialProbabilityC5WorkerDenominator q) *
          Prob.scheduleSum n t (fun suffix =>
            Prob.indicator (bankTrialSuccessGoodReturnStagePendingAt
              ring root S (bankTrialLocalRun ring root cut
                (bankTrialLocalStart S)) suffix))) :=
      Nat.mul_le_mul_right _ hp
    _ = _ := by simp only [Nat.mul_assoc]

/-- Boolean first-stop factorization for the ACTUAL pending
observer with the stoppedTapeRun/localRun conversion. -/
private theorem bankTrialSuccessPendingStoppedFactorization
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j T : Nat) :
    Prob.scheduleSum n T (fun word =>
      Prob.indicator
        (bankTrialSuccessGoodReturnStagePendingBool
          ring root S j T word)) =
    ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
      (bankTrialSuccessGoodReturnCutBool ring root S j)
      T [] (bankTrialLocalStart S)).map (fun cut =>
        Prob.scheduleSum n (T - cut.length) (fun suffix =>
          Prob.indicator (bankTrialSuccessGoodReturnStagePendingAt
            ring root S
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) suffix)))).sum := by
  unfold bankTrialSuccessGoodReturnStagePendingBool
  calc
    Prob.scheduleSum n T (fun word =>
        Prob.indicator
          (Prob.firstStoppedSuffixWord (bankTrialLocalNext ring root)
            (bankTrialSuccessGoodReturnCutBool ring root S j)
            (fun z _ suffix =>
              bankTrialSuccessGoodReturnStagePendingAt
                ring root S z suffix)
            T [] (bankTrialLocalStart S) word)) =
      ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        T [] (bankTrialLocalStart S)).map (fun cut =>
        Prob.scheduleSum n (T - cut.length) (fun suffix =>
          Prob.indicator
            (bankTrialSuccessGoodReturnStagePendingAt
              ring root S
              (Prob.stoppedTapeRun (bankTrialLocalNext ring root)
                cut (bankTrialLocalStart S)) suffix)))).sum :=
      Prob.stoppedPrefixFactorization
        (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        (fun z _ suffix =>
          bankTrialSuccessGoodReturnStagePendingAt ring root S z suffix)
        (bankTrialLocalStart S) T
        (bankTrialSuccessGoodReturnCutPrefixFree ring root S j)
    _ = _ := by
      apply bankTrialSuccessCutHistoryMapSumExt
      intro cut
      rw [bankTrialSuccessStoppedRunEqLocal
        ring root cut (bankTrialLocalStart S)]

theorem bankTrialSuccessPendingOneCutLeActive
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (j T : Nat) :
    bankTrialSuccessPendingPrefixHistoryMass ring root S j T ≤
      (2 ^ (compileAdvice q).K *
        (3 * bankTrialProbabilityC5WorkerDenominator q)) *
        bankTrialDurationActiveMass ring root S T := by
  have hmap :
      ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        T [] (bankTrialLocalStart S)).map (fun cut =>
        2 ^ bankTrialSuccessCutHistoryArmedCount
          ring root S cut j *
        bankTrialSuccessCutPenaltyAt ring root S
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) (T - cut.length))).sum ≤
      ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        T [] (bankTrialLocalStart S)).map (fun cut =>
        (2 ^ (compileAdvice q).K *
          (3 * bankTrialProbabilityC5WorkerDenominator q)) *
        Prob.scheduleSum n (T - cut.length) (fun suffix =>
          Prob.indicator (bankTrialSuccessGoodReturnStagePendingAt
            ring root S (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) suffix)))).sum := by
    apply bankTrialSuccessMapSumMonotone
    intro cut hmem
    exact bankTrialSuccessPendingStoppedCutCharge
      ring root S hsp hlarge hwidth hclean cut j
      (T - cut.length)
      (bankTrialSuccessStoppedGoodCutAuthenticated
        ring root S j T cut hmem)
  have hfactor := bankTrialSuccessPendingStoppedFactorization
    ring root S j T
  have hactive :
      Prob.scheduleSum n T (fun word =>
        Prob.indicator
          (bankTrialSuccessGoodReturnStagePendingBool
            ring root S j T word)) ≤
      bankTrialDurationActiveMass ring root S T := by
    have hword (word : List (Fin n)) :
        Prob.indicator
          (bankTrialSuccessGoodReturnStagePendingBool
            ring root S j T word) ≤
        (if bankTrialLocalTerminal
          (bankTrialLocalRun ring root word
            (bankTrialLocalStart S)) then 0 else 1) := by
      cases hp : bankTrialSuccessGoodReturnStagePendingBool
          ring root S j T word with
      | false =>
          simp [Prob.indicator, hp]
      | true =>
          have hb := bankTrialSuccessStagePendingBridge
            ring root S hsp hlarge hwidth hclean j T word hp
          have hn : ¬ bankTrialLocalTerminal
              (bankTrialLocalRun ring root word
                (bankTrialLocalStart S)) := by
            change decide (¬ bankTrialLocalTerminal
              (bankTrialLocalRun ring root word
                (bankTrialLocalStart S))) = true at hb
            exact of_decide_eq_true hb
          simp [Prob.indicator, hp, hn]
    change
      Prob.scheduleSum n T (fun word =>
        Prob.indicator
          (bankTrialSuccessGoodReturnStagePendingBool
            ring root S j T word)) ≤
      Prob.scheduleSum n T (fun word =>
        if bankTrialLocalTerminal
          (bankTrialLocalRun ring root word
            (bankTrialLocalStart S)) then 0 else 1)
    exact bankTrialProbabilityScheduleSumMono n T _ _ hword
  calc
    bankTrialSuccessPendingPrefixHistoryMass ring root S j T =
      ((Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
        (bankTrialSuccessGoodReturnCutBool ring root S j)
        T [] (bankTrialLocalStart S)).map (fun cut =>
        2 ^ bankTrialSuccessCutHistoryArmedCount
          ring root S cut j *
        bankTrialSuccessCutPenaltyAt ring root S
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) (T - cut.length))).sum := rfl
    _ ≤ _ := hmap
    _ = (2 ^ (compileAdvice q).K *
          (3 * bankTrialProbabilityC5WorkerDenominator q)) *
        Prob.scheduleSum n T (fun word =>
          Prob.indicator
            (bankTrialSuccessGoodReturnStagePendingBool
              ring root S j T word)) := by
      rw [hfactor]
      exact bankTrialSuccessListMapScale
        (Prob.firstStoppedPrefixes (bankTrialLocalNext ring root)
          (bankTrialSuccessGoodReturnCutBool ring root S j)
          T [] (bankTrialLocalStart S))
        (2 ^ (compileAdvice q).K *
          (3 * bankTrialProbabilityC5WorkerDenominator q))
        (fun cut =>
          Prob.scheduleSum n (T - cut.length) (fun suffix =>
            Prob.indicator (bankTrialSuccessGoodReturnStagePendingAt
              ring root S (bankTrialLocalRun ring root cut
                (bankTrialLocalStart S)) suffix)))
    _ ≤ _ := Nat.mul_le_mul_left _ hactive


private theorem bankTrialSuccessOpaquePendingClock
    (T J P D A X B Q : Nat)
    (hsum : Q ≤ J * ((P * (3 * D)) * A))
    (hmean : T * A ≤ X * B) :
    T * Q ≤ P * D * (3 * J * B) * X := by
  calc
    T * Q ≤ T * (J * ((P * (3 * D)) * A)) :=
      Nat.mul_le_mul_left T hsum
    _ = (P * D * (3 * J)) * (T * A) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (P * D * (3 * J)) * (X * B) :=
      Nat.mul_le_mul_left _ hmean
    _ = P * D * (3 * J * B) * X := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- P2, coarser C.6 form with the NECESSARY factor T.
It uses no unproved final-stage ordinal and no independence.
Coefficient: 3*(2K+1)*(8b+12)*n, not the proposed sharper
(K+(2K+1)*(2b+3))*n. The larger finite clock still suffices. -/
theorem bankTrialSuccessPendingAllCutsCoarseMarkov
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (J T : Nat) :
    T * bankTrialSuccessStageIndexSum
      (fun j => bankTrialSuccessPendingPrefixHistoryMass
        ring root S j T) J ≤
      2 ^ (compileAdvice q).K *
        bankTrialProbabilityC5WorkerDenominator q *
        (3 * J * ((8 * (compileAdvice q).b + 12) * n)) *
        n ^ T := by
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hn : 2 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    omega
  have hK : 0 < (compileAdvice q).K :=
    Counter.resetColdPrivateKPositive q hsp
  have hmean := bankTrialSuccessMarkovOfDurationBound
    ring root hn hsp hw hK hwidth S hclean T
  have hsum :
      bankTrialSuccessStageIndexSum
        (fun j => bankTrialSuccessPendingPrefixHistoryMass
          ring root S j T) J ≤
      J * ((2 ^ (compileAdvice q).K *
        (3 * bankTrialProbabilityC5WorkerDenominator q)) *
          bankTrialDurationActiveMass ring root S T) := by
    have hm := bankTrialSuccessStageIndexSumMono
      (fun j => bankTrialSuccessPendingPrefixHistoryMass
        ring root S j T)
      (fun _ => (2 ^ (compileAdvice q).K *
        (3 * bankTrialProbabilityC5WorkerDenominator q)) *
        bankTrialDurationActiveMass ring root S T)
      (fun j => bankTrialSuccessPendingOneCutLeActive
        ring root S hsp hlarge hwidth hclean j T) J
    rw [bankTrialSuccessStageIndexSumConstant] at hm
    exact hm
  exact bankTrialSuccessOpaquePendingClock
    T J (2 ^ (compileAdvice q).K)
    (bankTrialProbabilityC5WorkerDenominator q)
    (bankTrialDurationActiveMass ring root S T)
    (n ^ T) ((8 * (compileAdvice q).b + 12) * n)
    (bankTrialSuccessStageIndexSum
      (fun j => bankTrialSuccessPendingPrefixHistoryMass
        ring root S j T) J)
    hsum hmean

/-! Last numerical collection: the terminal mass is paid once;
a single extra D*P*n^T is absorbed by lengthening the horizon. -/

theorem bankTrialSuccessCompletedHeadMassLeTotal
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) :
    bankTrialProbabilityC5CompletedHeadMass ring root S T ≤
      n ^ T := by
  unfold bankTrialProbabilityC5CompletedHeadMass
  calc
    Prob.scheduleSum n T (fun word =>
        if bankTrialProbabilityC5CompletedHeadWord
          ring root S word then 1 else 0) ≤
      Prob.scheduleSum n T (fun _ => 1) := by
      apply bankTrialProbabilityScheduleSumMono n T
      intro word
      split <;> omega
    _ = n ^ T := by
      simpa only [Nat.mul_one] using
        (bankTrialProbabilityScheduleSumConst n T 1)

end L3

#print axioms L3.bankTrialSuccessDoubledWorkerBudget
#print axioms L3.bankTrialSuccessGoodCutOriginsLower
#print axioms L3.bankTrialSuccessStartCapGoodCutWon
#print axioms L3.bankTrialSuccessStartCapReachLeCompleted
#print axioms L3.bankTrialSuccessCutPenaltyLePendingMass
#print axioms L3.bankTrialSuccessPendingOneCutLeActive
#print axioms L3.bankTrialSuccessPendingAllCutsCoarseMarkov
#print axioms L3.bankTrialSuccessCompletedHeadMassLeTotal

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
Q4: joint terminal accounting on the ONE physical scheduler tape,
followed by an opaque-Nat horizon calculation.
No independent resampling of worker cuts is used.
-/

/-- At a terminal j-th good-return cut, every earlier WON charge
vanishes.  The cut is the unique last-good ordinal. -/
theorem bankTrialSuccessEarlierWonWeightsZeroOfTerminal
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (word cut : List (Fin n)) (j : Nat)
    (hcut : bankTrialSuccessGoodReturnCutPrefix
      ring root S word j = some cut)
    (hwon : (bankTrialLocalRun ring root cut
      (bankTrialLocalStart S)).phase = .won) :
    bankTrialSuccessStageIndexSum (fun i =>
      bankTrialSuccessCutWonWordMass ring root S word i *
        2 ^ bankTrialSuccessCutHistoryArmedCount
          ring root S word i) j = 0 := by
  have hnext := bankTrialSuccessWonGoodCutNextNone
    ring root S word cut j hcut hwon
  have hordinal := bankTrialSuccessOrdinalOfAdjacentCuts
    ring root S word cut j hcut hnext
  calc
    bankTrialSuccessStageIndexSum (fun i =>
        bankTrialSuccessCutWonWordMass ring root S word i *
          2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S word i) j =
      bankTrialSuccessStageIndexSum (fun _ => 0) j := by
        exact bankTrialSuccessCutHistorySumExt
          (fun i =>
            bankTrialSuccessCutWonWordMass ring root S word i *
              2 ^ bankTrialSuccessCutHistoryArmedCount
                ring root S word i)
          (fun _ => 0) j (fun i hi => by
            have hbound := bankTrialSuccessWonWordWeightLeCompletion
              ring root S hsp hlarge hwidth hclean word i
            have hne : i ≠
                bankTrialSuccessGoodReturnOrdinal ring root S word := by
              rw [hordinal]
              omega
            rw [if_neg hne] at hbound
            exact Nat.eq_zero_of_le_zero hbound)
    _ = 0 := bankTrialSuccessStageIndexSumZero j

/-- Joint indicator bound, word by word, at J = 2K+1.
The J-th reachable cut and all earlier WON cuts have disjoint
support.  Each carries at most 2^K, never two copies of it. -/
theorem bankTrialSuccessJointTerminalWordBound
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (word : List (Fin n)) :
    Prob.indicator
      (bankTrialSuccessGoodReturnCutPrefix ring root S word
        (2 * (compileAdvice q).K + 1)).isSome *
      2 ^ bankTrialSuccessCutHistoryArmedCount
        ring root S word (2 * (compileAdvice q).K + 1) +
    bankTrialSuccessStageIndexSum (fun i =>
      bankTrialSuccessCutWonWordMass ring root S word i *
        2 ^ bankTrialSuccessCutHistoryArmedCount
          ring root S word i)
      (2 * (compileAdvice q).K + 1) ≤
    2 ^ (compileAdvice q).K *
      (if bankTrialProbabilityC5CompletedHeadWord
        ring root S word then 1 else 0) := by
  cases hcut :
      bankTrialSuccessGoodReturnCutPrefix ring root S word
        (2 * (compileAdvice q).K + 1) with
  | none =>
      have hbound := bankTrialSuccessWonWordAllCutsBound
        ring root S hsp hlarge hwidth hclean word
        (2 * (compileAdvice q).K + 1)
      simpa [hcut, Prob.indicator] using hbound
  | some cut =>
      have hwon := bankTrialSuccessStartCapGoodCutWon
        ring root S hsp hlarge hwidth hclean word cut hcut
      have hzero := bankTrialSuccessEarlierWonWeightsZeroOfTerminal
        ring root S hsp hlarge hwidth hclean
        word cut (2 * (compileAdvice q).K + 1) hcut hwon
      have hcomplete := bankTrialSuccessWonGoodCutCompletedHeadWord
        ring root S hsp hlarge hclean word cut
        (2 * (compileAdvice q).K + 1) hcut hwon
      have hcap := bankTrialSuccessEveryGoodCutArmedCap
        ring root S hsp hlarge hwidth hclean word cut
        (2 * (compileAdvice q).K + 1) hcut
      have hpower := bankTrialSuccessTwoPowerMonotone
        (bankTrialSuccessCutHistoryArmedCount ring root S word
          (2 * (compileAdvice q).K + 1))
        (compileAdvice q).K hcap
      simpa [hcut, Prob.indicator, hzero, hcomplete] using hpower

/-- (J) The original scheduler horizon has only ONE charged
completed-head cylinder, shared by the final reach and all
prior WON debts. -/
theorem bankTrialSuccessJointTerminalMassBound
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (T : Nat) :
    bankTrialSuccessCutHistoryWeightedMass ring root S
        (2 * (compileAdvice q).K + 1) T +
      bankTrialSuccessStageIndexSum (fun i =>
        bankTrialSuccessWonPrefixHistoryMass ring root S i T)
        (2 * (compileAdvice q).K + 1) ≤
      2 ^ (compileAdvice q).K *
        bankTrialProbabilityC5CompletedHeadMass ring root S T := by
  have hterms :
      bankTrialSuccessStageIndexSum (fun i =>
        bankTrialSuccessWonPrefixHistoryMass ring root S i T)
        (2 * (compileAdvice q).K + 1) =
      Prob.scheduleSum n T (fun word =>
        bankTrialSuccessStageIndexSum (fun i =>
          bankTrialSuccessCutWonWordMass ring root S word i *
            2 ^ bankTrialSuccessCutHistoryArmedCount
              ring root S word i)
          (2 * (compileAdvice q).K + 1)) := by
    have hfun :
        (fun i => bankTrialSuccessWonPrefixHistoryMass
          ring root S i T) =
        (fun i => Prob.scheduleSum n T (fun word =>
          bankTrialSuccessCutWonWordMass ring root S word i *
            2 ^ bankTrialSuccessCutHistoryArmedCount
              ring root S word i)) := by
      funext i
      exact bankTrialSuccessWonPrefixHistoryFactorization
        ring root S i T
    rw [hfun]
    exact bankTrialSuccessStageIndexSumSchedule n T
      (2 * (compileAdvice q).K + 1)
      (fun i word =>
        bankTrialSuccessCutWonWordMass ring root S word i *
          2 ^ bankTrialSuccessCutHistoryArmedCount
            ring root S word i)
  calc
    bankTrialSuccessCutHistoryWeightedMass ring root S
        (2 * (compileAdvice q).K + 1) T +
        bankTrialSuccessStageIndexSum (fun i =>
          bankTrialSuccessWonPrefixHistoryMass ring root S i T)
          (2 * (compileAdvice q).K + 1) =
      Prob.scheduleSum n T (fun word =>
        Prob.indicator
          (bankTrialSuccessGoodReturnCutPrefix ring root S word
            (2 * (compileAdvice q).K + 1)).isSome *
          2 ^ bankTrialSuccessCutHistoryArmedCount ring root S word
            (2 * (compileAdvice q).K + 1) +
        bankTrialSuccessStageIndexSum (fun i =>
          bankTrialSuccessCutWonWordMass ring root S word i *
            2 ^ bankTrialSuccessCutHistoryArmedCount
              ring root S word i)
          (2 * (compileAdvice q).K + 1)) := by
      rw [hterms]
      unfold bankTrialSuccessCutHistoryWeightedMass
      exact (bankTrialC5ScheduleSumAdd T _ _).symm
    _ ≤ Prob.scheduleSum n T (fun word =>
        2 ^ (compileAdvice q).K *
          (if bankTrialProbabilityC5CompletedHeadWord
            ring root S word then 1 else 0)) := by
      apply bankTrialProbabilityScheduleSumMono n T
      intro word
      exact bankTrialSuccessJointTerminalWordBound
        ring root S hsp hlarge hwidth hclean word
    _ = 2 ^ (compileAdvice q).K *
          bankTrialProbabilityC5CompletedHeadMass ring root S T := by
      unfold bankTrialProbabilityC5CompletedHeadMass
      exact bankTrialSuccessScheduleSumScale n T
        (2 ^ (compileAdvice q).K)
        (fun word =>
          if bankTrialProbabilityC5CompletedHeadWord
            ring root S word then 1 else 0)

/-- Exact telescope debt split before taking ANY upper bound:
rarity, pending and ONE terminal WON charge remain separate. -/
theorem bankTrialSuccessJointDebtIdentity
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (J T : Nat) :
    bankTrialSuccessStageIndexSum (fun i =>
      bankTrialSuccessCutHistoryPrefixDebt ring root S i T) J =
    bankTrialSuccessStageIndexSum (fun i =>
      2 * bankTrialProbabilityC5WorkerNumerator q *
        bankTrialSuccessCutHistoryWeightedMass ring root S i T) J +
    bankTrialSuccessStageIndexSum (fun i =>
      bankTrialSuccessPendingPrefixHistoryMass ring root S i T) J +
    bankTrialProbabilityC5WorkerDenominator q *
      bankTrialSuccessStageIndexSum (fun i =>
        bankTrialSuccessWonPrefixHistoryMass ring root S i T) J := by
  have hfun :
      (fun i => bankTrialSuccessCutHistoryPrefixDebt
        ring root S i T) =
      (fun i =>
        2 * bankTrialProbabilityC5WorkerNumerator q *
          bankTrialSuccessCutHistoryWeightedMass
            ring root S i T +
        bankTrialSuccessPendingPrefixHistoryMass ring root S i T +
        bankTrialProbabilityC5WorkerDenominator q *
          bankTrialSuccessWonPrefixHistoryMass ring root S i T) := by
    funext i
    exact bankTrialSuccessPrefixDebtComponents
      ring root S i T
  rw [hfun, bankTrialSuccessStageIndexSumTriple,
    bankTrialSuccessStageIndexSumScale,
    bankTrialSuccessStageIndexSumScale]

/-- Opaque-Nat joint collection. Unlike the refuted earlier
collection, it charges A+V together BEFORE multiplication by T.
R is actual rarity, E is its per-horizon coefficient. -/
private theorem bankTrialSuccessOpaqueJointForwardCollect
    (D T X A V C R Q E P B : Nat)
    (htele : D * X ≤ D * A + (R + Q + D * V))
    (hrarity : R ≤ E * X)
    (hjoint : A + V ≤ P * C)
    (hpending : T * Q ≤ P * D * B * X) :
    D * T * X ≤
      D * T * (P * C) + (E * T + P * D * B) * X := by
  have hrarityCombined :
      D * X ≤ D * A + (E * X + Q + D * V) := by
    calc
      D * X ≤ D * A + (R + Q + D * V) := htele
      _ ≤ D * A + (E * X + Q + D * V) := by
        exact Nat.add_le_add_left
          (Nat.add_le_add_right
            (Nat.add_le_add_right hrarity Q) (D * V))
          (D * A)
  have hmass :
      D * X ≤ D * (P * C) + (E * X + Q) := by
    calc
      D * X ≤ D * A + (E * X + Q + D * V) :=
        hrarityCombined
      _ = D * (A + V) + (E * X + Q) := by
        simp only [Nat.mul_add, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm]
      _ ≤ D * (P * C) + (E * X + Q) :=
        Nat.add_le_add_right
          (Nat.mul_le_mul_left D hjoint) _
  calc
    D * T * X = T * (D * X) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ T * (D * (P * C) + (E * X + Q)) :=
      Nat.mul_le_mul_left T hmass
    _ = (D * T * (P * C) + (E * T) * X) + T * Q := by
      simp only [Nat.mul_add, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]
    _ ≤ (D * T * (P * C) + (E * T) * X) +
        P * D * B * X :=
      Nat.add_le_add_left hpending _
    _ = D * T * (P * C) +
        (E * T + P * D * B) * X := by
      simp only [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

/-- The corrected physical forward estimate.  The single CHM
cylinder pays reach and terminal debt JOINTLY; no extra CHM
term survives.  This is the doubled-N premise of the horizon
lemma with a coarse, finite C.6 pending clock. -/
theorem bankTrialSuccessForwardJointAtStartCap
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (T : Nat) :
    bankTrialProbabilityC5WorkerDenominator q * T * n ^ T ≤
      bankTrialProbabilityC5WorkerDenominator q * T *
        (2 ^ (compileAdvice q).K *
          bankTrialProbabilityC5CompletedHeadMass ring root S T) +
      (((2 * (compileAdvice q).K + 1) *
          (2 * bankTrialProbabilityC5WorkerNumerator q)) * T +
        2 ^ (compileAdvice q).K *
          bankTrialProbabilityC5WorkerDenominator q *
          (3 * (2 * (compileAdvice q).K + 1) *
            ((8 * (compileAdvice q).b + 12) * n))) *
        n ^ T := by
  have hkernel := bankTrialC5ActualWorkerExcursionKernelHolds
    ring root S hsp hlarge hwidth hclean
  have htel := bankTrialSuccessCutHistoryWeightedTelescopeOfKernel
    ring root S hkernel hlarge hclean
    (2 * (compileAdvice q).K + 1) T
  rw [bankTrialSuccessJointDebtIdentity
    ring root S (2 * (compileAdvice q).K + 1) T] at htel
  exact bankTrialSuccessOpaqueJointForwardCollect
    (bankTrialProbabilityC5WorkerDenominator q)
    T (n ^ T)
    (bankTrialSuccessCutHistoryWeightedMass ring root S
      (2 * (compileAdvice q).K + 1) T)
    (bankTrialSuccessStageIndexSum (fun i =>
      bankTrialSuccessWonPrefixHistoryMass ring root S i T)
      (2 * (compileAdvice q).K + 1))
    (bankTrialProbabilityC5CompletedHeadMass ring root S T)
    (bankTrialSuccessStageIndexSum (fun i =>
      2 * bankTrialProbabilityC5WorkerNumerator q *
        bankTrialSuccessCutHistoryWeightedMass ring root S i T)
      (2 * (compileAdvice q).K + 1))
    (bankTrialSuccessStageIndexSum (fun i =>
      bankTrialSuccessPendingPrefixHistoryMass ring root S i T)
      (2 * (compileAdvice q).K + 1))
    ((2 * (compileAdvice q).K + 1) *
      (2 * bankTrialProbabilityC5WorkerNumerator q))
    (2 ^ (compileAdvice q).K)
    (3 * (2 * (compileAdvice q).K + 1) *
      ((8 * (compileAdvice q).b + 12) * n))
    htel
    (bankTrialSuccessRarityAllCutsByFair
      ring root S hsp hlarge hwidth hclean
      (2 * (compileAdvice q).K + 1) T)
    (bankTrialSuccessJointTerminalMassBound
      ring root S hsp hlarge hwidth hclean T)
    (bankTrialSuccessPendingAllCutsCoarseMarkov
      ring root S hsp hlarge hwidth hclean
      (2 * (compileAdvice q).K + 1) T)

/-- The doubled worker budget is the 1024-budget for
the effective per-cut numerator 2N, using opaque multiplication
rather than unfolding the giant exponential coefficients. -/
private theorem bankTrialSuccessOpaqueDoubleBudget
    (J N D : Nat)
    (h : 2048 * J * N < D) :
    1024 * J * (2 * N) < D := by
  have heq : 1024 * J * (2 * N) = 2048 * J * N := by
    simp only [Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm, Nat.reduceMul]
  rw [heq]
  exact h

/-- The actual unconditional C.5 lower target.  The called
finite-horizon theorem explicitly chooses
T = 1024 * (2^K) * D * B + 1,
where B = 3(2K+1)(8b+12)n. -/
theorem bankTrialSuccessCompletedHeadMassLowerActual
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    BankTrialProbabilityC5CompletedHeadMassLower ring root S := by
  intro hsp hlarge hwidth hclean
  have hD : 0 < bankTrialProbabilityC5WorkerDenominator q := by
    unfold bankTrialProbabilityC5WorkerDenominator
    exact Nat.pow_pos (by omega)
  have hbudget :
      1024 * (2 * (compileAdvice q).K + 1) *
        (2 * bankTrialProbabilityC5WorkerNumerator q) <
      bankTrialProbabilityC5WorkerDenominator q :=
    bankTrialSuccessOpaqueDoubleBudget
      (2 * (compileAdvice q).K + 1)
      (bankTrialProbabilityC5WorkerNumerator q)
      (bankTrialProbabilityC5WorkerDenominator q)
      (bankTrialSuccessDoubledWorkerBudget q hsp hwidth)
  exact bankTrialC5ForwardOpaqueHorizon
    (D := bankTrialProbabilityC5WorkerDenominator q)
    (N := 2 * bankTrialProbabilityC5WorkerNumerator q)
    (M := 2 * (compileAdvice q).K + 1)
    (P := 2 ^ (compileAdvice q).K)
    (B := 3 * (2 * (compileAdvice q).K + 1) *
      ((8 * (compileAdvice q).b + 12) * n))
    (n := n) hD hbudget
    (bankTrialProbabilityC5CompletedHeadMass ring root S)
    (fun T _ =>
      bankTrialSuccessForwardJointAtStartCap
        ring root S hsp hlarge hwidth hclean T)

end L3


namespace L3

/-- G11c: the C.4/C.5 single-trial success lower bound at the actual
data, `1023 n^T <= 1024 2^K WinMass(T)` for some T, unconditional in
the BANK production regime (spatial-counter.tex (C.4)-(C.5)). -/
theorem bankTrialSuccessThetaLowerHolds
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    BankTrialProbabilityThetaLowerTarget ring root S :=
  bankTrialProbabilityThetaLowerOfCompletedHeadMass ring root S
    (bankTrialSuccessCompletedHeadMassLowerActual ring root S)

end L3

#print axioms L3.bankTrialSuccessEarlierWonWeightsZeroOfTerminal
#print axioms L3.bankTrialSuccessJointTerminalWordBound
#print axioms L3.bankTrialSuccessJointTerminalMassBound
#print axioms L3.bankTrialSuccessJointDebtIdentity
#print axioms L3.bankTrialSuccessForwardJointAtStartCap
#print axioms L3.bankTrialSuccessCompletedHeadMassLowerActual
#print axioms L3.bankTrialSuccessThetaLowerHolds

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
Part C. Bounded horizon.

The requested all-T theorem
bankTrialDurationAllKHeadChargeEstimateHolds is NOT proved.
No actual BANK-local counterexample is established.

For T <= B = (4b+6)(K+1)n, the exact requested charge is
a consequence of costWord_le_length. For every T there is
a head-conditioned T-budget and a 2^K rare-event bound.
The open T>B branch needs a head-conditioned worker charge;
the unconditional C.6 budgets do not imply it.
-/

/-- A word of length t can contain at most t correct HEAD labels. -/
theorem bankTrialSuccessHeadEventNeedsLength
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (w : List (Fin n)) (k : Nat)
        (z : BankTrialLocalState q),
      bankTrialProbabilityHeadEvent ring root w k z →
      k ≤ w.length := by
  intro w
  induction w with
  | nil =>
      intro k z h
      change k = 0 at h
      simp [h]
  | cons e tail ih =>
      intro k z h
      cases k with
      | zero =>
          exact Nat.zero_le _
      | succ k =>
          by_cases hg : BankTrialProbabilityArmedGate z
          · by_cases he : e = root
            · have ht :
                  bankTrialProbabilityHeadEvent ring root tail k
                    (bankTrialLocalNext ring root z e) := by
                simpa only [bankTrialProbabilityHeadEvent,
                  if_pos hg, if_pos he] using h
              have hb := ih k
                (bankTrialLocalNext ring root z e) ht
              simp only [List.length_cons]
              omega
            · by_cases hi : ring.rightNeighbor e = root
              · have hf : False := by
                  simpa only [bankTrialProbabilityHeadEvent,
                    if_pos hg, if_neg he, if_pos hi] using h
                exact False.elim hf
              · have ht :
                    bankTrialProbabilityHeadEvent ring root tail
                      (k + 1) (bankTrialLocalNext ring root z e) := by
                  simpa only [bankTrialProbabilityHeadEvent,
                    if_pos hg, if_neg he, if_neg hi] using h
                have hb := ih (k + 1)
                  (bankTrialLocalNext ring root z e) ht
                simp only [List.length_cons]
                omega
          · have ht :
                bankTrialProbabilityHeadEvent ring root tail
                  (k + 1) (bankTrialLocalNext ring root z e) := by
              simpa only [bankTrialProbabilityHeadEvent,
                if_neg hg] using h
            have hb := ih (k + 1)
              (bankTrialLocalNext ring root z e) ht
            simp only [List.length_cons]
            omega

/-- Exact all-K-head original-clock charge at a finite horizon:
costWord is no larger than the length-T scheduler word. -/
theorem bankTrialDurationAllKHeadCostLeHorizon
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) :
    bankTrialDurationAllKHeadCostMass ring root S T ≤
      T * bankTrialProbabilityHeadMass ring root
        (bankTrialLocalStart S) (compileAdvice q).K T := by
  calc
    bankTrialDurationAllKHeadCostMass ring root S T ≤
        Prob.scheduleSum n T (fun w =>
          w.length *
            (if bankTrialProbabilityHeadEvent ring root w
                (compileAdvice q).K (bankTrialLocalStart S)
             then 1 else 0)) := by
      unfold bankTrialDurationAllKHeadCostMass
      apply bankTrialProbabilityScheduleSumMono n T
      intro w
      by_cases he :
          bankTrialProbabilityHeadEvent ring root w
            (compileAdvice q).K (bankTrialLocalStart S)
      · simp only [if_pos he, Nat.mul_one]
        exact costWord_le_length
          (bankTrialLocalNext ring root)
          bankTrialLocalTerminal (bankTrialLocalStart S) w
      · simp only [if_neg he, Nat.mul_zero]
        exact Nat.le_refl _
    _ = T * bankTrialProbabilityHeadMass ring root
          (bankTrialLocalStart S) (compileAdvice q).K T := by
      rw [bankTrialSuccessScheduleSumLength]
      rfl

/-- The exact G12e charge for every horizon below its coefficient,
without needing any additional domain assumptions. -/
theorem bankTrialDurationAllKHeadChargeShortHorizon
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat)
    (hT : T ≤
      ((2 * (2 * (compileAdvice q).b + 2) + 2) *
        ((compileAdvice q).K + 1) * n)) :
    bankTrialDurationAllKHeadCostMass ring root S T ≤
      bankTrialProbabilityHeadMass ring root
        (bankTrialLocalStart S) (compileAdvice q).K T *
          ((2 * (2 * (compileAdvice q).b + 2) + 2) *
            ((compileAdvice q).K + 1) * n) := by
  calc
    bankTrialDurationAllKHeadCostMass ring root S T ≤
        T * bankTrialProbabilityHeadMass ring root
          (bankTrialLocalStart S) (compileAdvice q).K T :=
      bankTrialDurationAllKHeadCostLeHorizon ring root S T
    _ ≤
        ((2 * (2 * (compileAdvice q).b + 2) + 2) *
          ((compileAdvice q).K + 1) * n) *
          bankTrialProbabilityHeadMass ring root
            (bankTrialLocalStart S) (compileAdvice q).K T :=
      Nat.mul_le_mul_right _ hT
    _ = bankTrialProbabilityHeadMass ring root
          (bankTrialLocalStart S) (compileAdvice q).K T *
          ((2 * (2 * (compileAdvice q).b + 2) + 2) *
            ((compileAdvice q).K + 1) * n) :=
      Nat.mul_comm _ _

/-- An arithmetic rearrangement with opaque Nat factors, so
large compile-time powers never occur inside arithmetic tactics. -/
theorem bankTrialDurationHeadScaleAssoc (a t b : Nat) :
    a * (t * b) = t * (a * b) := by
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Valid for all horizons: the all-K-head first-hit cost mass
carries the same 2^K head-rarity factor as the event mass,
but still has a coefficient T rather than the target B. -/
theorem bankTrialDurationAllKHeadCostRareBound
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) :
    2 ^ (compileAdvice q).K *
      bankTrialDurationAllKHeadCostMass ring root S T ≤
        T * n ^ T := by
  have hcost :=
    bankTrialDurationAllKHeadCostLeHorizon ring root S T
  have hhead :=
    bankTrialProbabilityHeadMassBound ring hn root
      T (compileAdvice q).K (bankTrialLocalStart S)
  calc
    2 ^ (compileAdvice q).K *
        bankTrialDurationAllKHeadCostMass ring root S T ≤
      2 ^ (compileAdvice q).K *
        (T * bankTrialProbabilityHeadMass ring root
          (bankTrialLocalStart S) (compileAdvice q).K T) :=
      Nat.mul_le_mul_left _ hcost
    _ = T * (2 ^ (compileAdvice q).K *
        bankTrialProbabilityHeadMass ring root
          (bankTrialLocalStart S) (compileAdvice q).K T) :=
      bankTrialDurationHeadScaleAssoc _ _ _
    _ ≤ T * n ^ T := Nat.mul_le_mul_left _ hhead

end L3

#print axioms L3.bankTrialSuccessHeadEventNeedsLength
#print axioms L3.bankTrialDurationAllKHeadCostLeHorizon
#print axioms L3.bankTrialDurationAllKHeadChargeShortHorizon
#print axioms L3.bankTrialDurationHeadScaleAssoc
#print axioms L3.bankTrialDurationAllKHeadCostRareBound

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- An ARMED service whose first digit is zero goes directly to
CSTART, with no newly materialized actual-worker origin.
This is the precise physical exception to a head-to-origin
mapping; it is not a counterexample to the survival estimate. -/
theorem bankTrialDurationZeroBitHeadHasNoOrigin
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (z : BankTrialLocalState q)
    (hstart : BankTrialC5ArmedStart n q z)
    (hbit : bankTrialLiveWaveBit z.bank
      ⟨0, bankTrialWindowWidthPos q⟩ = false) :
    bankTrialLiveWaveRootMode
      (bankTrialLocalNext ring root z root).bank = .CSTART ∧
    (∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken
        (bankTrialLocalNext ring root z root).bank j = .E) ∧
    bankTrialC5ActualStarts ring root S z root = [] := by
  have hrow :=
    bankTrialC5ArmedHeadZeroCStart ring root z hstart hbit
  have hnomodes :
      ¬ ((bankTrialLiveWaveRootMode z.bank = .ARMED ∧
           bankTrialLiveWaveRootMode
             (bankTrialLocalNext ring root z root).bank = .IWAIT) ∨
          (bankTrialLiveWaveRootMode z.bank = .CSTART ∧
           bankTrialLiveWaveRootMode
             (bankTrialLocalNext ring root z root).bank = .CWAIT)) := by
    intro h
    rcases h with hi | hc
    · have hm := hi.2
      rw [hrow.cstart] at hm
      cases hm
    · have hm := hc.1
      rw [hstart.2.2.2.2.1] at hm
      cases hm
  have hlen := bankTrialC5ActualStartsZeroOfModes
    ring root root S z hnomodes
  have hnil :
      bankTrialC5ActualStarts ring root S z root = [] := by
    cases hs : bankTrialC5ActualStarts ring root S z root with
    | nil => rfl
    | cons o tail =>
        rw [hs] at hlen
        simp at hlen
  exact ⟨hrow.cstart, hrow.empty, hnil⟩

end L3

#print axioms L3.bankTrialDurationZeroBitHeadHasNoOrigin

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
K-head first-stop and exact cost decomposition.
This is NOT bankTrialDurationAllKHeadChargeEstimateHolds.
Every stop/cost uses the ORIGINAL Fin n scheduler tape. There is
no assumed independent worker experiment or C.8 charge.
-/

/-- K HEAD labels, once earned, survive arbitrary suffix letters
in the event predicate. This is a word-level fact, not a claim
about the BANK's eventual terminal outcome. -/
theorem bankTrialDurationKHeadEventAppend
    {n q : Nat} (ring : DirectedRing n) (root : Fin n) :
    ∀ (w suffix : List (Fin n))
      (k : Nat) (z : BankTrialLocalState q),
      bankTrialProbabilityHeadEvent ring root w k z →
      bankTrialProbabilityHeadEvent ring root
        (w ++ suffix) k z := by
  intro w
  induction w with
  | nil =>
      intro suffix k z h
      change k = 0 at h
      subst k
      cases suffix <;> simp [bankTrialProbabilityHeadEvent]
  | cons e w ih =>
      intro suffix k z h
      cases k with
      | zero =>
          simp [bankTrialProbabilityHeadEvent]
      | succ k =>
          by_cases hg : BankTrialProbabilityArmedGate z
          · by_cases he : e = root
            · have ht :
                  bankTrialProbabilityHeadEvent ring root w k
                    (bankTrialLocalNext ring root z e) := by
                simpa [bankTrialProbabilityHeadEvent, hg, he]
                  using h
              have htail := ih suffix k
                (bankTrialLocalNext ring root z e) ht
              simpa [bankTrialProbabilityHeadEvent, hg, he]
                using htail
            · by_cases hi : ring.rightNeighbor e = root
              · have hf : False := by
                  simpa [bankTrialProbabilityHeadEvent, hg, he, hi]
                    using h
                exact False.elim hf
              · have ht :
                    bankTrialProbabilityHeadEvent ring root w
                      (k + 1) (bankTrialLocalNext ring root z e) := by
                  simpa [bankTrialProbabilityHeadEvent, hg, he, hi]
                    using h
                have htail := ih suffix (k + 1)
                  (bankTrialLocalNext ring root z e) ht
                simpa [bankTrialProbabilityHeadEvent, hg, he, hi]
                  using htail
          · have ht :
                bankTrialProbabilityHeadEvent ring root w
                  (k + 1) (bankTrialLocalNext ring root z e) := by
              simpa [bankTrialProbabilityHeadEvent, hg] using h
            have htail := ih suffix (k + 1)
              (bankTrialLocalNext ring root z e) ht
            simpa [bankTrialProbabilityHeadEvent, hg] using htail

/-- The first moment a running original word records its K-th
HEAD is selected by Prob.firstStoppedPrefixes. The scanner
takes the earliest true prefix, so its Boolean need not be
prefix-free on later extensions. -/
noncomputable def bankTrialDurationKHeadCutStop
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (pre : List (Fin n)) (_ : BankTrialLocalState q) : Bool :=
  decide (bankTrialProbabilityHeadEvent ring root pre
    (compileAdvice q).K (bankTrialLocalStart S))

/-- An arbitrary Nat weight is sampled exactly once at the
first K-head stop, on the SAME complete word. -/
theorem bankTrialDurationKHeadNatStoppedExact
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (F : List (Fin n) → Nat) :
    ∀ (word pre : List (Fin n))
      (x : BankTrialLocalState q) (T : Nat),
      bankTrialSuccessNatStoppedWord
          (bankTrialLocalNext ring root)
          (bankTrialDurationKHeadCutStop ring root S)
          (fun cut _ _ suffix => F (cut ++ suffix))
          T pre x word =
        if bankTrialProbabilityHeadEvent ring root
          (pre ++ word) (compileAdvice q).K
          (bankTrialLocalStart S)
        then F (pre ++ word) else 0 := by
  intro word
  induction word with
  | nil =>
      intro pre x T
      by_cases hh :
          bankTrialProbabilityHeadEvent ring root pre
            (compileAdvice q).K (bankTrialLocalStart S)
      · simp [bankTrialSuccessNatStoppedWord,
          bankTrialDurationKHeadCutStop, hh]
      · simp [bankTrialSuccessNatStoppedWord,
          bankTrialDurationKHeadCutStop, hh]
  | cons e tail ih =>
      intro pre x T
      by_cases hh :
          bankTrialProbabilityHeadEvent ring root pre
            (compileAdvice q).K (bankTrialLocalStart S)
      · have hfull :=
          bankTrialDurationKHeadEventAppend ring root pre
            (e :: tail) (compileAdvice q).K
            (bankTrialLocalStart S) hh
        simp [bankTrialSuccessNatStoppedWord,
          bankTrialDurationKHeadCutStop, hh, hfull]
      · have hnext :
            bankTrialSuccessNatStoppedWord
              (bankTrialLocalNext ring root)
              (bankTrialDurationKHeadCutStop ring root S)
              (fun cut _ _ suffix => F (cut ++ suffix))
              T pre x (e :: tail) =
            bankTrialSuccessNatStoppedWord
              (bankTrialLocalNext ring root)
              (bankTrialDurationKHeadCutStop ring root S)
              (fun cut _ _ suffix => F (cut ++ suffix))
              (T - 1) (pre ++ [e])
              (bankTrialLocalNext ring root x e) tail := by
          simp [bankTrialSuccessNatStoppedWord,
            bankTrialDurationKHeadCutStop, hh]
        rw [hnext]
        simpa only [List.append_assoc, List.singleton_append]
          using ih (pre ++ [e])
            (bankTrialLocalNext ring root x e) (T - 1)

/-- Generic Nat-valued first-stop factorization, specialized
to the K-head stop. This applies to stopped costWord just as
it applies to a constant weight. -/
theorem bankTrialDurationKHeadWeightedCutFactorization
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (F : List (Fin n) → Nat) (T : Nat) :
    Prob.scheduleSum n T (fun word =>
      if bankTrialProbabilityHeadEvent ring root word
          (compileAdvice q).K (bankTrialLocalStart S)
      then F word else 0) =
    ((Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root)
      (bankTrialDurationKHeadCutStop ring root S)
      T [] (bankTrialLocalStart S)).map (fun cut =>
        Prob.scheduleSum n (T - cut.length) (fun suffix =>
          F (cut ++ suffix)))).sum := by
  calc
    Prob.scheduleSum n T (fun word =>
        if bankTrialProbabilityHeadEvent ring root word
            (compileAdvice q).K (bankTrialLocalStart S)
        then F word else 0) =
      Prob.scheduleSum n T (fun word =>
        bankTrialSuccessNatStoppedWord
          (bankTrialLocalNext ring root)
          (bankTrialDurationKHeadCutStop ring root S)
          (fun cut _ _ suffix => F (cut ++ suffix))
          T [] (bankTrialLocalStart S) word) := by
            apply congrArg (Prob.scheduleSum n T)
            funext word
            simpa only [List.nil_append] using
              (bankTrialDurationKHeadNatStoppedExact
                ring root S F word []
                (bankTrialLocalStart S) T).symm
    _ = _ :=
      bankTrialSuccessNatStoppedFactorizationLocal
        ring root
        (bankTrialDurationKHeadCutStop ring root S)
        (fun cut _ _ suffix => F (cut ++ suffix))
        (bankTrialLocalStart S) T

/-- Exact HEAD mass: one first K-head prefix p contributes
n^(T-|p|) original-scheduler extensions. -/
theorem bankTrialDurationKHeadMassCutFactorization
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) :
    bankTrialProbabilityHeadMass ring root
      (bankTrialLocalStart S) (compileAdvice q).K T =
    ((Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root)
      (bankTrialDurationKHeadCutStop ring root S)
      T [] (bankTrialLocalStart S)).map (fun cut =>
        n ^ (T - cut.length))).sum := by
  change Prob.scheduleSum n T (fun word =>
      if bankTrialProbabilityHeadEvent ring root word
        (compileAdvice q).K (bankTrialLocalStart S)
      then 1 else 0) = _
  rw [bankTrialDurationKHeadWeightedCutFactorization
    ring root S (fun _ => 1) T]
  apply bankTrialSuccessCutHistoryMapSumExt
  intro cut
  simpa only [Nat.mul_one] using
    (bankTrialProbabilityScheduleSumConst
      n (T - cut.length) 1)

/-- Exact all-K-head cost mass on the same first-stop cut list.
No fresh suffix experiment or independence is introduced. -/
theorem bankTrialDurationKHeadCostCutFactorization
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) :
    bankTrialDurationAllKHeadCostMass ring root S T =
    ((Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root)
      (bankTrialDurationKHeadCutStop ring root S)
      T [] (bankTrialLocalStart S)).map (fun cut =>
        Prob.scheduleSum n (T - cut.length) (fun suffix =>
          costWord (bankTrialLocalNext ring root)
            bankTrialLocalTerminal (bankTrialLocalStart S)
            (cut ++ suffix)))).sum := by
  change Prob.scheduleSum n T (fun word =>
      if bankTrialProbabilityHeadEvent ring root word
        (compileAdvice q).K (bankTrialLocalStart S) then
          costWord (bankTrialLocalNext ring root)
            bankTrialLocalTerminal (bankTrialLocalStart S) word
      else 0) = _
  exact bankTrialDurationKHeadWeightedCutFactorization
    ring root S
    (fun word => costWord (bankTrialLocalNext ring root)
      bankTrialLocalTerminal (bankTrialLocalStart S) word) T

/-- Deterministic stopped-cost concatenation with the actual
BANK state at the cut, including early terminal prefixes. -/
theorem bankTrialDurationKHeadCostAppendLe
    {n q : Nat} (ring : DirectedRing n) (root : Fin n) :
    ∀ (pre suffix : List (Fin n))
      (z : BankTrialLocalState q),
      costWord (bankTrialLocalNext ring root)
        bankTrialLocalTerminal z (pre ++ suffix) ≤
      pre.length +
        costWord (bankTrialLocalNext ring root)
          bankTrialLocalTerminal
          (bankTrialLocalRun ring root pre z) suffix := by
  intro pre
  induction pre with
  | nil =>
      intro suffix z
      simp only [List.nil_append, List.length_nil,
        Nat.zero_add, bankTrialLocalRun]
      exact Nat.le_refl _
  | cons e pre ih =>
      intro suffix z
      by_cases ht : bankTrialLocalTerminal z
      · have hz :=
          costWord_terminal
            (bankTrialLocalNext ring root)
            bankTrialLocalTerminal z ht ((e :: pre) ++ suffix)
        rw [hz]
        exact Nat.zero_le _
      · have hstep :
            costWord (bankTrialLocalNext ring root)
                bankTrialLocalTerminal z
                ((e :: pre) ++ suffix) =
            1 + costWord (bankTrialLocalNext ring root)
                bankTrialLocalTerminal
                (bankTrialLocalNext ring root z e)
                (pre ++ suffix) := by
                  simp only [List.cons_append, costWord,
                    K2FiniteSafeEliminationExpected.rawCost,
                    if_neg ht]
        have htail := ih suffix
          (bankTrialLocalNext ring root z e)
        calc
          costWord (bankTrialLocalNext ring root)
              bankTrialLocalTerminal z
              ((e :: pre) ++ suffix) =
            1 + costWord (bankTrialLocalNext ring root)
              bankTrialLocalTerminal
              (bankTrialLocalNext ring root z e)
              (pre ++ suffix) := hstep
          _ ≤ 1 + (pre.length +
              costWord (bankTrialLocalNext ring root)
                bankTrialLocalTerminal
                (bankTrialLocalRun ring root pre
                  (bankTrialLocalNext ring root z e))
                suffix) := Nat.add_le_add_left htail 1
          _ = (e :: pre).length +
              costWord (bankTrialLocalNext ring root)
                bankTrialLocalTerminal
                (bankTrialLocalRun ring root (e :: pre) z)
                suffix := by
                  simp only [List.length_cons, bankTrialLocalRun]
                  omega

/-- Core list-map monotonicity for the cut-sum estimate. -/
theorem bankTrialDurationKHeadCutListSumMono
    {A : Type} (xs : List A) (f g : A → Nat)
    (h : ∀ x, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h x) ih

/-- Exact original-tape pre-cut and post-cut bound, BEFORE bounding
the terminal-time mean at the authenticated post-head state. -/
theorem bankTrialDurationKHeadCostCutDecomposition
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) :
    bankTrialDurationAllKHeadCostMass ring root S T ≤
    ((Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root)
      (bankTrialDurationKHeadCutStop ring root S)
      T [] (bankTrialLocalStart S)).map (fun cut =>
        cut.length * n ^ (T - cut.length) +
        costNumerator (bankTrialLocalNext ring root)
          bankTrialLocalTerminal
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) (T - cut.length))).sum := by
  rw [bankTrialDurationKHeadCostCutFactorization]
  apply bankTrialDurationKHeadCutListSumMono
  intro cut
  have hbound :
      Prob.scheduleSum n (T - cut.length) (fun suffix =>
        costWord (bankTrialLocalNext ring root)
          bankTrialLocalTerminal (bankTrialLocalStart S)
          (cut ++ suffix)) ≤
      Prob.scheduleSum n (T - cut.length) (fun suffix =>
        cut.length +
          costWord (bankTrialLocalNext ring root)
            bankTrialLocalTerminal
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) suffix) :=
    bankTrialProbabilityScheduleSumMono n (T - cut.length)
      _ _ (fun suffix =>
        bankTrialDurationKHeadCostAppendLe
          ring root cut suffix (bankTrialLocalStart S))
  calc
    Prob.scheduleSum n (T - cut.length) (fun suffix =>
        costWord (bankTrialLocalNext ring root)
          bankTrialLocalTerminal (bankTrialLocalStart S)
          (cut ++ suffix)) ≤
      Prob.scheduleSum n (T - cut.length) (fun suffix =>
        cut.length +
          costWord (bankTrialLocalNext ring root)
            bankTrialLocalTerminal
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)) suffix) := hbound
    _ = cut.length * n ^ (T - cut.length) +
        costNumerator (bankTrialLocalNext ring root)
          bankTrialLocalTerminal
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) (T - cut.length) := by
            rw [bankTrialC5ScheduleSumAdd,
              bankTrialProbabilityScheduleSumConst]
            rw [Nat.mul_comm (n ^ (T - cut.length)) cut.length]
            rfl

/-- Original n-edge first-letter recursion, as a reusable
expression for its true per-edge HEAD masses. -/
noncomputable def bankTrialDurationKHeadChildMass
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q) (k T : Nat) (e : Fin n) : Nat :=
  if BankTrialProbabilityArmedGate z then
    if e = root then
      bankTrialProbabilityHeadMass ring root
        (bankTrialLocalNext ring root z e) k T
    else if ring.rightNeighbor e = root then 0
    else bankTrialProbabilityHeadMass ring root
      (bankTrialLocalNext ring root z e) (k + 1) T
  else bankTrialProbabilityHeadMass ring root
    (bankTrialLocalNext ring root z e) (k + 1) T


/-- Correct-head mass grows by at least one full extra
scheduler letter: n * HeadMass(k,T) <= HeadMass(k,T+1).
No assumption on cleanliness or threshold is required. -/
theorem bankTrialDurationKHeadMassStepMono
    {n q : Nat} (ring : DirectedRing n) (root : Fin n) :
    ∀ (T k : Nat) (z : BankTrialLocalState q),
      n * bankTrialProbabilityHeadMass ring root z k T ≤
        bankTrialProbabilityHeadMass ring root z k (T + 1) := by
  intro T
  induction T with
  | zero =>
      intro k z
      cases k with
      | zero =>
          rw [bankTrialProbabilityHeadMassZero,
            bankTrialProbabilityHeadMassZero]
          simp
      | succ k =>
          have hzero :
              bankTrialProbabilityHeadMass ring root z
                (k + 1) 0 = 0 := by
            unfold bankTrialProbabilityHeadMass
            rw [bankTrialProbabilityScheduleSumZero]
            simp [bankTrialProbabilityHeadEvent]
          rw [hzero, Nat.mul_zero]
          exact Nat.zero_le _
  | succ T ih =>
      intro k z
      cases k with
      | zero =>
          rw [bankTrialProbabilityHeadMassZero,
            bankTrialProbabilityHeadMassZero]
          apply Nat.le_of_eq
          calc
            n * n ^ (T + 1) =
              n ^ (T + 1) * n := Nat.mul_comm _ _
            _ = n ^ ((T + 1) + 1) :=
              (Nat.pow_succ n (T + 1)).symm
      | succ k =>
          have hchild (e : Fin n) :
              n * bankTrialDurationKHeadChildMass
                ring root z k T e ≤
              bankTrialDurationKHeadChildMass
                ring root z k (T + 1) e := by
            unfold bankTrialDurationKHeadChildMass
            by_cases hg : BankTrialProbabilityArmedGate z
            · by_cases he : e = root
              · simp only [if_pos hg, if_pos he]
                exact ih k (bankTrialLocalNext ring root z e)
              · by_cases hr : ring.rightNeighbor e = root
                · simp only [if_pos hg, if_neg he, if_pos hr,
                    Nat.mul_zero]
                  exact Nat.zero_le _
                · simp only [if_pos hg, if_neg he, if_neg hr]
                  exact ih (k + 1)
                    (bankTrialLocalNext ring root z e)
            · simp only [if_neg hg]
              exact ih (k + 1)
                (bankTrialLocalNext ring root z e)
          have hsum := ofFn_sum_le
            (fun e : Fin n =>
              n * bankTrialDurationKHeadChildMass
                ring root z k T e)
            (fun e : Fin n =>
              bankTrialDurationKHeadChildMass
                ring root z k (T + 1) e) hchild
          calc
            n * bankTrialProbabilityHeadMass ring root z
                (k + 1) (T + 1) =
              (List.ofFn (fun e : Fin n =>
                n * bankTrialDurationKHeadChildMass
                  ring root z k T e)).sum := by
                    rw [bankTrialProbabilityHeadMassSucc
                      ring root z k T]
                    exact (ofFn_sum_mul_left n
                      (bankTrialDurationKHeadChildMass
                        ring root z k T)).symm
            _ ≤ (List.ofFn (fun e : Fin n =>
                  bankTrialDurationKHeadChildMass
                    ring root z k (T + 1) e)).sum := hsum
            _ = bankTrialProbabilityHeadMass ring root z
                  (k + 1) ((T + 1) + 1) := by
                    rw [bankTrialProbabilityHeadMassSucc
                      ring root z k (T + 1)]
                    rfl


/-- Every spatial-band CLEAN-start WON word authenticates
all K HEAD labels; their exact finite-word mass is included. -/
theorem bankTrialDurationKHeadWinMassLeHeadMass
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hsmall : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (T : Nat) :
    bankTrialProbabilityWinMass ring root S T ≤
      bankTrialProbabilityHeadMass ring root
        (bankTrialLocalStart S) (compileAdvice q).K T := by
  unfold bankTrialProbabilityWinMass
    bankTrialProbabilityHeadMass
  apply bankTrialProbabilityScheduleSumMono n T
  intro w
  by_cases hw :
      (bankTrialLocalRun ring root w
        (bankTrialLocalStart S)).phase = .won
  · have hh := bankTrialDurationWinHasAllHeads
      ring root S hclean hsmall hlarge w hw
    simp only [if_pos hw, if_pos hh]
    exact Nat.le_refl _
  · simp only [if_neg hw]
    exact Nat.zero_le _


/-- G11c's 1023/1024 lower success certificate transfers
to HEAD mass, and the same original-clock bound holds at
every LATER horizon. No probability-one limit is claimed. -/
theorem bankTrialDurationKHeadNearFairEventually
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsmall : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    ∃ Tstar : Nat, ∀ T : Nat, Tstar ≤ T →
      1023 * n ^ T ≤
        (1024 * 2 ^ (compileAdvice q).K) *
          bankTrialProbabilityHeadMass ring root
            (bankTrialLocalStart S) (compileAdvice q).K T := by
  have htheta := bankTrialSuccessThetaLowerHolds ring root S
  obtain ⟨Tstar, hstar⟩ :=
    htheta hsmall hlarge hwidth hclean
  have hwin :=
    bankTrialDurationKHeadWinMassLeHeadMass
      ring root S hclean hsmall hlarge Tstar
  have hbase :
      1023 * n ^ Tstar ≤
        (1024 * 2 ^ (compileAdvice q).K) *
          bankTrialProbabilityHeadMass ring root
            (bankTrialLocalStart S) (compileAdvice q).K
            Tstar := by
    exact Nat.le_trans hstar
      (Nat.mul_le_mul_left
        (1024 * 2 ^ (compileAdvice q).K) hwin)
  have hind : ∀ r : Nat,
      1023 * n ^ (Tstar + r) ≤
        (1024 * 2 ^ (compileAdvice q).K) *
          bankTrialProbabilityHeadMass ring root
            (bankTrialLocalStart S) (compileAdvice q).K
            (Tstar + r) := by
    intro r
    induction r with
    | zero =>
        simpa only [Nat.add_zero] using hbase
    | succ r ih =>
        have hmass :=
          bankTrialDurationKHeadMassStepMono ring root
            (Tstar + r) (compileAdvice q).K
            (bankTrialLocalStart S)
        have hscaled :=
          Nat.mul_le_mul_left
            (1024 * 2 ^ (compileAdvice q).K) hmass
        have hidx : Tstar + (r + 1) =
            (Tstar + r) + 1 := by omega
        rw [hidx]
        calc
          1023 * n ^ ((Tstar + r) + 1) =
              n * (1023 * n ^ (Tstar + r)) := by
                rw [Nat.pow_succ]
                simp only [Nat.mul_assoc, Nat.mul_comm,
                  Nat.mul_left_comm]
          _ ≤ n * ((1024 * 2 ^ (compileAdvice q).K) *
              bankTrialProbabilityHeadMass ring root
                (bankTrialLocalStart S) (compileAdvice q).K
                (Tstar + r)) :=
            Nat.mul_le_mul_left n ih
          _ ≤ (1024 * 2 ^ (compileAdvice q).K) *
              bankTrialProbabilityHeadMass ring root
                (bankTrialLocalStart S) (compileAdvice q).K
                ((Tstar + r) + 1) := by
                  simpa only [Nat.mul_assoc, Nat.mul_comm,
                    Nat.mul_left_comm] using hscaled
  refine ⟨Tstar, ?_⟩
  intro T hT
  obtain ⟨r, hr⟩ :
      ∃ r : Nat, T = Tstar + r :=
    ⟨T - Tstar, by omega⟩
  rw [hr]
  exact hind r


/-- The combined worker-rank coefficient and recovery
coefficient add to 8b+11. This is scalar arithmetic and
does not establish a uniform post-cut cost. -/
theorem bankTrialDurationKHeadPostCoefficient
    (b n : Nat) :
    (2 * (2 * b + 2) + 1) * n +
      (2 * (2 * b + 2) + 2) * n =
      (8 * b + 11) * n := by
  have hc :
      (2 * (2 * b + 2) + 1) +
        (2 * (2 * b + 2) + 2) = 8 * b + 11 := by
    omega
  calc
    (2 * (2 * b + 2) + 1) * n +
        (2 * (2 * b + 2) + 2) * n =
      ((2 * (2 * b + 2) + 1) +
        (2 * (2 * b + 2) + 2)) * n := by
          exact (Nat.add_mul _ _ _).symm
    _ = (8 * b + 11) * n := by rw [hc]


/-- If M'=n*M+d and R'=n*R+(T+1)*d, then the
conditional stopped-cut length ratio is nondecreasing,
expressed without Nat division. The missing original-word
recurrences are NOT presumed here. -/
theorem bankTrialDurationKHeadRatioGrowthArithmetic
    (n T m r d : Nat) (hbound : r ≤ T * m) :
    r * (n * m + d) ≤
      (n * r + (T + 1) * d) * m := by
  have hcross :
      (T * m) * d ≤ ((T + 1) * d) * m := by
    calc
      (T * m) * d = T * (d * m) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ (T + 1) * (d * m) :=
        Nat.mul_le_mul_right (d * m) (Nat.le_succ T)
      _ = ((T + 1) * d) * m := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  calc
    r * (n * m + d) = (n * r) * m + r * d := by
      simp only [Nat.mul_add, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (n * r) * m + (T * m) * d :=
      Nat.add_le_add_left (Nat.mul_le_mul_right d hbound) _
    _ ≤ (n * r) * m + ((T + 1) * d) * m :=
      Nat.add_le_add_left hcross _
    _ = (n * r + (T + 1) * d) * m := by
      exact (Nat.add_mul _ _ _).symm


/-- At b=256,K=2, the fixed 1023/1024 near-fair
fraction is not enough to absorb the proposed pre-cut
mean under the revised c_post. THIS IS ONLY a numerical
counterexample to that particular proof inequality,
not a BANK word-level refutation of the C.8 target. -/
theorem bankTrialDurationKHeadFixedThetaMarginCounter :
    ¬ (∀ b K : Nat, 17 ≤ b → 1 ≤ K →
      1024 * (K + 2 * (K - 1) * (4 * b + 5)) ≤
        2 * 1023 *
          (((4 * b + 6) * (K + 1)) - (8 * b + 11))) := by
  intro h
  have hbad := h 256 2 (by decide) (by decide)
  change (2109440 : Nat) ≤ 2109426 at hbad
  omega


/-- REPLACEMENT of the pre-cut specification. The prospective
post-cut coefficient is the sum of the *combined* class-one
worker rank (4b+5)n and the recovery budget (4b+6)n.
This definition does NOT prove the post-cut bound. -/
def BankTrialDurationKHeadCutLengthCharge
    {n q : Nat} (ring : DirectedRing n)
    (root : Fin n) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    BankTrialLocalClean q S →
    (compileAdvice q).useSmall = false →
    2 * (compileAdvice q).bankLeaseCap ≤ n →
    ∀ T : Nat,
      ((Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        (bankTrialDurationKHeadCutStop ring root S)
        T [] (bankTrialLocalStart S)).map (fun cut =>
          cut.length * n ^ (T - cut.length))).sum ≤
        bankTrialProbabilityHeadMass ring root
          (bankTrialLocalStart S) (compileAdvice q).K T *
          (((6 * (compileAdvice q).b + 9) *
            ((compileAdvice q).K + 1) * n) -
           ((8 * (compileAdvice q).b + 11) * n))

end L3

#print axioms L3.bankTrialDurationKHeadEventAppend
#print axioms L3.bankTrialDurationKHeadNatStoppedExact
#print axioms L3.bankTrialDurationKHeadWeightedCutFactorization
#print axioms L3.bankTrialDurationKHeadMassCutFactorization
#print axioms L3.bankTrialDurationKHeadCostCutFactorization
#print axioms L3.bankTrialDurationKHeadCostAppendLe
#print axioms L3.bankTrialDurationKHeadCutListSumMono
#print axioms L3.bankTrialDurationKHeadCostCutDecomposition
#print axioms L3.bankTrialDurationKHeadMassStepMono
#print axioms L3.bankTrialDurationKHeadWinMassLeHeadMass
#print axioms L3.bankTrialDurationKHeadNearFairEventually
#print axioms L3.bankTrialDurationKHeadPostCoefficient
#print axioms L3.bankTrialDurationKHeadRatioGrowthArithmetic
#print axioms L3.bankTrialDurationKHeadFixedThetaMarginCounter

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The part of the K-head subdistribution which is LOST at the
original final horizon. This is not the unconditional failure mass. -/
noncomputable def bankTrialDurationKHeadLostMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) : Nat :=
  Prob.scheduleSum n T (fun w =>
    if bankTrialProbabilityHeadEvent ring root w
        (compileAdvice q).K (bankTrialLocalStart S) ∧
      (bankTrialLocalRun ring root w
        (bankTrialLocalStart S)).phase = .lost
    then 1 else 0)

/-- A pointwise outcome partition WITH the head predicate on the
LOST summand. No CLEAN invariant is used here. -/
theorem bankTrialDurationHeadEventOutcomeCover {q : Nat}
    (z : BankTrialLocalState q) (h : Prop) :
    (if h then 1 else 0) ≤
      (if z.phase = .won then 1 else 0) +
        ((if bankTrialLocalTerminal z then 0 else 1) +
          (if h ∧ z.phase = .lost then 1 else 0)) := by
  classical
  cases z with
  | mk bank phase =>
      cases phase <;> by_cases hh : h <;>
        simp [bankTrialLocalTerminal, hh]

/-- H <= W + A + L at EVERY horizon. The loss term is conditioned
on the very same adapted K-head event. -/
theorem bankTrialDurationKHeadCoveredByResolvedMass
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) :
    bankTrialProbabilityHeadMass ring root
        (bankTrialLocalStart S) (compileAdvice q).K T ≤
      bankTrialProbabilityWinMass ring root S T +
        (bankTrialDurationActiveMass ring root S T +
          bankTrialDurationKHeadLostMass ring root S T) := by
  unfold bankTrialProbabilityHeadMass
    bankTrialProbabilityWinMass bankTrialDurationActiveMass
    bankTrialDurationKHeadLostMass
  calc
    Prob.scheduleSum n T (fun w =>
        if bankTrialProbabilityHeadEvent ring root w
          (compileAdvice q).K (bankTrialLocalStart S)
        then 1 else 0) ≤
      Prob.scheduleSum n T (fun w =>
        (if (bankTrialLocalRun ring root w
          (bankTrialLocalStart S)).phase = .won
        then 1 else 0) +
        ((if bankTrialLocalTerminal
          (bankTrialLocalRun ring root w
            (bankTrialLocalStart S))
        then 0 else 1) +
        (if bankTrialProbabilityHeadEvent ring root w
              (compileAdvice q).K (bankTrialLocalStart S) ∧
            (bankTrialLocalRun ring root w
              (bankTrialLocalStart S)).phase = .lost
         then 1 else 0))) := by
           apply bankTrialProbabilityScheduleSumMono n T
           intro w
           exact bankTrialDurationHeadEventOutcomeCover
             (bankTrialLocalRun ring root w
               (bankTrialLocalStart S))
             (bankTrialProbabilityHeadEvent ring root w
               (compileAdvice q).K (bankTrialLocalStart S))
    _ = Prob.scheduleSum n T (fun w =>
          if (bankTrialLocalRun ring root w
            (bankTrialLocalStart S)).phase = .won
          then 1 else 0) +
        (Prob.scheduleSum n T (fun w =>
          if bankTrialLocalTerminal
            (bankTrialLocalRun ring root w
              (bankTrialLocalStart S))
          then 0 else 1) +
         Prob.scheduleSum n T (fun w =>
          if bankTrialProbabilityHeadEvent ring root w
                (compileAdvice q).K (bankTrialLocalStart S) ∧
              (bankTrialLocalRun ring root w
                (bankTrialLocalStart S)).phase = .lost
          then 1 else 0)) := by
            rw [bankTrialC5ScheduleSumAdd T]
            rw [bankTrialC5ScheduleSumAdd T]

/-- OPAQUE Nat budget extraction. This theorem contains no giant
advice powers; instantiate it only after they have been packaged
into N and D. -/
theorem bankTrialDurationPostHeadMargin
    (K N D : Nat)
    (h : 2048 * (2 * K + 1) * N < D) :
    0 < D ∧ 8 * N ≤ D := by
  have hfactor : 8 ≤ 2048 * (2 * K + 1) := by omega
  have hscaled : 8 * N ≤
      2048 * (2 * K + 1) * N :=
    Nat.mul_le_mul_right N hfactor
  constructor <;> omega

/-- Arithmetic closure: D*L <= 2*N*H and 8*N <= D give
3*H <= 4*B, provided H <= B+L. The proof never divides Nat
masses and never assumes independence. -/
theorem bankTrialDurationPostHeadSurvivalArithmetic
    (D N H B L : Nat)
    (hpositive : 0 < D)
    (hmargin : 8 * N ≤ D)
    (hpartition : H ≤ B + L)
    (hcharge : D * L ≤ (2 * N) * H) :
    3 * H ≤ 4 * B := by
  have hbase : D * H ≤ D * B + D * L := by
    calc
      D * H ≤ D * (B + L) :=
        Nat.mul_le_mul_left D hpartition
      _ = D * B + D * L := Nat.mul_add D B L
  have hfour :
      4 * (D * H) ≤ 4 * (D * B) + 4 * (D * L) := by
    calc
      4 * (D * H) ≤ 4 * (D * B + D * L) :=
        Nat.mul_le_mul_left 4 hbase
      _ = 4 * (D * B) + 4 * (D * L) :=
        Nat.mul_add 4 (D * B) (D * L)
  have hrare : 4 * (D * L) ≤ D * H := by
    calc
      4 * (D * L) ≤ 4 * ((2 * N) * H) :=
        Nat.mul_le_mul_left 4 hcharge
      _ = (8 * N) * H :=
        (Nat.mul_assoc 4 (2 * N) H).symm.trans
          (by rw [show 4 * (2 * N) = 8 * N by omega])
      _ ≤ D * H := Nat.mul_le_mul_right H hmargin
  have hcancel : 3 * (D * H) ≤ 4 * (D * B) := by
    have htotal : 4 * (D * H) ≤
        4 * (D * B) + D * H :=
      Nat.le_trans hfour
        (Nat.add_le_add_left hrare (4 * (D * B)))
    omega
  have hmul : D * (3 * H) ≤ D * (4 * B) := by
    simpa only [Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using hcancel
  exact Nat.le_of_mul_le_mul_left hmul hpositive

/-- Select only actual launches whose POSTservice head ledger is K.
This deliberately includes a K-th-head ARMED -> IWAIT launch and
a later CSTART -> CWAIT launch; it does NOT pretend that a zero-bit
ARMED -> CSTART head has an origin. -/
noncomputable def bankTrialDurationKHeadActualStarts {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (z : BankTrialLocalState q) (e : Fin n) :
    List (BankTrialC5ActualOrigin n q) :=
  (bankTrialC5ActualStarts ring root S z e).filter
    (fun o => o.heads == (compileAdvice q).K)

/-- The proved C.5 kernel gives the same C.1 rarity for K-tagged
launches, because filtering cannot introduce any new origin. -/
theorem bankTrialDurationKHeadActualRarity
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    BankTrialProbabilityC5WorkerRarity ring root
      (bankTrialDurationKHeadActualStarts ring root S)
      (bankTrialC5ActualTimeout ring root) := by
  have hkernel := bankTrialC5ActualWorkerExcursionKernelHolds
    ring root S hsp hlarge hwidth hclean
  change Prob.OriginRarity bankTrialLocalTerminal
    (bankTrialDurationKHeadActualStarts ring root S)
    (bankTrialC5ActualTimeout ring root)
    (bankTrialProbabilityC5WorkerNumerator q)
    (bankTrialProbabilityC5WorkerDenominator q)
  intro z hnonterminal e o ho T
  have hsource : o ∈ bankTrialC5ActualStarts
      ring root S z e := by
    unfold bankTrialDurationKHeadActualStarts at ho
    exact (List.mem_filter.mp ho).1
  exact hkernel.conditionalRarity
    z hnonterminal e o hsource T

/-- TWO STILL-OPEN, deterministic original-tape obligations:
(1) every K-head LOST word is covered by a K-indexed origin's
first-exit timeout;
(2) on every word, the number of K-indexed launches is at most
two, and no such launch appears before the K-head event.

Both assertions are deliberately explicit rather than smuggled
into the conditional-rarity theorem. -/
def BankTrialDurationKHeadPostLaunchCensus {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  ∀ T : Nat,
    bankTrialDurationKHeadLostMass ring root S T ≤
      Prob.originEventNumerator
        (bankTrialLocalNext ring root) bankTrialLocalTerminal
        (bankTrialDurationKHeadActualStarts ring root S)
        (bankTrialC5ActualTimeout ring root)
        (bankTrialLocalStart S) T ∧
    Prob.originsNumerator
        (bankTrialLocalNext ring root) bankTrialLocalTerminal
        (bankTrialDurationKHeadActualStarts ring root S)
        (bankTrialLocalStart S) T ≤
      2 * bankTrialProbabilityHeadMass ring root
        (bankTrialLocalStart S) (compileAdvice q).K T

/-- This is the conditional K-head loss charge, derived from the
actual origin rarity with no resampling. It requires ONLY the two
deterministic census clauses just isolated above. -/
theorem bankTrialDurationKHeadLostChargeOfCensus
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hcensus : BankTrialDurationKHeadPostLaunchCensus
      ring root S) (T : Nat) :
    bankTrialProbabilityC5WorkerDenominator q *
      bankTrialDurationKHeadLostMass ring root S T ≤
    (2 * bankTrialProbabilityC5WorkerNumerator q) *
      bankTrialProbabilityHeadMass ring root
        (bankTrialLocalStart S) (compileAdvice q).K T := by
  have hrare := bankTrialDurationKHeadActualRarity
    ring root S hsp hlarge hwidth hclean
  have horigin := Prob.origin_counting_le
    (bankTrialLocalNext ring root) bankTrialLocalTerminal
    (bankTrialDurationKHeadActualStarts ring root S)
    (bankTrialC5ActualTimeout ring root)
    (bankTrialProbabilityC5WorkerNumerator q)
    (bankTrialProbabilityC5WorkerDenominator q)
    hrare (bankTrialLocalStart S) T
  have hcover := (hcensus T).1
  have hcount := (hcensus T).2
  calc
    bankTrialProbabilityC5WorkerDenominator q *
        bankTrialDurationKHeadLostMass ring root S T ≤
      bankTrialProbabilityC5WorkerDenominator q *
        Prob.originEventNumerator
          (bankTrialLocalNext ring root) bankTrialLocalTerminal
          (bankTrialDurationKHeadActualStarts ring root S)
          (bankTrialC5ActualTimeout ring root)
          (bankTrialLocalStart S) T :=
        Nat.mul_le_mul_left _ hcover
    _ ≤ bankTrialProbabilityC5WorkerNumerator q *
        Prob.originsNumerator
          (bankTrialLocalNext ring root) bankTrialLocalTerminal
          (bankTrialDurationKHeadActualStarts ring root S)
          (bankTrialLocalStart S) T := horigin
    _ ≤ bankTrialProbabilityC5WorkerNumerator q *
        (2 * bankTrialProbabilityHeadMass ring root
          (bankTrialLocalStart S) (compileAdvice q).K T) :=
        Nat.mul_le_mul_left _ hcount
    _ = (2 * bankTrialProbabilityC5WorkerNumerator q) *
        bankTrialProbabilityHeadMass ring root
          (bankTrialLocalStart S) (compileAdvice q).K T := by
            simp only [Nat.mul_assoc, Nat.mul_comm,
              Nat.mul_left_comm]

/-- CONDITIONAL SURVIVAL CLOSURE, NOT THE TARGET "Holds".
To get the unconditional C.8 survival theorem one must prove the
deterministic post-launch census; no such proof is claimed here. -/
theorem bankTrialDurationAllKHeadSurvivalOfCensus
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hcensus : ∀ (S : GrantBankReference.BankLocalReference
        (compileAdvice q).b),
      BankTrialLocalClean q S →
      (compileAdvice q).useSmall = false →
      2 * (compileAdvice q).bankLeaseCap ≤ n →
      BankTrialDurationKHeadPostLaunchCensus ring root S) :
    BankTrialDurationAllKHeadSurvivalEstimate
      (q := q) ring root := by
  intro S hclean hsp hlarge T
  have hbudget := bankTrialSuccessDoubledWorkerBudget
    q hsp hwidth
  have hmargin := bankTrialDurationPostHeadMargin
    (compileAdvice q).K
    (bankTrialProbabilityC5WorkerNumerator q)
    (bankTrialProbabilityC5WorkerDenominator q) hbudget
  have hpartition := bankTrialDurationKHeadCoveredByResolvedMass
    ring root S T
  have hcharge := bankTrialDurationKHeadLostChargeOfCensus
    ring root S hsp hlarge hwidth hclean
    (hcensus S hclean hsp hlarge) T
  exact bankTrialDurationPostHeadSurvivalArithmetic
    (bankTrialProbabilityC5WorkerDenominator q)
    (bankTrialProbabilityC5WorkerNumerator q)
    (bankTrialProbabilityHeadMass ring root
      (bankTrialLocalStart S) (compileAdvice q).K T)
    (bankTrialProbabilityWinMass ring root S T +
      bankTrialDurationActiveMass ring root S T)
    (bankTrialDurationKHeadLostMass ring root S T)
    hmargin.1 hmargin.2 (by rw [Nat.add_assoc]; exact hpartition) hcharge

end L3

#print axioms L3.bankTrialDurationHeadEventOutcomeCover
#print axioms L3.bankTrialDurationKHeadCoveredByResolvedMass
#print axioms L3.bankTrialDurationPostHeadMargin
#print axioms L3.bankTrialDurationPostHeadSurvivalArithmetic
#print axioms L3.bankTrialDurationKHeadActualRarity
#print axioms L3.bankTrialDurationKHeadLostChargeOfCensus
#print axioms L3.bankTrialDurationAllKHeadSurvivalOfCensus

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The existing filter selects exactly the C.5 actual origins
whose AFTER-bank carry tag equals K. -/
theorem bankTrialDurationKHeadSelectedTag
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialDurationKHeadActualStarts ring root S x e) :
    o ∈ bankTrialC5ActualStarts ring root S x e ∧
      o.heads = (compileAdvice q).K := by
  unfold bankTrialDurationKHeadActualStarts at ho
  have hs := List.mem_filter.mp ho
  exact ⟨hs.1, Eq.mp
    (Nat.beq_eq_true_eq o.heads (compileAdvice q).K) hs.2⟩

/-- A K-tagged increment is launched on the K-th ARMED outgoing
head; a K-tagged comparator is launched after K heads have
already been counted. In neither case is its tag a pre-increment
K-1 value. -/
theorem bankTrialDurationKHeadLaunchIndex
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (x : BankTrialLocalState q)
    (hx : x = bankTrialLocalRun ring root pre (bankTrialLocalStart S))
    (e : Fin n) (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialDurationKHeadActualStarts ring root S x e) :
    e = root ∧
      o.heads = (compileAdvice q).K ∧
      ((o.increment = true ∧
          bankTrialLiveHeadCount ring root pre
            (bankTrialLocalStart S) + 1 = (compileAdvice q).K) ∨
       (o.increment = false ∧
          bankTrialLiveHeadCount ring root pre
            (bankTrialLocalStart S) = (compileAdvice q).K)) := by
  obtain ⟨hsource, htag⟩ :=
    bankTrialDurationKHeadSelectedTag ring root S x e o ho
  have hindex := bankTrialC5ActualOriginLaunchHeadIndex
    ring root S hsp hlarge hwidth hclean pre x hx e o hsource
  refine ⟨bankTrialC5ActualStartAtRoot
    ring root S x e o hsource, htag, ?_⟩
  rcases hindex with hinc | hcomp
  · exact Or.inl ⟨hinc.1, hinc.2.symm.trans htag⟩
  · exact Or.inr ⟨hcomp.1, hcomp.2.symm.trans htag⟩

/-- No K-tagged origin can occur on a prefix with fewer than
K-1 previously paid heads. This is the exact non-prematurity
consequence available without a full HEAD-event authentication. -/
theorem bankTrialDurationKHeadNoPrematureLaunch
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (x : BankTrialLocalState q)
    (hx : x = bankTrialLocalRun ring root pre (bankTrialLocalStart S))
    (e : Fin n)
    (hearly : bankTrialLiveHeadCount ring root pre
        (bankTrialLocalStart S) + 1 < (compileAdvice q).K) :
    bankTrialDurationKHeadActualStarts ring root S x e = [] := by
  cases hs : bankTrialDurationKHeadActualStarts ring root S x e with
  | nil =>
      rfl
  | cons o rest =>
      have ho : o ∈
          bankTrialDurationKHeadActualStarts ring root S x e := by
        rw [hs]
        simp
      have hindex := bankTrialDurationKHeadLaunchIndex
        ring root S hsp hlarge hwidth hclean pre x hx e o ho
      rcases hindex.2.2 with hinc | hcomp
      · omega
      · omega

/-- A selected K-tagged origin whose FIRST worker exit is already
RECOVERY or LOST is charged by its C.5 timeout on the original
scheduler suffix. This does not assert that every K-head LOST
word has such a first-exit origin: that is the remaining census
coverage obligation. -/
theorem bankTrialDurationKHeadFirstTerminalExitTimeout
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialDurationKHeadActualStarts ring root S x e)
    (segment rest : List (Fin n))
    (hfirst : ∀ u v : List (Fin n), ∀ f : Fin n,
      segment = u ++ (f :: v) →
        ¬ (bankTrialC5ActualReturned o
             (bankTrialLocalRun ring root u o.after) ∨
           bankTrialC5ActualBadExit o
             (bankTrialLocalRun ring root u o.after)))
    (hterminal :
      (bankTrialLocalRun ring root segment o.after).phase =
        .recovery ∨
      (bankTrialLocalRun ring root segment o.after).phase =
        .lost) :
    bankTrialC5ActualTimeout ring root o (segment ++ rest) = true := by
  obtain ⟨hsource, htag⟩ :=
    bankTrialDurationKHeadSelectedTag ring root S x e o ho
  have hbad : bankTrialC5ActualBadExit o
      (bankTrialLocalRun ring root segment o.after) := by
    rcases hterminal with hrec | hlost
    · exact Or.inl hrec
    · exact Or.inr (Or.inl hlost)
  have hnot : ¬ bankTrialC5ActualReturned o
      (bankTrialLocalRun ring root segment o.after) := by
    intro hret
    unfold bankTrialC5ActualReturned at hret
    cases hinc : o.increment with
    | true =>
        simp only [hinc, ↓reduceIte] at hret
        obtain ⟨begun, hlive, _⟩ := hret
        rcases hterminal with hrec | hlost
        · rw [hrec] at hlive
          cases hlive
        · rw [hlost] at hlive
          cases hlive
    | false =>
        simp only [hinc, ↓reduceIte] at hret
        rcases hret with hbefore | hfinal
        · omega
        · have hwon := hfinal.2
          rcases hterminal with hrec | hlost
          · rw [hrec] at hwon
            cases hwon
          · rw [hlost] at hwon
            cases hwon
  have hkernel := bankTrialC5ActualWorkerExcursionKernelHolds
    ring root S hsp hlarge hwidth hclean
  exact hkernel.nonreturnBad x e o hsource segment rest
    hfirst (Or.inr hbad) hnot

end L3

#print axioms L3.bankTrialDurationKHeadSelectedTag
#print axioms L3.bankTrialDurationKHeadLaunchIndex
#print axioms L3.bankTrialDurationKHeadNoPrematureLaunch
#print axioms L3.bankTrialDurationKHeadFirstTerminalExitTimeout

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- A good return of the final K-tagged comparator has phase WON.
The alternative ARMED return is only defined strictly below K. -/
theorem bankTrialDurationKComparatorReturnWon
    {n q : Nat} (o : BankTrialC5ActualOrigin n q)
    (hcomp : o.increment = false)
    (htag : o.heads = (compileAdvice q).K)
    (z : BankTrialLocalState q)
    (hret : bankTrialC5ActualReturned o z) :
    z.phase = .won := by
  unfold bankTrialC5ActualReturned at hret
  simp only [hcomp, ↓reduceIte] at hret
  rcases hret with hbefore | hfinal
  · omega
  · exact hfinal.2

/-- Once the K comparator's scanner recognizes a GOOD exit, its
terminal WON state absorbs every subsequent physical letter. -/
theorem bankTrialDurationKComparatorGoodCannotLose
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (hcomp : o.increment = false)
    (htag : o.heads = (compileAdvice q).K) :
    ∀ (word : List (Fin n)) (z : BankTrialLocalState q),
      bankTrialC5WorkerFirstExit ring root o word z = some true →
      (bankTrialLocalRun ring root word z).phase ≠ .lost := by
  intro word
  induction word with
  | nil =>
      intro z hscan hlost
      by_cases hret : bankTrialC5ActualReturned o z
      · have hw := bankTrialDurationKComparatorReturnWon
          o hcomp htag z hret
        change z.phase = .lost at hlost
        rw [hw] at hlost
        cases hlost
      · simp only [bankTrialC5WorkerFirstExit,
          if_neg hret] at hscan
        split at hscan <;> cases hscan
  | cons e tail ih =>
      intro z hscan hlost
      by_cases hret : bankTrialC5ActualReturned o z
      · have hw := bankTrialDurationKComparatorReturnWon
          o hcomp htag z hret
        have hterminal : bankTrialLocalTerminal z :=
          Or.inl hw
        have habs := bankTrialLocalRunTerminalAbsorbs
          ring root (e :: tail) z hterminal
        rw [habs, hw] at hlost
        cases hlost
      · by_cases hbad : bankTrialC5ActualBadExit o z
        · have hf :
            bankTrialC5WorkerFirstExit ring root o
              (e :: tail) z = some false := by
            simp [bankTrialC5WorkerFirstExit, hret, hbad]
          rw [hf] at hscan
          cases hscan
        · have htail :
            bankTrialC5WorkerFirstExit ring root o tail
              (bankTrialLocalNext ring root z e) = some true := by
            simpa only [bankTrialC5WorkerFirstExit,
              if_neg hret, if_neg hbad] using hscan
          exact ih (bankTrialLocalNext ring root z e) htail hlost

/-- A terminal LOST suffix of a K-tagged comparator cannot have
scanner outcome NONE or GOOD. Its first classified exit is BAD,
and the installed C.5 nonreturnBad field makes its timeout true.
This handles RECOVERY -> LOST without needing to charge twice. -/
theorem bankTrialDurationKComparatorLostTimeout
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (x : BankTrialLocalState q) (e : Fin n)
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialDurationKHeadActualStarts ring root S x e)
    (hcomp : o.increment = false)
    (word : List (Fin n))
    (hlost : (bankTrialLocalRun ring root word o.after).phase =
      .lost) :
    bankTrialC5ActualTimeout ring root o word = true := by
  obtain ⟨hsource, htag⟩ :=
    bankTrialDurationKHeadSelectedTag ring root S x e o ho
  have hscan :
      bankTrialC5WorkerFirstExit ring root o word o.after =
        some false := by
    cases hs : bankTrialC5WorkerFirstExit ring root o word
        o.after with
    | none =>
        have hnonterminal :=
          bankTrialSuccessWorkerFirstExitNoneNonterminal
            ring root o word hs
        exact False.elim (hnonterminal (Or.inr hlost))
    | some result =>
        cases result with
        | false =>
            rfl
        | true =>
            have hnotlost := bankTrialDurationKComparatorGoodCannotLose
              ring root o hcomp htag word o.after hs
            exact False.elim (hnotlost hlost)
  have hkernel := bankTrialC5ActualWorkerExcursionKernelHolds
    ring root S hsp hlarge hwidth hclean
  exact bankTrialC5FirstBadImpliesTimeout
    ring root S hkernel x e o hsource word hscan

/-- On a reachable LIVE CSTART cut whose chronological head
count is K, its next outgoing root service creates the K-tagged
COMPARATOR (not another increment or another head). -/
theorem bankTrialDurationKHeadCStartRootSelected
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (x : BankTrialLocalState q)
    (begun : Bool)
    (hx : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hlive : x.phase = .live begun)
    (hmode : bankTrialLiveWaveRootMode x.bank = .CSTART)
    (hcount : bankTrialLiveHeadCount ring root pre
      (bankTrialLocalStart S) = (compileAdvice q).K) :
    ∃ o : BankTrialC5ActualOrigin n q,
      o ∈ bankTrialDurationKHeadActualStarts ring root S x root ∧
      o.increment = false ∧
      o.after = bankTrialLocalNext ring root x root := by
  obtain ⟨o, ho, hafter, hcomp⟩ :=
    bankTrialC5CStartRootActualOrigin
      ring root S hlarge hclean pre x begun hx hlive hmode
  have hindex := bankTrialC5ActualOriginLaunchHeadIndex
    ring root S hsp hlarge hwidth hclean pre x hx root o ho
  have htag : o.heads = (compileAdvice q).K := by
    rcases hindex with hi | hc
    · have hf : true = false := hi.1.symm.trans hcomp
      cases hf
    · exact hc.2.trans hcount
  have hselected :
      o ∈ bankTrialDurationKHeadActualStarts ring root S x root := by
    unfold bankTrialDurationKHeadActualStarts
    exact List.mem_filter.mpr
      ⟨ho, beq_iff_eq.mpr htag⟩
  exact ⟨o, hselected, hcomp, hafter⟩

/-- Every non-root service during the workerless CSTART interval
remains LIVE/CSTART, and preserves the chronological K head count.
In particular that physical step cannot be LIVE -> LOST. -/
theorem bankTrialDurationKHeadCStartNonrootStep
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (x : BankTrialLocalState q)
    (begun : Bool)
    (hx : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hlive : x.phase = .live begun)
    (hmode : bankTrialLiveWaveRootMode x.bank = .CSTART)
    (hcount : bankTrialLiveHeadCount ring root pre
      (bankTrialLocalStart S) = (compileAdvice q).K)
    (e : Fin n) (hne : e ≠ root) :
    ∃ nextBegun : Bool,
      (bankTrialLocalNext ring root x e).phase =
        .live nextBegun ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root x e).bank = .CSTART ∧
      bankTrialLiveHeadCount ring root (pre ++ [e])
        (bankTrialLocalStart S) = (compileAdvice q).K := by
  have hnil := bankTrialSuccessNoActualOriginOfNonroot
    ring root e S x hne
  obtain ⟨nextBegun, hnext, hnextMode⟩ :=
    bankTrialSuccessCStartNoOriginNext
      ring root S hlarge hclean pre x begun hx hlive hmode e hnil
  refine ⟨nextBegun, hnext, hnextMode, ?_⟩
  rw [bankTrialC5StrengthenedSnocHeads]
  have hnot : ¬
      (BankTrialProbabilityArmedGate
        (bankTrialLocalRun ring root pre (bankTrialLocalStart S)) ∧
        e = root) := by
    intro h
    exact hne h.2
  rw [if_neg hnot, Nat.add_zero]
  exact hcount

/-- If the observer is already LIVE/CSTART with exactly K paid
heads and a suffix ends LOST, that suffix must include a selected
K-tagged comparator origin. Merely waiting at CSTART cannot lose.
The witness identifies the ORIGINAL chronological launch position. -/
theorem bankTrialDurationKHeadCStartLostHasComparator
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    ∀ (suffix : List (Fin n)) (pre : List (Fin n))
      (x : BankTrialLocalState q) (begun : Bool),
      x = bankTrialLocalRun ring root pre (bankTrialLocalStart S) →
      x.phase = .live begun →
      bankTrialLiveWaveRootMode x.bank = .CSTART →
      bankTrialLiveHeadCount ring root pre
        (bankTrialLocalStart S) = (compileAdvice q).K →
      (bankTrialLocalRun ring root suffix x).phase = .lost →
      ∃ u v : List (Fin n),
        suffix = u ++ (root :: v) ∧
        ∃ o : BankTrialC5ActualOrigin n q,
          o ∈ bankTrialDurationKHeadActualStarts ring root S
            (bankTrialLocalRun ring root u x) root ∧
          o.increment = false := by
  intro suffix
  induction suffix with
  | nil =>
      intro pre x begun hx hlive hmode hcount hlost
      change x.phase = .lost at hlost
      rw [hlive] at hlost
      cases hlost
  | cons e tail ih =>
      intro pre x begun hx hlive hmode hcount hlost
      by_cases he : e = root
      · subst e
        obtain ⟨o, ho, hcomp, _⟩ :=
          bankTrialDurationKHeadCStartRootSelected
            ring root S hsp hlarge hwidth hclean
            pre x begun hx hlive hmode hcount
        refine ⟨[], tail, rfl, o, ?_, hcomp⟩
        change o ∈
          bankTrialDurationKHeadActualStarts ring root S x root
        exact ho
      · obtain ⟨nextBegun, hnext, hmodeNext, hcountNext⟩ :=
          bankTrialDurationKHeadCStartNonrootStep
            ring root S hlarge hclean
            pre x begun hx hlive hmode hcount e he
        have hxNext :
            bankTrialLocalNext ring root x e =
              bankTrialLocalRun ring root (pre ++ [e])
                (bankTrialLocalStart S) := by
          rw [bankTrialLocalRunAppend, ← hx]
          rfl
        obtain ⟨u, v, hdecomp, o, horigin, hcomp⟩ :=
          ih (pre ++ [e]) (bankTrialLocalNext ring root x e)
            nextBegun hxNext hnext hmodeNext hcountNext hlost
        refine ⟨e :: u, v, ?_, o, ?_, hcomp⟩
        · rw [hdecomp]
          rfl
        · exact horigin

/-- CSTART half of (t2): any suffix that starts at a genuine
K-head LIVE/CSTART cut and ends LOST has a selected K comparator
whose OWN remaining scheduler suffix triggers the timeout.
No re-sampling or whole-word rarity assertion is used. -/
theorem bankTrialDurationKHeadCStartLostTimeoutWitness
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (x : BankTrialLocalState q)
    (begun : Bool)
    (hx : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hlive : x.phase = .live begun)
    (hmode : bankTrialLiveWaveRootMode x.bank = .CSTART)
    (hcount : bankTrialLiveHeadCount ring root pre
      (bankTrialLocalStart S) = (compileAdvice q).K)
    (suffix : List (Fin n))
    (hlost : (bankTrialLocalRun ring root suffix x).phase = .lost) :
    ∃ u v : List (Fin n),
      suffix = u ++ (root :: v) ∧
      ∃ o : BankTrialC5ActualOrigin n q,
        o ∈ bankTrialDurationKHeadActualStarts ring root S
          (bankTrialLocalRun ring root u x) root ∧
        o.increment = false ∧
        bankTrialC5ActualTimeout ring root o v = true := by
  obtain ⟨u, v, hdecomp, o, horigin, hcomp⟩ :=
    bankTrialDurationKHeadCStartLostHasComparator
      ring root S hsp hlarge hwidth hclean
      suffix pre x begun hx hlive hmode hcount hlost
  have hsource :=
    (bankTrialDurationKHeadSelectedTag
      ring root S (bankTrialLocalRun ring root u x)
      root o horigin).1
  have hpost :=
    bankTrialC5ActualStartPost
      ring root S (bankTrialLocalRun ring root u x)
      root o hsource
  have hrun :
      bankTrialLocalRun ring root suffix x =
        bankTrialLocalRun ring root v o.after := by
    rw [hdecomp, bankTrialLocalRunAppend]
    change bankTrialLocalRun ring root v
      (bankTrialLocalNext ring root
        (bankTrialLocalRun ring root u x) root) =
      bankTrialLocalRun ring root v o.after
    rw [hpost]
  have hafterLost :
      (bankTrialLocalRun ring root v o.after).phase = .lost := by
    rw [← hrun]
    exact hlost
  have htimeout := bankTrialDurationKComparatorLostTimeout
    ring root S hsp hlarge hwidth hclean
    (bankTrialLocalRun ring root u x) root o
    horigin hcomp v hafterLost
  exact ⟨u, v, hdecomp, o, horigin, hcomp, htimeout⟩

/-- (t3) The K-th increment origin cannot occur a second time
later on the same original scheduler word. Its first launch
already raises the chronological HEAD count to K; that count
is monotonically nondecreasing under suffix extension. -/
theorem bankTrialDurationKHeadIncrementCannotRepeat
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre between : List (Fin n))
    (x y : BankTrialLocalState q)
    (hx : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hy : y = bankTrialLocalRun ring root
      ((pre ++ [root]) ++ between) (bankTrialLocalStart S))
    (o p : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialDurationKHeadActualStarts ring root S x root)
    (hinc : o.increment = true)
    (e : Fin n)
    (hp : p ∈ bankTrialDurationKHeadActualStarts ring root S y e)
    (hincLater : p.increment = true) : False := by
  obtain ⟨hsource, htag⟩ :=
    bankTrialDurationKHeadSelectedTag ring root S x root o ho
  have hpaid :
      bankTrialLiveHeadCount ring root (pre ++ [root])
        (bankTrialLocalStart S) = (compileAdvice q).K := by
    have h := bankTrialC5ActualOriginHeadCountExact
      ring root S hsp hlarge hwidth hclean
      pre x hx root o hsource
    exact h.symm.trans htag
  have hmonotone :
      bankTrialLiveHeadCount ring root (pre ++ [root])
        (bankTrialLocalStart S) ≤
      bankTrialLiveHeadCount ring root
        ((pre ++ [root]) ++ between) (bankTrialLocalStart S) := by
    rw [bankTrialLiveHeadCountAppend ring root (pre ++ [root]) between]
    exact Nat.le_add_right _ _
  have hindex := bankTrialDurationKHeadLaunchIndex
    ring root S hsp hlarge hwidth hclean
    ((pre ++ [root]) ++ between) y hy e p hp
  rcases hindex.2.2 with hnew | hold
  · omega
  · have hf : false = true := hold.1.symm.trans hincLater
    cases hf

end L3

#print axioms L3.bankTrialDurationKComparatorReturnWon
#print axioms L3.bankTrialDurationKComparatorGoodCannotLose
#print axioms L3.bankTrialDurationKComparatorLostTimeout
#print axioms L3.bankTrialDurationKHeadCStartRootSelected
#print axioms L3.bankTrialDurationKHeadCStartNonrootStep
#print axioms L3.bankTrialDurationKHeadCStartLostHasComparator
#print axioms L3.bankTrialDurationKHeadCStartLostTimeoutWitness
#print axioms L3.bankTrialDurationKHeadIncrementCannotRepeat

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Once the local observer has left LIVE, no later letter can
pay an ARMED head. This applies also to the RECOVERY interval. -/
theorem bankTrialDurationNoLiveFutureHeads
    {n q : Nat} (ring : DirectedRing n) (root : Fin n) :
    ∀ (word : List (Fin n)) (z : BankTrialLocalState q),
      (∀ begun : Bool, z.phase ≠ .live begun) →
      bankTrialLiveHeadCount ring root word z = 0 := by
  intro word
  induction word with
  | nil =>
      intro z _
      rfl
  | cons e tail ih =>
      intro z hnotlive
      have hnotgate : ¬ BankTrialProbabilityArmedGate z := by
        intro hg
        obtain ⟨⟨begun, hlive⟩, _⟩ := hg
        exact hnotlive begun hlive
      have hnext : ∀ begun : Bool,
          (bankTrialLocalNext ring root z e).phase ≠ .live begun := by
        intro begun hnextlive
        obtain ⟨oldBegun, holdlive⟩ :=
          bankTrialC5StrengthenedOldLive
            ring root e z begun hnextlive
        exact hnotlive oldBegun holdlive
      change
        (if BankTrialProbabilityArmedGate z ∧ e = root
         then 1 else 0) +
          bankTrialLiveHeadCount ring root tail
            (bankTrialLocalNext ring root z e) = 0
      rw [if_neg (show ¬ (BankTrialProbabilityArmedGate z ∧
          e = root) by intro h; exact hnotgate h.1)]
      simpa only [Nat.zero_add] using
        ih (bankTrialLocalNext ring root z e) hnext

/-- The adapted event always entails at least its requested
number of ACTUAL paid ARMED root decisions, for any observer
state. It needs no CLEAN/reachability hypothesis. -/
theorem bankTrialDurationHeadEventCountLower
    {n q : Nat} (ring : DirectedRing n) (root : Fin n) :
    ∀ (word : List (Fin n)) (k : Nat)
      (z : BankTrialLocalState q),
      bankTrialProbabilityHeadEvent ring root word k z →
      k ≤ bankTrialLiveHeadCount ring root word z := by
  intro word
  induction word with
  | nil =>
      intro k z hevent
      change k = 0 at hevent
      change k ≤ 0
      omega
  | cons e tail ih =>
      intro k z hevent
      cases k with
      | zero =>
          exact Nat.zero_le _
      | succ k =>
          by_cases hgate : BankTrialProbabilityArmedGate z
          · by_cases hroot : e = root
            · have htail :
                  bankTrialProbabilityHeadEvent ring root tail k
                    (bankTrialLocalNext ring root z e) := by
                simpa [bankTrialProbabilityHeadEvent,
                  hgate, hroot] using hevent
              have hcount := ih k (bankTrialLocalNext ring root z e)
                htail
              change k + 1 ≤
                (if BankTrialProbabilityArmedGate z ∧ e = root
                 then 1 else 0) +
                  bankTrialLiveHeadCount ring root tail
                    (bankTrialLocalNext ring root z e)
              rw [if_pos ⟨hgate, hroot⟩]
              omega
            · by_cases hin : ring.rightNeighbor e = root
              · have hfalse : False := by
                  simpa [bankTrialProbabilityHeadEvent,
                    hgate, hroot, hin] using hevent
                exact False.elim hfalse
              · have htail :
                    bankTrialProbabilityHeadEvent ring root tail (k + 1)
                      (bankTrialLocalNext ring root z e) := by
                  simpa [bankTrialProbabilityHeadEvent,
                    hgate, hroot, hin] using hevent
                have hcount := ih (k + 1)
                  (bankTrialLocalNext ring root z e) htail
                change k + 1 ≤
                  (if BankTrialProbabilityArmedGate z ∧ e = root
                   then 1 else 0) +
                    bankTrialLiveHeadCount ring root tail
                      (bankTrialLocalNext ring root z e)
                rw [if_neg (show ¬
                    (BankTrialProbabilityArmedGate z ∧ e = root)
                    by intro h; exact hroot h.2)]
                simpa only [Nat.zero_add] using hcount
          · have htail :
                bankTrialProbabilityHeadEvent ring root tail (k + 1)
                  (bankTrialLocalNext ring root z e) := by
              simpa [bankTrialProbabilityHeadEvent,
                hgate] using hevent
            have hcount := ih (k + 1)
              (bankTrialLocalNext ring root z e) htail
            change k + 1 ≤
              (if BankTrialProbabilityArmedGate z ∧ e = root
               then 1 else 0) +
                bankTrialLiveHeadCount ring root tail
                  (bankTrialLocalNext ring root z e)
            rw [if_neg (show ¬
                (BankTrialProbabilityArmedGate z ∧ e = root)
                by intro h; exact hgate h.1)]
            simpa only [Nat.zero_add] using hcount

/-- Conversely, for a reachable CLEAN-start tape, k paid
heads imply the adapted k-head event. A forbidden incoming
letter at a still-open ARMED gate creates RECOVERY and makes
all further head credit zero. Unlike NoArmedIncoming, this
proof imposes no condition on letters AFTER the kth head. -/
theorem bankTrialDurationCleanCountImpliesHeadEvent
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    ∀ (word pre : List (Fin n)) (z : BankTrialLocalState q)
      (k : Nat),
      z = bankTrialLocalRun ring root pre (bankTrialLocalStart S) →
      k ≤ bankTrialLiveHeadCount ring root word z →
      bankTrialProbabilityHeadEvent ring root word k z := by
  intro word
  induction word with
  | nil =>
      intro pre z k hz hcount
      change k ≤ 0 at hcount
      change k = 0
      omega
  | cons e tail ih =>
      intro pre z k hz hcount
      cases k with
      | zero =>
          change True
          trivial
      | succ k =>
          have hzNext :
              bankTrialLocalNext ring root z e =
                bankTrialLocalRun ring root (pre ++ [e])
                  (bankTrialLocalStart S) := by
            rw [bankTrialLocalRunAppend, ← hz]
            rfl
          by_cases hgate : BankTrialProbabilityArmedGate z
          · by_cases hroot : e = root
            · have htailBound :
                  k ≤ bankTrialLiveHeadCount ring root tail
                    (bankTrialLocalNext ring root z e) := by
                change k + 1 ≤
                  (if BankTrialProbabilityArmedGate z ∧ e = root
                   then 1 else 0) +
                    bankTrialLiveHeadCount ring root tail
                      (bankTrialLocalNext ring root z e) at hcount
                rw [if_pos ⟨hgate, hroot⟩] at hcount
                omega
              have htail := ih (pre ++ [e])
                (bankTrialLocalNext ring root z e) k
                hzNext htailBound
              simpa [bankTrialProbabilityHeadEvent,
                hgate, hroot] using htail
            · by_cases hin : ring.rightNeighbor e = root
              · obtain ⟨⟨begun, hlive⟩, hmode⟩ := hgate
                have hzeta :
                    z = (⟨z.bank, .live begun⟩ :
                      BankTrialLocalState q) :=
                  bankTrialCmpStateEta z begun hlive
                have hrun :
                    bankTrialLocalRun ring root pre
                      (bankTrialLocalStart S) =
                      (⟨z.bank, .live begun⟩ :
                        BankTrialLocalState q) :=
                  hz.symm.trans hzeta
                have hfalse :=
                  bankTrialProbabilityCleanLiveUnlatched
                    ring root S hclean pre z.bank begun hrun
                have hrecover :=
                  bankTrialProbabilityIncomingArmedEntersRecovery
                    ring root e z.bank begun hfalse hmode
                    hroot hin
                have hnotlive : ∀ nextBegun : Bool,
                    (bankTrialLocalNext ring root z e).phase ≠
                      .live nextBegun := by
                  intro nextBegun hnext
                  rw [hzeta, hrecover] at hnext
                  cases hnext
                have hzero :=
                  bankTrialDurationNoLiveFutureHeads
                    ring root tail (bankTrialLocalNext ring root z e)
                    hnotlive
                have hbound : k + 1 ≤ 0 := by
                  change k + 1 ≤
                    (if BankTrialProbabilityArmedGate z ∧ e = root
                     then 1 else 0) +
                      bankTrialLiveHeadCount ring root tail
                        (bankTrialLocalNext ring root z e) at hcount
                  rw [if_neg (show ¬
                      (BankTrialProbabilityArmedGate z ∧ e = root)
                      by intro h; exact hroot h.2),
                    hzero] at hcount
                  simpa only [Nat.zero_add] using hcount
                omega
              · have htailBound :
                    k + 1 ≤ bankTrialLiveHeadCount ring root tail
                      (bankTrialLocalNext ring root z e) := by
                  change k + 1 ≤
                    (if BankTrialProbabilityArmedGate z ∧ e = root
                     then 1 else 0) +
                      bankTrialLiveHeadCount ring root tail
                        (bankTrialLocalNext ring root z e) at hcount
                  rw [if_neg (show ¬
                      (BankTrialProbabilityArmedGate z ∧ e = root)
                      by intro h; exact hroot h.2)] at hcount
                  simpa only [Nat.zero_add] using hcount
                have htail := ih (pre ++ [e])
                  (bankTrialLocalNext ring root z e) (k + 1)
                  hzNext htailBound
                simpa [bankTrialProbabilityHeadEvent,
                  hgate, hroot, hin] using htail
          · have htailBound :
                k + 1 ≤ bankTrialLiveHeadCount ring root tail
                  (bankTrialLocalNext ring root z e) := by
              change k + 1 ≤
                (if BankTrialProbabilityArmedGate z ∧ e = root
                 then 1 else 0) +
                  bankTrialLiveHeadCount ring root tail
                    (bankTrialLocalNext ring root z e) at hcount
              rw [if_neg (show ¬
                  (BankTrialProbabilityArmedGate z ∧ e = root)
                  by intro h; exact hgate h.1)] at hcount
              simpa only [Nat.zero_add] using hcount
            have htail := ih (pre ++ [e])
              (bankTrialLocalNext ring root z e) (k + 1)
              hzNext htailBound
            simpa [bankTrialProbabilityHeadEvent,
              hgate] using htail

/-- Every emitted K-tagged origin lies on a literal prefix
satisfying the adapted K-head event. This also establishes the
event for a K comparator whose launch does not pay another head. -/
theorem bankTrialDurationKHeadLaunchHasHeadEvent
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (z : BankTrialLocalState q)
    (hz : z = bankTrialLocalRun ring root pre (bankTrialLocalStart S))
    (e : Fin n) (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialDurationKHeadActualStarts ring root S z e) :
    bankTrialProbabilityHeadEvent ring root (pre ++ [e])
      (compileAdvice q).K (bankTrialLocalStart S) := by
  obtain ⟨hsource, htag⟩ :=
    bankTrialDurationKHeadSelectedTag ring root S z e o ho
  have hcount :=
    bankTrialC5ActualOriginHeadCountExact
      ring root S hsp hlarge hwidth hclean pre z hz e o hsource
  exact bankTrialDurationCleanCountImpliesHeadEvent
    ring root S hclean (pre ++ [e]) []
    (bankTrialLocalStart S) (compileAdvice q).K
    rfl (Nat.le_of_eq (hcount.symm.trans htag).symm)

/-- A positive kth paid ARMED head always has a first physical
root service on the same scheduler tape. No stochastic
conditioning and no list-of-cuts assumption is needed. -/
theorem bankTrialDurationHeadCountNthCut
    {n q : Nat} (ring : DirectedRing n) (root : Fin n) :
    ∀ (word : List (Fin n)) (k : Nat) (z : BankTrialLocalState q),
      0 < k →
      k ≤ bankTrialLiveHeadCount ring root word z →
      ∃ pre tail : List (Fin n),
        word = pre ++ (root :: tail) ∧
        BankTrialProbabilityArmedGate
          (bankTrialLocalRun ring root pre z) ∧
        bankTrialLiveHeadCount ring root pre z + 1 = k := by
  intro word
  induction word with
  | nil =>
      intro k z hk hcount
      change k ≤ 0 at hcount
      omega
  | cons e tail ih =>
      intro k z hk hcount
      by_cases hpay : BankTrialProbabilityArmedGate z ∧ e = root
      · by_cases hone : k = 1
        · subst k
          refine ⟨[], tail, ?_, hpay.1, ?_⟩
          · rw [hpay.2]
            rfl
          · change (0 : Nat) + 1 = 1
            rfl
        · have hsub : 0 < k - 1 := by omega
          have htail :
              k - 1 ≤ bankTrialLiveHeadCount ring root tail
                (bankTrialLocalNext ring root z e) := by
            change k ≤
              (if BankTrialProbabilityArmedGate z ∧ e = root
               then 1 else 0) +
                bankTrialLiveHeadCount ring root tail
                  (bankTrialLocalNext ring root z e) at hcount
            rw [if_pos hpay] at hcount
            omega
          obtain ⟨u, v, hw, hg, hc⟩ :=
            ih (k - 1) (bankTrialLocalNext ring root z e)
              hsub htail
          refine ⟨e :: u, v, ?_, ?_, ?_⟩
          · change e :: tail = e :: (u ++ root :: v)
            rw [hw]
          · change BankTrialProbabilityArmedGate
              (bankTrialLocalRun ring root u
                (bankTrialLocalNext ring root z e))
            exact hg
          · change (if BankTrialProbabilityArmedGate z ∧
                e = root then 1 else 0) +
                bankTrialLiveHeadCount ring root u
                  (bankTrialLocalNext ring root z e) + 1 = k
            rw [if_pos hpay]
            omega
      · have htail :
            k ≤ bankTrialLiveHeadCount ring root tail
              (bankTrialLocalNext ring root z e) := by
          change k ≤
            (if BankTrialProbabilityArmedGate z ∧ e = root
             then 1 else 0) +
              bankTrialLiveHeadCount ring root tail
                (bankTrialLocalNext ring root z e) at hcount
          rw [if_neg hpay] at hcount
          simpa only [Nat.zero_add] using hcount
        obtain ⟨u, v, hw, hg, hc⟩ :=
          ih k (bankTrialLocalNext ring root z e) hk htail
        refine ⟨e :: u, v, ?_, ?_, ?_⟩
        · change e :: tail = e :: (u ++ root :: v)
          rw [hw]
        · change BankTrialProbabilityArmedGate
            (bankTrialLocalRun ring root u
              (bankTrialLocalNext ring root z e))
          exact hg
        · change (if BankTrialProbabilityArmedGate z ∧
              e = root then 1 else 0) +
              bankTrialLiveHeadCount ring root u
                (bankTrialLocalNext ring root z e) + 1 = k
          rw [if_neg hpay]
          omega

/-- The kth head of a successful adapted HEAD word has a
chronological predecessor gate and an exact K-1 paid-head count.
This strengthens the stopped-cut statement with the root letter. -/
theorem bankTrialDurationKHeadEventCut
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (word : List (Fin n))
    (hevent : bankTrialProbabilityHeadEvent ring root word
      (compileAdvice q).K (bankTrialLocalStart S)) :
    ∃ pre tail : List (Fin n),
      word = pre ++ (root :: tail) ∧
      BankTrialProbabilityArmedGate
        (bankTrialLocalRun ring root pre (bankTrialLocalStart S)) ∧
      bankTrialLiveHeadCount ring root pre
        (bankTrialLocalStart S) + 1 = (compileAdvice q).K := by
  have hpositive : 0 < (compileAdvice q).K :=
    Counter.resetColdPrivateKPositive q hsp
  have hcount := bankTrialDurationHeadEventCountLower
    ring root word (compileAdvice q).K (bankTrialLocalStart S)
    hevent
  exact bankTrialDurationHeadCountNthCut ring root
    word (compileAdvice q).K (bankTrialLocalStart S)
    hpositive hcount

/-- t2, zero-first-bit branch at the Kth HEAD:
the head itself is workerless LIVE/CSTART, and LOST requires a
subsequent K-tagged comparator whose suffix times out. -/
theorem bankTrialDurationKHeadZeroCutLostTimeoutWitness
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre suffix : List (Fin n))
    (hgate : BankTrialProbabilityArmedGate
      (bankTrialLocalRun ring root pre (bankTrialLocalStart S)))
    (hcount : bankTrialLiveHeadCount ring root pre
      (bankTrialLocalStart S) + 1 = (compileAdvice q).K)
    (hzero : bankTrialLiveWaveBit
      (bankTrialLocalRun ring root pre (bankTrialLocalStart S)).bank
      ⟨0, bankTrialWindowWidthPos q⟩ = false)
    (hlost : (bankTrialLocalRun ring root
      ((pre ++ [root]) ++ suffix) (bankTrialLocalStart S)).phase =
        .lost) :
    ∃ u v : List (Fin n),
      suffix = u ++ (root :: v) ∧
      ∃ o : BankTrialC5ActualOrigin n q,
        o ∈ bankTrialDurationKHeadActualStarts ring root S
          (bankTrialLocalRun ring root u
            (bankTrialLocalNext ring root
              (bankTrialLocalRun ring root pre
                (bankTrialLocalStart S)) root)) root ∧
        o.increment = false ∧
        bankTrialC5ActualTimeout ring root o v = true := by
  have hstart := bankTrialSuccessReachableArmedStart
    ring root S hlarge hclean pre
    (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
    rfl hgate
  have hzeroStep := bankTrialC5ArmedHeadZeroCStart
    ring root
    (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
    hstart hzero
  obtain ⟨nextBegun, hnextLive⟩ := hzeroStep.live
  have hstate :
      bankTrialLocalNext ring root
        (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
        root =
      bankTrialLocalRun ring root (pre ++ [root])
        (bankTrialLocalStart S) := by
    rw [bankTrialLocalRunAppend]
    rfl
  have hcountCut :
      bankTrialLiveHeadCount ring root (pre ++ [root])
        (bankTrialLocalStart S) = (compileAdvice q).K := by
    rw [bankTrialC5StrengthenedSnocHeads,
      if_pos (show BankTrialProbabilityArmedGate
          (bankTrialLocalRun ring root pre (bankTrialLocalStart S)) ∧
          root = root from ⟨hgate, rfl⟩)]
    exact hcount
  have hfinal :
      (bankTrialLocalRun ring root suffix
        (bankTrialLocalNext ring root
          (bankTrialLocalRun ring root pre
            (bankTrialLocalStart S)) root)).phase = .lost := by
    rw [bankTrialLocalRunAppend] at hlost
    rw [hstate]
    exact hlost
  exact bankTrialDurationKHeadCStartLostTimeoutWitness
    ring root S hsp hlarge hwidth hclean
    (pre ++ [root])
    (bankTrialLocalNext ring root
      (bankTrialLocalRun ring root pre
        (bankTrialLocalStart S)) root)
    nextBegun hstate hnextLive hzeroStep.cstart
    hcountCut suffix hfinal

/-- No LIVE CSTART or IWAIT state can reappear after a true
CWAIT prefix with all K heads already paid. The only possible
LIVE entry into those modes comes from those same modes or a
new paid head; the latter would violate the all-word K cap. -/
theorem bankTrialDurationKNoLiveWaitAfterCWait
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n))
    (hcount : bankTrialLiveHeadCount ring root pre
      (bankTrialLocalStart S) = (compileAdvice q).K)
    (hmode : bankTrialLiveWaveRootMode
      (bankTrialLocalRun ring root pre (bankTrialLocalStart S)).bank =
        .CWAIT) :
    ∀ (suffix : List (Fin n)) (begun : Bool),
      (bankTrialLocalRun ring root (pre ++ suffix)
        (bankTrialLocalStart S)).phase = .live begun →
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root (pre ++ suffix)
          (bankTrialLocalStart S)).bank ≠ .IWAIT ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root (pre ++ suffix)
          (bankTrialLocalStart S)).bank ≠ .CSTART := by
  have hentry := bankTrialC5ActualLiveModeEntryHolds
    ring root S hlarge hclean
  have hreverse : ∀ rev : List (Fin n), ∀ begun : Bool,
      (bankTrialLocalRun ring root (pre ++ rev.reverse)
        (bankTrialLocalStart S)).phase = .live begun →
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root (pre ++ rev.reverse)
          (bankTrialLocalStart S)).bank ≠ .IWAIT ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root (pre ++ rev.reverse)
          (bankTrialLocalStart S)).bank ≠ .CSTART := by
    intro rev
    induction rev with
    | nil =>
        intro begun hlive
        rw [List.reverse_nil, List.append_nil]
        constructor
        · intro hi
          rw [hmode] at hi
          cases hi
        · intro hc
          rw [hmode] at hc
          cases hc
    | cons e rest ih =>
        intro nextBegun hnext
        have hword :
            pre ++ (e :: rest).reverse =
              (pre ++ rest.reverse) ++ [e] := by
          simp only [List.reverse_cons, List.append_assoc]
        have hnextStep :
            (bankTrialLocalNext ring root
              (bankTrialLocalRun ring root (pre ++ rest.reverse)
                (bankTrialLocalStart S)) e).phase =
                  .live nextBegun := by
          rw [hword, bankTrialLocalRunAppend] at hnext
          exact hnext
        obtain ⟨oldBegun, holdLive⟩ :=
          bankTrialC5StrengthenedOldLive ring root e
            (bankTrialLocalRun ring root (pre ++ rest.reverse)
              (bankTrialLocalStart S))
            nextBegun hnextStep
        have hprevious := ih oldBegun holdLive
        have hmon :
            (compileAdvice q).K ≤
              bankTrialLiveHeadCount ring root
                (pre ++ rest.reverse) (bankTrialLocalStart S) := by
          rw [bankTrialLiveHeadCountAppend]
          omega
        have hcap :=
          bankTrialC5ActualAllWordsHeadCap
            ring root S hsp hlarge hwidth hclean
            ((pre ++ rest.reverse) ++ [e])
        have hnotpay : ¬
            (BankTrialProbabilityArmedGate
              (bankTrialLocalRun ring root (pre ++ rest.reverse)
                (bankTrialLocalStart S)) ∧ e = root) := by
          intro hpay
          have hpaidCount :
              bankTrialLiveHeadCount ring root
                ((pre ++ rest.reverse) ++ [e])
                (bankTrialLocalStart S) =
              bankTrialLiveHeadCount ring root
                (pre ++ rest.reverse) (bankTrialLocalStart S) + 1 := by
            rw [bankTrialC5StrengthenedSnocHeads, if_pos hpay]
          rw [hpaidCount] at hcap
          omega
        have hnotnext : ¬
            (bankTrialLiveWaveRootMode
              (bankTrialLocalNext ring root
                (bankTrialLocalRun ring root (pre ++ rest.reverse)
                  (bankTrialLocalStart S)) e).bank = .IWAIT ∨
             bankTrialLiveWaveRootMode
              (bankTrialLocalNext ring root
                (bankTrialLocalRun ring root (pre ++ rest.reverse)
                  (bankTrialLocalStart S)) e).bank = .CSTART) := by
          intro hnew
          rcases hentry (pre ++ rest.reverse) e
              nextBegun hnextStep hnew with hold | hpaid
          · rcases hold with hi | hc
            · exact hprevious.1 hi
            · exact hprevious.2 hc
          · exact hnotpay hpaid
        rw [hword, bankTrialLocalRunAppend]
        constructor
        · intro hi
          exact hnotnext (Or.inl hi)
        · intro hc
          exact hnotnext (Or.inr hc)
  intro suffix begun hphase
  have h := hreverse suffix.reverse begun
    (by simpa only [List.reverse_reverse] using hphase)
  simpa only [List.reverse_reverse] using h

/-- t3, comparator uniqueness: no second K-tagged comparator
launch occurs later on the same scheduler word. The first
comparator leaves the root in CWAIT with K paid heads, and
the LIVE mode-entry invariant prevents reentry into CSTART. -/
theorem bankTrialDurationKHeadComparatorCannotRepeat
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre between : List (Fin n))
    (x y : BankTrialLocalState q)
    (hx : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hy : y = bankTrialLocalRun ring root
      ((pre ++ [root]) ++ between) (bankTrialLocalStart S))
    (o p : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialDurationKHeadActualStarts ring root S x root)
    (hcomp : o.increment = false)
    (e : Fin n)
    (hp : p ∈ bankTrialDurationKHeadActualStarts ring root S y e)
    (hcompLater : p.increment = false) : False := by
  obtain ⟨hsource, htag⟩ :=
    bankTrialDurationKHeadSelectedTag ring root S x root o ho
  obtain ⟨_, _, _, _, hmodes⟩ :=
    bankTrialC5ActualStartGuardFacts ring root S x root o hsource
  have hnextMode :
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root x root).bank = .CWAIT := by
    rcases hmodes with hi | hc
    · have hinc : o.increment = true := by
        rw [bankTrialC5ActualIncrementTagExact
          ring root S x root o hsource, hi.1]
        rfl
      rw [hcomp] at hinc
      cases hinc
    · exact hc.2
  have hpost :=
    bankTrialC5ActualStartPost ring root S x root o hsource
  have hstate :
      o.after = bankTrialLocalRun ring root (pre ++ [root])
        (bankTrialLocalStart S) := by
    calc
      o.after = bankTrialLocalNext ring root x root := hpost
      _ = bankTrialLocalRun ring root (pre ++ [root])
            (bankTrialLocalStart S) := by
        rw [bankTrialLocalRunAppend, ← hx]
        rfl
  have hmodeAfter :
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root (pre ++ [root])
          (bankTrialLocalStart S)).bank = .CWAIT := by
    rw [← hstate, hpost]
    exact hnextMode
  have hcountAfter :
      bankTrialLiveHeadCount ring root (pre ++ [root])
        (bankTrialLocalStart S) = (compileAdvice q).K :=
    (bankTrialC5ActualOriginHeadCountExact
      ring root S hsp hlarge hwidth hclean pre x hx root o
      hsource).symm.trans htag
  obtain ⟨hsourceLater, _⟩ :=
    bankTrialDurationKHeadSelectedTag ring root S y e p hp
  obtain ⟨_, _, _, ⟨oldBegun, _, hliveLater, _⟩,
    hmodesLater⟩ :=
    bankTrialC5ActualStartGuardFacts ring root S y e p
      hsourceLater
  have hmodeBeforeLater :
      bankTrialLiveWaveRootMode y.bank = .CSTART := by
    rcases hmodesLater with hi | hc
    · have hinc : p.increment = true := by
        rw [bankTrialC5ActualIncrementTagExact
          ring root S y e p hsourceLater, hi.1]
        rfl
      rw [hcompLater] at hinc
      cases hinc
    · exact hc.1
  have hliveFull :
      (bankTrialLocalRun ring root
        ((pre ++ [root]) ++ between)
        (bankTrialLocalStart S)).phase = .live oldBegun := by
    rw [← hy]
    exact hliveLater
  have hnoWait := bankTrialDurationKNoLiveWaitAfterCWait
    ring root S hsp hlarge hwidth hclean
    (pre ++ [root]) hcountAfter hmodeAfter between oldBegun
    hliveFull
  have hnotCStart :
      bankTrialLiveWaveRootMode y.bank ≠ .CSTART := by
    rw [hy]
    exact hnoWait.2
  exact hnotCStart hmodeBeforeLater

end L3

#print axioms L3.bankTrialDurationNoLiveFutureHeads
#print axioms L3.bankTrialDurationHeadEventCountLower
#print axioms L3.bankTrialDurationCleanCountImpliesHeadEvent
#print axioms L3.bankTrialDurationKHeadLaunchHasHeadEvent
#print axioms L3.bankTrialDurationHeadCountNthCut
#print axioms L3.bankTrialDurationKHeadEventCut
#print axioms L3.bankTrialDurationKHeadZeroCutLostTimeoutWitness
#print axioms L3.bankTrialDurationKNoLiveWaitAfterCWait
#print axioms L3.bankTrialDurationKHeadComparatorCannotRepeat

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-! G12e/C.8 at the success-scale charge. The two physical
    obligations below remain assumptions, not theorems. -/

/-- (A) A clean spatial WON word carries the K-head event,
with the identical original stopped costWord. -/
theorem bankTrialDurationSuccessCostLeAllKHeadCost
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hsmall : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (T : Nat) :
    bankTrialDurationSuccessCostMass ring root S T ≤
      bankTrialDurationAllKHeadCostMass ring root S T := by
  unfold bankTrialDurationSuccessCostMass
    bankTrialDurationAllKHeadCostMass
  apply bankTrialProbabilityScheduleSumMono n T
  intro w
  by_cases hwon :
      (bankTrialLocalRun ring root w
        (bankTrialLocalStart S)).phase = .won
  · have hhead := bankTrialSuccessCleanWinningHeadEvent
      ring root S hsmall hlarge hclean w hwon
    simp only [if_pos hwon, if_pos hhead]
    exact Nat.le_refl _
  · simp only [if_neg hwon]
    exact Nat.zero_le _

/-- (D), open post-cut obligation. Membership means an actual
first K-head stopped prefix on a length-T original tape.
The suffix horizon t is arbitrary, not necessarily T-|cut|. -/
def BankTrialDurationKHeadPostCutBudget
    {n q : Nat} (ring : DirectedRing n)
    (root : Fin n) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    BankTrialLocalClean q S →
    (compileAdvice q).useSmall = false →
    2 * (compileAdvice q).bankLeaseCap ≤ n →
    ∀ (T : Nat) (cut : List (Fin n)),
      cut ∈ Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        (bankTrialDurationKHeadCutStop ring root S)
        T [] (bankTrialLocalStart S) →
      ∀ t : Nat,
        costNumerator (bankTrialLocalNext ring root)
          bankTrialLocalTerminal
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) t ≤
          ((8 * (compileAdvice q).b + 11) * n) * n ^ t

/-- (B), the exact all-K-head charge at C' rather than B. -/
def BankTrialDurationAllKHeadChargeAtSuccessScale
    {n q : Nat} (ring : DirectedRing n)
    (root : Fin n) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    BankTrialLocalClean q S →
    (compileAdvice q).useSmall = false →
    2 * (compileAdvice q).bankLeaseCap ≤ n →
    ∀ T : Nat,
      bankTrialDurationAllKHeadCostMass ring root S T ≤
        bankTrialProbabilityHeadMass ring root
          (bankTrialLocalStart S) (compileAdvice q).K T *
          ((6 * (compileAdvice q).b + 9) *
            ((compileAdvice q).K + 1) * n)

/-- Scalar check for subtracting the post-cut allowance.
All factors here are opaque Nat parameters. -/
private theorem bankTrialDurationKHeadPostFitsScale
    (b K n : Nat) (hK : 0 < K) :
    (8 * b + 11) * n ≤
      (6 * b + 9) * (K + 1) * n := by
  have hlinear : 8 * b + 11 ≤ (6 * b + 9) * 2 := by
    omega
  have htwo : 2 ≤ K + 1 := by
    omega
  exact Nat.mul_le_mul_right n
    (Nat.le_trans hlinear
      (Nat.mul_le_mul_left (6 * b + 9) htwo))

/-- Membership-aware list-sum accounting. This is purely Nat
arithmetic; no independence or new stopped-tree hypothesis. -/
private theorem bankTrialDurationKHeadCutPostSumArithmetic
    {α : Type} (cuts : List α)
    (before after weight : α → Nat)
    (head post charge : Nat)
    (hafter : ∀ cut, cut ∈ cuts →
      after cut ≤ post * weight cut)
    (hbefore : (cuts.map before).sum ≤
      head * (charge - post))
    (hhead : (cuts.map weight).sum = head)
    (hpost : post ≤ charge) :
    (cuts.map (fun cut =>
      before cut + after cut)).sum ≤
        head * charge := by
  have hsum :
      ∀ (xs : List α),
        (∀ cut, cut ∈ xs →
          after cut ≤ post * weight cut) →
        (xs.map (fun cut =>
          before cut + after cut)).sum ≤
          (xs.map before).sum +
            post * (xs.map weight).sum := by
    intro xs
    induction xs with
    | nil =>
        intro _
        simp
    | cons cut rest ih =>
        intro hrest
        have hfirst : after cut ≤ post * weight cut :=
          hrest cut (by simp)
        have htail :
            (rest.map (fun x =>
              before x + after x)).sum ≤
            (rest.map before).sum +
              post * (rest.map weight).sum := by
          apply ih
          intro x hx
          exact hrest x (by simp [hx])
        simp only [List.map_cons, List.sum_cons]
        calc
          before cut + after cut +
              (rest.map (fun x =>
                before x + after x)).sum ≤
            (before cut + post * weight cut) +
              ((rest.map before).sum +
                post * (rest.map weight).sum) :=
                  Nat.add_le_add
                    (Nat.add_le_add_left hfirst (before cut))
                    htail
          _ = (before cut + (rest.map before).sum) +
              post * (weight cut +
                (rest.map weight).sum) := by
                  rw [Nat.mul_add]
                  simp only [Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm]
  have hbound := hsum cuts hafter
  calc
    (cuts.map (fun cut =>
      before cut + after cut)).sum ≤
      (cuts.map before).sum +
        post * (cuts.map weight).sum := hbound
    _ = (cuts.map before).sum + head * post := by
      rw [hhead, Nat.mul_comm post head]
    _ ≤ head * (charge - post) + head * post :=
      Nat.add_le_add_right hbefore (head * post)
    _ = head * charge := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hpost]

/-- (D -> B) Original-tape cut decomposition plus the two
open physical budgets imply the success-scale HEAD charge. -/
theorem bankTrialDurationAllKHeadChargeAtSuccessScaleOfBudgets
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hcut : BankTrialDurationKHeadCutLengthCharge
      (q := q) ring root)
    (hpost : BankTrialDurationKHeadPostCutBudget
      (q := q) ring root) :
    BankTrialDurationAllKHeadChargeAtSuccessScale
      (q := q) ring root := by
  intro S hclean hsmall hlarge T
  have hK : 0 < (compileAdvice q).K :=
    Counter.resetColdPrivateKPositive q hsmall
  have hpostFits :
      (8 * (compileAdvice q).b + 11) * n ≤
        (6 * (compileAdvice q).b + 9) *
          ((compileAdvice q).K + 1) * n :=
    bankTrialDurationKHeadPostFitsScale
      (compileAdvice q).b (compileAdvice q).K n hK
  exact Nat.le_trans
    (bankTrialDurationKHeadCostCutDecomposition
      ring root S T)
    (bankTrialDurationKHeadCutPostSumArithmetic
      (Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        (bankTrialDurationKHeadCutStop ring root S)
        T [] (bankTrialLocalStart S))
      (fun cut => cut.length * n ^ (T - cut.length))
      (fun cut =>
        costNumerator (bankTrialLocalNext ring root)
          bankTrialLocalTerminal
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)) (T - cut.length))
      (fun cut => n ^ (T - cut.length))
      (bankTrialProbabilityHeadMass ring root
        (bankTrialLocalStart S) (compileAdvice q).K T)
      ((8 * (compileAdvice q).b + 11) * n)
      ((6 * (compileAdvice q).b + 9) *
        ((compileAdvice q).K + 1) * n)
      (fun cut hmem =>
        hpost S hclean hsmall hlarge
          T cut hmem (T - cut.length))
      (hcut S hclean hsmall hlarge T)
      (bankTrialDurationKHeadMassCutFactorization
        ring root S T).symm
      hpostFits)

/-- 4C'=3B at the success scale, with opaque b,K,n. -/
private theorem bankTrialDurationSuccessScaleCoefficients
    (b K n : Nat) :
    4 * ((6 * b + 9) * (K + 1) * n) =
      3 * ((8 * b + 12) * (K + 1) * n) := by
  have hcoefficient :
      4 * (6 * b + 9) = 3 * (8 * b + 12) := by
    omega
  calc
    4 * ((6 * b + 9) * (K + 1) * n) =
      (4 * (6 * b + 9)) * ((K + 1) * n) := by
        simp only [Nat.mul_assoc]
    _ = (3 * (8 * b + 12)) * ((K + 1) * n) := by
      rw [hcoefficient]
    _ = 3 * ((8 * b + 12) * (K + 1) * n) := by
      simp only [Nat.mul_assoc]

/-- C.8 cancellation: no multiplication tactic sees compileAdvice. -/
private theorem bankTrialDurationSuccessScaleChargeArithmetic
    (success allCost headMass nonfailure mid full : Nat)
    (hsub : success ≤ allCost)
    (hcost : allCost ≤ headMass * mid)
    (hsurvival : 3 * headMass ≤ 4 * nonfailure)
    (hscale : 4 * mid = 3 * full) :
    success ≤ nonfailure * full := by
  have htriple : 3 * success ≤
      3 * (nonfailure * full) := by
    calc
      3 * success ≤ 3 * allCost :=
        Nat.mul_le_mul_left 3 hsub
      _ ≤ 3 * (headMass * mid) :=
        Nat.mul_le_mul_left 3 hcost
      _ = (3 * headMass) * mid := by
        simp only [Nat.mul_assoc]
      _ ≤ (4 * nonfailure) * mid :=
        Nat.mul_le_mul_right mid hsurvival
      _ = nonfailure * (4 * mid) := by
        simp only [Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm]
      _ = nonfailure * (3 * full) := by
        rw [hscale]
      _ = 3 * (nonfailure * full) := by
        simp only [Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm]
  omega

/-- (C) C.8 at coefficient B from charge C' and the
adapted survival coupling; the proof needs no C.6 charge at B. -/
theorem bankTrialDurationSuccessConditionalOfScaleCharge
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hcharge : BankTrialDurationAllKHeadChargeAtSuccessScale
      (q := q) ring root)
    (hsurvival : BankTrialDurationAllKHeadSurvivalEstimate
      (q := q) ring root) :
    BankTrialDurationSuccessConditionalTarget (q := q)
      ring root := by
  intro S hclean T
  exact bankTrialDurationSuccessScaleChargeArithmetic
    (bankTrialDurationSuccessCostMass ring root S T)
    (bankTrialDurationAllKHeadCostMass ring root S T)
    (bankTrialProbabilityHeadMass ring root
      (bankTrialLocalStart S) (compileAdvice q).K T)
    (bankTrialProbabilityWinMass ring root S T +
      bankTrialDurationActiveMass ring root S T)
    ((6 * (compileAdvice q).b + 9) *
      ((compileAdvice q).K + 1) * n)
    ((8 * (compileAdvice q).b + 12) *
      ((compileAdvice q).K + 1) * n)
    (bankTrialDurationSuccessCostLeAllKHeadCost
      ring root S hclean hsmall hlarge T)
    (hcharge S hclean hsmall hlarge T)
    (hsurvival S hclean hsmall hlarge T)
    (bankTrialDurationSuccessScaleCoefficients
      (compileAdvice q).b (compileAdvice q).K n)

end L3

#print axioms L3.bankTrialDurationSuccessCostLeAllKHeadCost
#print axioms L3.bankTrialDurationAllKHeadChargeAtSuccessScaleOfBudgets
#print axioms L3.bankTrialDurationSuccessConditionalOfScaleCharge

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Every enumerated first K-head cut satisfies the K-head event
at its complete chronological prefix. No probabilistic claim. -/
private theorem bankTrialDurationKHeadCutMemberEventAt
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    ∀ (T : Nat) (pre : List (Fin n))
      (z : BankTrialLocalState q) (cut : List (Fin n)),
      cut ∈ Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        (bankTrialDurationKHeadCutStop ring root S)
        T pre z →
      bankTrialProbabilityHeadEvent ring root
        (pre ++ cut) (compileAdvice q).K
        (bankTrialLocalStart S) := by
  intro T
  induction T with
  | zero =>
      intro pre z cut hcut
      by_cases hs :
          bankTrialDurationKHeadCutStop ring root S pre z = true
      · have hnil : cut = [] := by
          simpa only [Prob.firstStoppedPrefixes,
            if_pos hs, List.mem_singleton] using hcut
        rw [hnil, List.append_nil]
        change decide (bankTrialProbabilityHeadEvent
          ring root pre (compileAdvice q).K
            (bankTrialLocalStart S)) = true at hs
        exact of_decide_eq_true hs
      · have hempty : cut ∈
            ([] : List (List (Fin n))) := by
          simpa only [Prob.firstStoppedPrefixes,
            if_neg hs] using hcut
        cases hempty
  | succ t ih =>
      intro pre z cut hcut
      by_cases hs :
          bankTrialDurationKHeadCutStop ring root S pre z = true
      · have hnil : cut = [] := by
          simpa only [Prob.firstStoppedPrefixes,
            if_pos hs, List.mem_singleton] using hcut
        rw [hnil, List.append_nil]
        change decide (bankTrialProbabilityHeadEvent
          ring root pre (compileAdvice q).K
            (bankTrialLocalStart S)) = true at hs
        exact of_decide_eq_true hs
      · have hflat : cut ∈
            (List.ofFn (fun e : Fin n => e)).flatMap
              (fun e =>
                (Prob.firstStoppedPrefixes
                  (bankTrialLocalNext ring root)
                  (bankTrialDurationKHeadCutStop ring root S)
                  t (pre ++ [e])
                  (bankTrialLocalNext ring root z e)).map
                    (List.cons e)) := by
          simpa only [Prob.firstStoppedPrefixes,
            if_neg hs] using hcut
        obtain ⟨e, _, hem⟩ := List.mem_flatMap.mp hflat
        obtain ⟨tail, htail, heq⟩ := List.mem_map.mp hem
        rw [← heq]
        have hnext := ih (pre ++ [e])
          (bankTrialLocalNext ring root z e) tail htail
        simpa only [List.append_assoc, List.singleton_append]
          using hnext

/-- An actual first-stop prefix has exactly K paid heads.
The lower bound is event soundness and the upper bound is the
CLEAN chronological head cap, not a new probability estimate. -/
theorem bankTrialDurationKHeadFirstCutCountExact
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsmall : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (T : Nat) (cut : List (Fin n))
    (hcut : cut ∈ Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root)
      (bankTrialDurationKHeadCutStop ring root S)
      T [] (bankTrialLocalStart S)) :
    bankTrialLiveHeadCount ring root cut
      (bankTrialLocalStart S) = (compileAdvice q).K := by
  have hevent :
      bankTrialProbabilityHeadEvent ring root cut
        (compileAdvice q).K (bankTrialLocalStart S) := by
    simpa only [List.nil_append] using
      (bankTrialDurationKHeadCutMemberEventAt
        ring root S T [] (bankTrialLocalStart S) cut hcut)
  exact Nat.le_antisymm
    (bankTrialC5ActualAllWordsHeadCap
      ring root S hsmall hlarge hwidth hclean cut)
    (bankTrialDurationHeadEventCountLower
      ring root cut (compileAdvice q).K
      (bankTrialLocalStart S) hevent)

/-- A CLEAN first K-head cut has no later ARMED outgoing gate,
even along arbitrary original-tape suffixes. At such a gate
one more root letter would violate the global K head cap. -/
theorem bankTrialDurationKHeadCutNoLaterArmedGate
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsmall : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (T : Nat) (cut : List (Fin n))
    (hcut : cut ∈ Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root)
      (bankTrialDurationKHeadCutStop ring root S)
      T [] (bankTrialLocalStart S))
    (suffix : List (Fin n)) :
    ¬ BankTrialProbabilityArmedGate
      (bankTrialLocalRun ring root suffix
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S))) := by
  intro hgate
  have hcount := bankTrialDurationKHeadFirstCutCountExact
    ring root S hsmall hlarge hwidth hclean T cut hcut
  have hmon :
      (compileAdvice q).K ≤
        bankTrialLiveHeadCount ring root (cut ++ suffix)
          (bankTrialLocalStart S) := by
    rw [bankTrialLiveHeadCountAppend, hcount]
    exact Nat.le_add_right _ _
  have hgateFull : BankTrialProbabilityArmedGate
      (bankTrialLocalRun ring root (cut ++ suffix)
        (bankTrialLocalStart S)) := by
    rw [bankTrialLocalRunAppend]
    exact hgate
  have hcap := bankTrialC5ActualAllWordsHeadCap
    ring root S hsmall hlarge hwidth hclean
    ((cut ++ suffix) ++ [root])
  rw [bankTrialC5StrengthenedSnocHeads,
    if_pos (show BankTrialProbabilityArmedGate
        (bankTrialLocalRun ring root (cut ++ suffix)
          (bankTrialLocalStart S)) ∧ root = root
      from ⟨hgateFull, rfl⟩)] at hcap
  have hbad : (compileAdvice q).K + 1 ≤
      (compileAdvice q).K :=
    Nat.le_trans (Nat.add_le_add_right hmon 1) hcap
  exact (Nat.lt_irrefl (compileAdvice q).K)
    (Nat.lt_of_lt_of_le
      (Nat.lt_succ_self (compileAdvice q).K) hbad)

/-- An original phase/class-zero state is precisely an
ARMED LIVE gate; the reverse implication is not needed here. -/
private theorem bankTrialDurationKHeadClassZeroArmedGate
    {q : Nat} (z : BankTrialLocalState q)
    (hzero : bankTrialDurationClass z = 0) :
    BankTrialProbabilityArmedGate z := by
  cases z with
  | mk B phase =>
      cases phase with
      | live begun =>
          change (if (B.fields ⟨0, by omega⟩).1 = .ARMED
            then 0 else 1) = 0 at hzero
          by_cases hm : (B.fields ⟨0, by omega⟩).1 = .ARMED
          · exact ⟨⟨begun, rfl⟩, hm⟩
          · simp only [if_neg hm] at hzero
            cases hzero
      | recovery =>
          cases hzero
      | won =>
          cases hzero
      | lost =>
          cases hzero

/-- Hence the head-refill term in the rank drift is zero at
every future state from an actual K-head first cut. -/
theorem bankTrialDurationKHeadCutNoLaterClassZero
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsmall : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (T : Nat) (cut : List (Fin n))
    (hcut : cut ∈ Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root)
      (bankTrialDurationKHeadCutStop ring root S)
      T [] (bankTrialLocalStart S))
    (suffix : List (Fin n)) :
    bankTrialDurationClass
      (bankTrialLocalRun ring root suffix
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S))) ≠ 0 := by
  intro hzero
  exact bankTrialDurationKHeadCutNoLaterArmedGate
    ring root S hsmall hlarge hwidth hclean
    T cut hcut suffix
    (bankTrialDurationKHeadClassZeroArmedGate _ hzero)

/-- Opaque-coefficient accounting for the alternative rank route:
race n, remaining worker rank (4b+5)n, and half of the LIVE
recovery occupation credit 8bn give (8b+6)n, within (8b+11)n.
This arithmetic is not the unproved cut-state drift transfer. -/
theorem bankTrialDurationKHeadPotentialPostAllowance
    (b n : Nat) :
    n + ((4 * b + 5) * n) + ((4 * b) * n) ≤
      (8 * b + 11) * n := by
  have hscalar :
      1 + (4 * b + 5) + 4 * b ≤ 8 * b + 11 := by
    omega
  calc
    n + ((4 * b + 5) * n) + ((4 * b) * n) =
      (1 + (4 * b + 5) + 4 * b) * n := by
        rw [Nat.add_mul (1 + (4 * b + 5)) (4 * b) n,
          Nat.add_mul 1 (4 * b + 5) n, Nat.one_mul]
    _ ≤ (8 * b + 11) * n :=
      Nat.mul_le_mul_right n hscalar

end L3

#print axioms L3.bankTrialDurationKHeadFirstCutCountExact
#print axioms L3.bankTrialDurationKHeadCutNoLaterArmedGate
#print axioms L3.bankTrialDurationKHeadCutNoLaterClassZero
#print axioms L3.bankTrialDurationKHeadPotentialPostAllowance

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- No strictly earlier prefix of a first-stop cut can already
satisfy the K-head event. The proof is over the physical
firstStoppedPrefixes recursion, not a fresh scheduler. -/
private theorem bankTrialDurationKHeadFirstCutNoProperPrefix
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    ∀ (T : Nat) (pre : List (Fin n))
      (z : BankTrialLocalState q) (cut : List (Fin n)),
      cut ∈ Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        (bankTrialDurationKHeadCutStop ring root S)
        T pre z →
      ∀ (u v : List (Fin n)),
        cut = u ++ v → v ≠ [] →
        ¬ bankTrialProbabilityHeadEvent ring root
          (pre ++ u) (compileAdvice q).K
          (bankTrialLocalStart S) := by
  intro T
  induction T with
  | zero =>
      intro pre z cut hcut u v heq hne
      by_cases hs :
          bankTrialDurationKHeadCutStop ring root S pre z = true
      · have hnil : cut = [] := by
          simpa only [Prob.firstStoppedPrefixes,
            if_pos hs, List.mem_singleton] using hcut
        rw [hnil] at heq
        have hv : v = [] := by
          cases u with
          | nil =>
              simpa only [List.nil_append] using heq.symm
          | cons e rest =>
              have hf : ([] : List (Fin n)) =
                  e :: (rest ++ v) := by
                    simpa only [List.cons_append] using heq
              cases hf
        exact False.elim (hne hv)
      · have hempty : cut ∈
            ([] : List (List (Fin n))) := by
          simpa only [Prob.firstStoppedPrefixes,
            if_neg hs] using hcut
        cases hempty
  | succ t ih =>
      intro pre z cut hcut u v heq hne
      by_cases hs :
          bankTrialDurationKHeadCutStop ring root S pre z = true
      · have hnil : cut = [] := by
          simpa only [Prob.firstStoppedPrefixes,
            if_pos hs, List.mem_singleton] using hcut
        rw [hnil] at heq
        have hv : v = [] := by
          cases u with
          | nil =>
              simpa only [List.nil_append] using heq.symm
          | cons e rest =>
              have hf : ([] : List (Fin n)) =
                  e :: (rest ++ v) := by
                    simpa only [List.cons_append] using heq
              cases hf
        exact False.elim (hne hv)
      · have hflat : cut ∈
            (List.ofFn (fun e : Fin n => e)).flatMap
              (fun e =>
                (Prob.firstStoppedPrefixes
                  (bankTrialLocalNext ring root)
                  (bankTrialDurationKHeadCutStop ring root S)
                  t (pre ++ [e])
                  (bankTrialLocalNext ring root z e)).map
                    (List.cons e)) := by
          simpa only [Prob.firstStoppedPrefixes,
            if_neg hs] using hcut
        obtain ⟨e, _, hem⟩ := List.mem_flatMap.mp hflat
        obtain ⟨tail, htail, hshape⟩ := List.mem_map.mp hem
        rw [← hshape] at heq
        cases u with
        | nil =>
            have hs' : ¬ bankTrialProbabilityHeadEvent ring root pre
                (compileAdvice q).K (bankTrialLocalStart S) := by
              intro h
              apply hs
              unfold bankTrialDurationKHeadCutStop
              exact decide_eq_true h
            simpa only [List.append_nil] using hs'
        | cons f u =>
            have heqstep : e :: tail = f :: (u ++ v) := by
              simpa only [List.cons_append] using heq
            have hparts := List.cons.inj heqstep
            obtain ⟨hef, hrest⟩ := hparts
            subst f
            have hnext := ih (pre ++ [e])
              (bankTrialLocalNext ring root z e)
              tail htail u v hrest hne
            simpa only [List.append_assoc,
              List.singleton_append] using hnext

/-- (i) The first *actual* K-head cut is exactly the outgoing
root service at an authentic LIVE/ARMED gate. Hence its
postservice state is LIVE, not a later WON/LOST extension. -/
theorem bankTrialDurationKHeadFirstCutLive
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsmall : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (T : Nat) (cut : List (Fin n))
    (hcut : cut ∈ Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root)
      (bankTrialDurationKHeadCutStop ring root S)
      T [] (bankTrialLocalStart S)) :
    ∃ begun : Bool,
      (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S)).phase = .live begun := by
  have hevent :
      bankTrialProbabilityHeadEvent ring root cut
        (compileAdvice q).K (bankTrialLocalStart S) := by
    simpa only [List.nil_append] using
      (bankTrialDurationKHeadCutMemberEventAt
        ring root S T [] (bankTrialLocalStart S) cut hcut)
  obtain ⟨pre, tail, hword, hgate, hcount⟩ :=
    bankTrialDurationKHeadEventCut
      ring root S hsmall cut hevent
  have hprefixCount :
      (compileAdvice q).K ≤
        bankTrialLiveHeadCount ring root (pre ++ [root])
          (bankTrialLocalStart S) := by
    rw [bankTrialC5StrengthenedSnocHeads,
      if_pos (show BankTrialProbabilityArmedGate
          (bankTrialLocalRun ring root pre
            (bankTrialLocalStart S)) ∧ root = root
        from ⟨hgate, rfl⟩)]
    exact Nat.le_of_eq hcount.symm
  have hprefixEvent :
      bankTrialProbabilityHeadEvent ring root
        (pre ++ [root]) (compileAdvice q).K
        (bankTrialLocalStart S) :=
    bankTrialDurationCleanCountImpliesHeadEvent
      ring root S hclean (pre ++ [root]) []
      (bankTrialLocalStart S) (compileAdvice q).K
      rfl hprefixCount
  have htail : tail = [] := by
    by_cases hnil : tail = []
    · exact hnil
    · have hshape : cut = (pre ++ [root]) ++ tail := by
        rw [hword]
        simp only [List.append_assoc, List.singleton_append]
      have hnot := bankTrialDurationKHeadFirstCutNoProperPrefix
        ring root S T [] (bankTrialLocalStart S) cut
        hcut (pre ++ [root]) tail hshape hnil
      exact False.elim
        (hnot (by simpa only [List.nil_append] using hprefixEvent))
  have hcutEq : cut = pre ++ [root] := by
    rw [hword, htail]
  have hstart := bankTrialSuccessReachableArmedStart
    ring root S hlarge hclean pre
    (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
    rfl hgate
  cases hbit : bankTrialLiveWaveBit
      (bankTrialLocalRun ring root pre
        (bankTrialLocalStart S)).bank
      ⟨0, bankTrialWindowWidthPos q⟩ with
  | false =>
      have hzero := bankTrialC5ArmedHeadZeroCStart
        ring root
        (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
        hstart hbit
      obtain ⟨begun, hphase⟩ := hzero.live
      refine ⟨begun, ?_⟩
      rw [hcutEq, bankTrialLocalRunAppend]
      change (bankTrialLocalNext ring root
        (bankTrialLocalRun ring root pre
          (bankTrialLocalStart S)) root).phase = .live begun
      exact hphase
  | true =>
      have hone := bankTrialC5ArmedHeadOneStage
        ring root
        (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
        hstart hbit
      obtain ⟨begun, hphase⟩ := hone.1
      refine ⟨begun, ?_⟩
      rw [hcutEq, bankTrialLocalRunAppend]
      change (bankTrialLocalNext ring root
        (bankTrialLocalRun ring root pre
          (bankTrialLocalStart S)) root).phase = .live begun
      exact hphase

/-- A terminal local observer has zero recovery occupation and
its abstract recovery clock is done. This reexports the
same-file-private terminal calculation at an accessible name. -/
theorem bankTrialDurationKHeadRecoveryTwinTerminalClock {n q : Nat}
    (z : BankTrialLocalState q)
    (ht : bankTrialLocalTerminal z) :
    bankTrialDurationRecoveryTwinOccupation n z =
      bankTrialDurationRecoveryTwinPotential
        (compileAdvice q).b n
        (bankTrialDurationRecoveryClockOf z) := by
  have hc : bankTrialDurationRecoveryClockOf z = .done := by
    unfold bankTrialDurationRecoveryClockOf
    simp only [if_pos ht]
  rw [hc]
  simp only [bankTrialDurationRecoveryTwinOccupation,
    if_pos ht, bankTrialDurationRecoveryTwinPotential]

/-- (ii.a) The exact 2-charged recovery Bellman inequality
on every CLEAN-reachable original BANK state. Its witness is
the concrete TwinOccupation, not an existentially chosen
potential whose cut value could be arbitrarily large. -/
theorem bankTrialDurationKHeadRecoveryTwinDrift
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    ∀ (z : BankTrialLocalState q),
      BankTrialDurationReachable ring root S z →
      ¬ bankTrialLocalTerminal z →
      2 * n *
          (if bankTrialDurationClass z = 2 then 1 else 0) +
        (List.ofFn (fun e : Fin n =>
          bankTrialDurationRecoveryTwinOccupation n
            (bankTrialLocalNext ring root z e))).sum ≤
        n * bankTrialDurationRecoveryTwinOccupation n z := by
  classical
  intro z hz hnot
  by_cases hrec : z.phase = .recovery
  · have hrows := bankTrialDurationRecoveryAllRowsNonalias
      ring root hsmall hw
    have hf := bankTrialDurationRecoveryReachableFrontHolds
      ring root hsmall hw S hclean z hz hrec
    have hclass : bankTrialDurationClass z = 2 :=
      (bankTrialDurationNonterminalRecoveryClass z hnot).2 hrec
    have hchild (e : Fin n) :
        bankTrialDurationRecoveryTwinOccupation n
          (bankTrialLocalNext ring root z e) =
        bankTrialDurationRecoveryTwinPotential
          (compileAdvice q).b n
          (bankTrialDurationRecoveryClockNext
            (compileAdvice q).b root
            (Counter.site ring root (n - 1))
            (bankTrialDurationRecoveryNominated ring root z)
            e (bankTrialDurationRecoveryClockOf z)) := by
      have hrow := hrows z e hf
      have heq :
          bankTrialDurationRecoveryTwinOccupation n
            (bankTrialLocalNext ring root z e) =
          bankTrialDurationRecoveryTwinPotential
            (compileAdvice q).b n
            (bankTrialDurationRecoveryClockOf
              (bankTrialLocalNext ring root z e)) := by
        rcases hrow.1 with ht | hfnext
        · exact bankTrialDurationKHeadRecoveryTwinTerminalClock
            (bankTrialLocalNext ring root z e) ht
        · exact bankTrialDurationRecoveryTwinOccupationFront
            (bankTrialLocalNext ring root z e) hfnext
      exact heq.trans (congrArg
        (bankTrialDurationRecoveryTwinPotential
          (compileAdvice q).b n) hrow.2)
    have hsum := FiniteUniformStoppingTree.ofFn_sum_eq
      (fun e : Fin n =>
        bankTrialDurationRecoveryTwinOccupation n
          (bankTrialLocalNext ring root z e))
      (fun e : Fin n =>
        bankTrialDurationRecoveryTwinPotential
          (compileAdvice q).b n
          (bankTrialDurationRecoveryClockNext
            (compileAdvice q).b root
            (Counter.site ring root (n - 1))
            (bankTrialDurationRecoveryNominated ring root z)
            e (bankTrialDurationRecoveryClockOf z))) hchild
    have hports :=
      bankTrialDurationRecoveryTwinPortSumHolds ring root hw z hf
    have hbellman :=
      bankTrialDurationRecoveryTwinFrontBellman
        ring root hw z hf
    have hcost :
        2 * n +
          (List.ofFn (fun e : Fin n =>
            bankTrialDurationRecoveryTwinOccupation n
              (bankTrialLocalNext ring root z e))).sum ≤
        n * bankTrialDurationRecoveryTwinOccupation n z := by
      calc
        2 * n +
            (List.ofFn (fun e : Fin n =>
              bankTrialDurationRecoveryTwinOccupation n
                (bankTrialLocalNext ring root z e))).sum =
          2 * n +
            (List.ofFn (fun e : Fin n =>
              bankTrialDurationRecoveryTwinPotential
                (compileAdvice q).b n
                (bankTrialDurationRecoveryClockNext
                  (compileAdvice q).b root
                  (Counter.site ring root (n - 1))
                  (bankTrialDurationRecoveryNominated ring root z)
                  e (bankTrialDurationRecoveryClockOf z)))).sum := by
                    rw [hsum]
        _ ≤ 2 * n +
            bankTrialDurationRecoveryTwinRowSum
              (compileAdvice q).b n
              (bankTrialDurationRecoveryClockOf z) :=
            Nat.add_le_add_left hports _
        _ ≤ n * bankTrialDurationRecoveryTwinPotential
              (compileAdvice q).b n
              (bankTrialDurationRecoveryClockOf z) := hbellman
        _ = n * bankTrialDurationRecoveryTwinOccupation n z := by
            rw [bankTrialDurationRecoveryTwinOccupationFront z hf]
    simpa only [hclass, if_pos rfl, ↓reduceIte, Nat.mul_one]
      using hcost
  · have hclass : bankTrialDurationClass z ≠ 2 := by
      intro hc
      exact hrec
        ((bankTrialDurationNonterminalRecoveryClass z hnot).1 hc)
    have hpot :
        bankTrialDurationRecoveryTwinOccupation n z =
          8 * (compileAdvice q).b * n := by
      simp only [bankTrialDurationRecoveryTwinOccupation,
        if_neg hnot, if_neg hrec]
    have hlive : ∃ begun : Bool, z.phase = .live begun := by
      cases hp : z.phase with
      | live begun => exact ⟨begun, rfl⟩
      | recovery => exact False.elim (hrec hp)
      | won => exact False.elim (hnot (Or.inl hp))
      | lost => exact False.elim (hnot (Or.inr hp))
    have hchild (e : Fin n) :
        bankTrialDurationRecoveryTwinOccupation n
            (bankTrialLocalNext ring root z e) ≤
          8 * (compileAdvice q).b * n := by
      by_cases ht :
          bankTrialLocalTerminal (bankTrialLocalNext ring root z e)
      · simpa only [bankTrialDurationRecoveryTwinOccupation,
          if_pos ht] using
            (Nat.zero_le (8 * (compileAdvice q).b * n))
      · by_cases hr :
            (bankTrialLocalNext ring root z e).phase = .recovery
        · have hfnext :=
            bankTrialDurationRecoveryFirstEntryFrontHolds
              ring root hsmall hw S hclean z hz e hlive hr
          have hm :
              bankTrialLiveWaveRootMode
                (bankTrialLocalNext ring root z e).bank =
                  .RESET := by
            rcases hlive with ⟨begun, hp⟩
            cases z with
            | mk B phase =>
              cases hp
              change
                ((bankTrialLocalNext ring root
                  (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank.fields
                  ⟨0, by omega⟩).1 = .RESET
              rw [bankTrialLocalNextLiveBank]
              exact bankTrialLocalLiveRecoveryRoot
                ring root e B begun hr
          have hclock :=
            bankTrialDurationRecoveryClockResetOfFront
              (bankTrialLocalNext ring root z e) hfnext hm
          apply Nat.le_of_eq
          calc
            bankTrialDurationRecoveryTwinOccupation n
                (bankTrialLocalNext ring root z e) =
              bankTrialDurationRecoveryTwinPotential
                (compileAdvice q).b n
                (bankTrialDurationRecoveryClockOf
                  (bankTrialLocalNext ring root z e)) :=
              bankTrialDurationRecoveryTwinOccupationFront
                (bankTrialLocalNext ring root z e) hfnext
            _ = 8 * (compileAdvice q).b * n := by
              rw [hclock]
              simp only [bankTrialDurationRecoveryTwinPotential]
              exact Nat.mul_comm _ _
        · simpa only [bankTrialDurationRecoveryTwinOccupation,
            if_neg ht, if_neg hr] using
              (Nat.le_refl (8 * (compileAdvice q).b * n))
    have hsum := FiniteUniformStoppingTree.ofFn_sum_le
      (fun e : Fin n =>
        bankTrialDurationRecoveryTwinOccupation n
          (bankTrialLocalNext ring root z e))
      (fun _ : Fin n => 8 * (compileAdvice q).b * n) hchild
    rw [FiniteUniformStoppingTree.ofFn_sum_const] at hsum
    simpa only [if_neg hclass, Nat.mul_zero, Nat.zero_add,
      hpot] using hsum

/-- The G12c rank rows, now exposed for a reachable
post-head state rather than just the CLEAN seed. -/
private theorem bankTrialDurationKHeadWorkerRows
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b) :
    BankTrialDurationWorkerRankEdgeRows (q := q)
      ring root := by
  exact bankTrialDurationRankRowsOfLeaseAwareNoOrphan
    ring root
    (bankTrialDurationNoReachableOrphanHolds
      ring root hsmall hw hpositive hwidth)
    (bankTrialDurationLeaseAwareRowsOfWeakAndServiceCoverage
      ring root hw
      (bankTrialDurationClassOneReferenceWeakRowsHolds
        ring root hw hpositive hwidth)
      (bankTrialDurationClassOneServiceCoverageHolds
        ring root hw hpositive hwidth))

/-- At an original observer state with no class zero, its
class is one or two. No Mathlib bound on this finite case is
needed. -/
private theorem bankTrialDurationKHeadClassOneOrTwo
    {q : Nat} (z : BankTrialLocalState q)
    (hzero : bankTrialDurationClass z ≠ 0) :
    bankTrialDurationClass z = 1 ∨
      bankTrialDurationClass z = 2 := by
  cases z with
  | mk B phase =>
      cases phase with
      | live begun =>
          by_cases hm : (B.fields ⟨0, by omega⟩).1 = .ARMED
          · have hfalse : bankTrialDurationClass
                (⟨B, .live begun⟩ : BankTrialLocalState q) = 0 := by
              change (if (B.fields ⟨0, by omega⟩).1 =
                .ARMED then 0 else 1) = 0
              rw [if_pos hm]
            exact False.elim (hzero hfalse)
          · left
            change (if (B.fields ⟨0, by omega⟩).1 =
              .ARMED then 0 else 1) = 1
            rw [if_neg hm]
      | recovery => exact Or.inr rfl
      | won => exact Or.inr rfl
      | lost => exact Or.inr rfl

/-- (ii.b) Combination of the original worker rank and the
two-charged recovery potential. Since class zero is excluded,
the worker's head-refill term disappears exactly. -/
private theorem bankTrialDurationKHeadCombinedDrift
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hrows : BankTrialDurationWorkerRankEdgeRows
      (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (z : BankTrialLocalState q)
    (hz : BankTrialDurationReachable ring root S z)
    (hzero : bankTrialDurationClass z ≠ 0)
    (hnot : ¬ bankTrialLocalTerminal z) :
    2 * n + (List.ofFn (fun e : Fin n =>
      2 * bankTrialDurationWorkerRankPotential n
        (bankTrialLocalNext ring root z e) +
      bankTrialDurationRecoveryTwinOccupation n
        (bankTrialLocalNext ring root z e))).sum ≤
    n * (2 * bankTrialDurationWorkerRankPotential n z +
      bankTrialDurationRecoveryTwinOccupation n z) := by
  have hwcost :
      n * (if bankTrialDurationClass z = 1 then 1 else 0) +
        (List.ofFn (fun e : Fin n =>
          bankTrialDurationWorkerRankPotential n
            (bankTrialLocalNext ring root z e))).sum ≤
        n * bankTrialDurationWorkerRankPotential n z := by
    have h := bankTrialDurationWorkerPotentialDriftOfEdges
      ring root hrows S hclean z hz hnot
    rw [if_neg hzero, Nat.mul_zero, Nat.add_zero] at h
    exact h
  have hrec := bankTrialDurationKHeadRecoveryTwinDrift
    ring root hsmall hw S hclean z hz hnot
  have hcases :=
    bankTrialDurationKHeadClassOneOrTwo z hzero
  have hcredit :
      (if bankTrialDurationClass z = 1 then 1 else 0) +
        (if bankTrialDurationClass z = 2 then 1 else 0) = 1 := by
    rcases hcases with hone | htwo
    · simp [hone]
    · simp [htwo]
  have hfirst :
      2 * n * (if bankTrialDurationClass z = 1 then 1 else 0) +
        (List.ofFn (fun e : Fin n =>
          2 * bankTrialDurationWorkerRankPotential n
            (bankTrialLocalNext ring root z e))).sum ≤
        2 * (n * bankTrialDurationWorkerRankPotential n z) := by
    calc
      2 * n * (if bankTrialDurationClass z = 1 then 1 else 0) +
          (List.ofFn (fun e : Fin n =>
            2 * bankTrialDurationWorkerRankPotential n
              (bankTrialLocalNext ring root z e))).sum =
        2 * (n * (if bankTrialDurationClass z = 1 then 1 else 0) +
          (List.ofFn (fun e : Fin n =>
            bankTrialDurationWorkerRankPotential n
              (bankTrialLocalNext ring root z e))).sum) := by
            rw [ofFn_sum_mul_left, Nat.mul_add]
            simp only [Nat.mul_assoc]
      _ ≤ 2 * (n * bankTrialDurationWorkerRankPotential n z) :=
        Nat.mul_le_mul_left 2 hwcost
  have hcredits :
      2 * n * (if bankTrialDurationClass z = 1 then 1 else 0) +
        2 * n * (if bankTrialDurationClass z = 2 then 1 else 0) =
      2 * n := by
    calc
      2 * n * (if bankTrialDurationClass z = 1 then 1 else 0) +
          2 * n * (if bankTrialDurationClass z = 2 then 1 else 0) =
        2 * n * ((if bankTrialDurationClass z = 1 then 1 else 0) +
          (if bankTrialDurationClass z = 2 then 1 else 0)) := by
            rw [Nat.mul_add]
      _ = 2 * n := by rw [hcredit, Nat.mul_one]
  calc
    2 * n + (List.ofFn (fun e : Fin n =>
        2 * bankTrialDurationWorkerRankPotential n
          (bankTrialLocalNext ring root z e) +
        bankTrialDurationRecoveryTwinOccupation n
          (bankTrialLocalNext ring root z e))).sum =
      (2 * n *
          (if bankTrialDurationClass z = 1 then 1 else 0) +
        (List.ofFn (fun e : Fin n =>
          2 * bankTrialDurationWorkerRankPotential n
            (bankTrialLocalNext ring root z e))).sum) +
      (2 * n *
          (if bankTrialDurationClass z = 2 then 1 else 0) +
        (List.ofFn (fun e : Fin n =>
          bankTrialDurationRecoveryTwinOccupation n
            (bankTrialLocalNext ring root z e))).sum) := by
            rw [ofFn_sum_add]
            conv => lhs; rw [← hcredits]
            simp only [Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm]
    _ ≤ 2 * (n * bankTrialDurationWorkerRankPotential n z) +
        n * bankTrialDurationRecoveryTwinOccupation n z :=
      Nat.add_le_add hfirst hrec
    _ = n * (2 * bankTrialDurationWorkerRankPotential n z +
        bankTrialDurationRecoveryTwinOccupation n z) := by
      simp only [Nat.mul_add, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm]

/-- (ii.c) A generic twice-charged stopped-clock induction
starting at any reachable state whose *entire future* has no
class-zero gate. This is on the same original Fin n alphabet. -/
private theorem bankTrialDurationKHeadCutRelativeTwiceCost
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (potential : BankTrialLocalState q → Nat)
    (hdrift : ∀ z : BankTrialLocalState q,
      BankTrialDurationReachable ring root S z →
      (∀ w : List (Fin n),
        bankTrialDurationClass
          (bankTrialLocalRun ring root w z) ≠ 0) →
      ¬ bankTrialLocalTerminal z →
      2 * n + (List.ofFn (fun e : Fin n =>
        potential (bankTrialLocalNext ring root z e))).sum ≤
        n * potential z) :
    ∀ (t : Nat) (z : BankTrialLocalState q),
      BankTrialDurationReachable ring root S z →
      (∀ w : List (Fin n),
        bankTrialDurationClass
          (bankTrialLocalRun ring root w z) ≠ 0) →
      2 * costNumerator (bankTrialLocalNext ring root)
        bankTrialLocalTerminal z t ≤ n ^ t * potential z := by
  intro t
  induction t with
  | zero =>
      intro z _ _
      change 2 * Prob.scheduleSum n 0
        (costWord (bankTrialLocalNext ring root)
          bankTrialLocalTerminal z) ≤ n ^ 0 * potential z
      rw [bankTrialProbabilityScheduleSumZero]
      simp only [costWord,
        K2FiniteSafeEliminationExpected.rawCost, Nat.mul_zero]
      exact Nat.zero_le _
  | succ t ih =>
      intro z hz hno
      by_cases ht : bankTrialLocalTerminal z
      · have hfun :
            costWord (bankTrialLocalNext ring root)
                bankTrialLocalTerminal z =
              (fun _ : List (Fin n) => 0) := by
          funext w
          exact costWord_terminal
            (bankTrialLocalNext ring root)
            bankTrialLocalTerminal z ht w
        change 2 * Prob.scheduleSum n (t + 1)
          (costWord (bankTrialLocalNext ring root)
            bankTrialLocalTerminal z) ≤
          n ^ (t + 1) * potential z
        rw [hfun, bankTrialProbabilityScheduleSumConst]
        simp only [Nat.mul_zero]
        exact Nat.zero_le _
      · have hnext (e : Fin n) :
            BankTrialDurationReachable ring root S
              (bankTrialLocalNext ring root z e) :=
          bankTrialDurationReachableNext ring root S z hz e
        have hnoNext (e : Fin n) (w : List (Fin n)) :
            bankTrialDurationClass
              (bankTrialLocalRun ring root w
                (bankTrialLocalNext ring root z e)) ≠ 0 :=
          hno (e :: w)
        have hstep (e : Fin n) :
            Prob.scheduleSum n t (fun w =>
              costWord (bankTrialLocalNext ring root)
                bankTrialLocalTerminal z (e :: w)) =
              n ^ t +
                costNumerator (bankTrialLocalNext ring root)
                  bankTrialLocalTerminal
                  (bankTrialLocalNext ring root z e) t := by
          have hfun :
              (fun w : List (Fin n) =>
                costWord (bankTrialLocalNext ring root)
                  bankTrialLocalTerminal z (e :: w)) =
              (fun w : List (Fin n) =>
                1 + costWord (bankTrialLocalNext ring root)
                  bankTrialLocalTerminal
                  (bankTrialLocalNext ring root z e) w) := by
            funext w
            simp only [costWord,
              K2FiniteSafeEliminationExpected.rawCost, if_neg ht]
          rw [hfun, bankTrialC5ScheduleSumAdd,
            bankTrialProbabilityScheduleSumConst]
          simp only [Nat.mul_one]
          rfl
        have hcostEq :
            costNumerator (bankTrialLocalNext ring root)
                bankTrialLocalTerminal z (t + 1) =
              n * n ^ t +
              (List.ofFn (fun e : Fin n =>
                costNumerator (bankTrialLocalNext ring root)
                  bankTrialLocalTerminal
                  (bankTrialLocalNext ring root z e) t)).sum := by
          change Prob.scheduleSum n (t + 1)
              (costWord (bankTrialLocalNext ring root)
                bankTrialLocalTerminal z) = _
          rw [bankTrialProbabilityScheduleSumFirst]
          have heq := ofFn_sum_eq
            (fun e : Fin n =>
              Prob.scheduleSum n t (fun w =>
                costWord (bankTrialLocalNext ring root)
                  bankTrialLocalTerminal z (e :: w)))
            (fun e : Fin n =>
              n ^ t +
                costNumerator (bankTrialLocalNext ring root)
                  bankTrialLocalTerminal
                  (bankTrialLocalNext ring root z e) t)
            hstep
          rw [heq, ofFn_sum_add, ofFn_sum_const]
        have hchildren :
            2 * (List.ofFn (fun e : Fin n =>
              costNumerator (bankTrialLocalNext ring root)
                bankTrialLocalTerminal
                (bankTrialLocalNext ring root z e) t)).sum ≤
            n ^ t * (List.ofFn (fun e : Fin n =>
              potential (bankTrialLocalNext ring root z e))).sum := by
          calc
            2 * (List.ofFn (fun e : Fin n =>
                costNumerator (bankTrialLocalNext ring root)
                  bankTrialLocalTerminal
                  (bankTrialLocalNext ring root z e) t)).sum =
              (List.ofFn (fun e : Fin n =>
                2 * costNumerator (bankTrialLocalNext ring root)
                  bankTrialLocalTerminal
                  (bankTrialLocalNext ring root z e) t)).sum := by
                    exact (ofFn_sum_mul_left 2 _).symm
            _ ≤ (List.ofFn (fun e : Fin n =>
                  n ^ t * potential
                    (bankTrialLocalNext ring root z e))).sum :=
              ofFn_sum_le _ _ (fun e =>
                ih (bankTrialLocalNext ring root z e)
                  (hnext e) (hnoNext e))
            _ = n ^ t * (List.ofFn (fun e : Fin n =>
                  potential (bankTrialLocalNext ring root z e))).sum :=
              ofFn_sum_mul_left (n ^ t) _
        calc
          2 * costNumerator (bankTrialLocalNext ring root)
              bankTrialLocalTerminal z (t + 1) =
            2 * (n * n ^ t +
              (List.ofFn (fun e : Fin n =>
                costNumerator (bankTrialLocalNext ring root)
                  bankTrialLocalTerminal
                  (bankTrialLocalNext ring root z e) t)).sum) := by
                    rw [hcostEq]
          _ = n ^ t * (2 * n) +
                2 * (List.ofFn (fun e : Fin n =>
                  costNumerator (bankTrialLocalNext ring root)
                    bankTrialLocalTerminal
                    (bankTrialLocalNext ring root z e) t)).sum := by
                    simp only [Nat.mul_add, Nat.mul_assoc,
                      Nat.mul_comm, Nat.mul_left_comm]
          _ ≤ n ^ t * (2 * n) +
                n ^ t * (List.ofFn (fun e : Fin n =>
                  potential (bankTrialLocalNext ring root z e))).sum :=
              Nat.add_le_add_left hchildren _
          _ = n ^ t * (2 * n +
                (List.ofFn (fun e : Fin n =>
                  potential (bankTrialLocalNext ring root z e))).sum) := by
                    rw [Nat.mul_add]
          _ ≤ n ^ t * (n * potential z) :=
            Nat.mul_le_mul_left _
              (hdrift z hz hno ht)
          _ = n ^ (t + 1) * potential z := by
            rw [Nat.pow_succ]
            simp only [Nat.mul_assoc, Nat.mul_comm,
              Nat.mul_left_comm]

/-- Cancellation by two over opaque Nat variables, so omega
never sees a large exponential term. -/
private theorem bankTrialDurationKHeadTwiceCancel
    (a b : Nat) (h : 2 * a ≤ 2 * b) : a ≤ b := by
  omega

/-- The scalar allowance is proved with opaque b,n only. -/
private theorem bankTrialDurationKHeadCombinedAllowance
    (b n : Nat) :
    2 * ((4 * b + 5) * n) + 8 * b * n ≤
      2 * ((8 * b + 11) * n) := by
  have hc : 2 * (4 * b + 5) + 8 * b ≤
      2 * (8 * b + 11) := by
    omega
  calc
    2 * ((4 * b + 5) * n) + 8 * b * n =
      (2 * (4 * b + 5) + 8 * b) * n := by
        simp only [Nat.add_mul, Nat.mul_assoc]
    _ ≤ (2 * (8 * b + 11)) * n :=
      Nat.mul_le_mul_right n hc
    _ = 2 * ((8 * b + 11) * n) := by
      rw [Nat.mul_assoc]

/-- (ii) Uniform cut-relative stopped cost from any reachable
LIVE state with no future ARMED gate. This is the same
full original scheduler used at the CLEAN seed. -/
theorem bankTrialDurationKHeadCutRelativeStageCost
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hrows : BankTrialDurationWorkerRankEdgeRows
      (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (z : BankTrialLocalState q)
    (hz : BankTrialDurationReachable ring root S z)
    (hlive : ∃ begun : Bool, z.phase = .live begun)
    (hno : ∀ w : List (Fin n),
      bankTrialDurationClass
        (bankTrialLocalRun ring root w z) ≠ 0)
    (t : Nat) :
    costNumerator (bankTrialLocalNext ring root)
      bankTrialLocalTerminal z t ≤
        ((8 * (compileAdvice q).b + 11) * n) * n ^ t := by
  have hworkerCap :
      bankTrialDurationWorkerRankPotential n z ≤
        (4 * (compileAdvice q).b + 5) * n := by
    have hcap := bankTrialDurationWorkerRankPotentialCap n z
    have hc : 2 * (2 * (compileAdvice q).b + 2) + 1 =
        4 * (compileAdvice q).b + 5 := by
      omega
    simpa only [bankTrialDurationWorkerLimit, hc] using hcap
  obtain ⟨begun, hphase⟩ := hlive
  have hnot : ¬ bankTrialLocalTerminal z := by
    intro ht
    rcases ht with hwon | hlost
    · rw [hphase] at hwon
      cases hwon
    · rw [hphase] at hlost
      cases hlost
  have hrec : z.phase ≠ .recovery := by
    intro hr
    rw [hphase] at hr
    cases hr
  have hrecPot :
      bankTrialDurationRecoveryTwinOccupation n z =
        8 * (compileAdvice q).b * n := by
    simp only [bankTrialDurationRecoveryTwinOccupation,
      if_neg hnot, if_neg hrec]
  have hstartCap :
      2 * bankTrialDurationWorkerRankPotential n z +
        bankTrialDurationRecoveryTwinOccupation n z ≤
      2 * ((4 * (compileAdvice q).b + 5) * n) +
        8 * (compileAdvice q).b * n := by
    rw [hrecPot]
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left 2 hworkerCap) _
  have hcost : 2 * costNumerator
      (bankTrialLocalNext ring root)
      bankTrialLocalTerminal z t ≤
      n ^ t * (2 * bankTrialDurationWorkerRankPotential n z +
        bankTrialDurationRecoveryTwinOccupation n z) :=
    bankTrialDurationKHeadCutRelativeTwiceCost
      ring root S
      (fun y => 2 * bankTrialDurationWorkerRankPotential n y +
        bankTrialDurationRecoveryTwinOccupation n y)
      (fun y hy hnoY hnotY =>
        bankTrialDurationKHeadCombinedDrift ring root
          hsmall hw hrows S hclean y hy
          (hnoY []) hnotY)
      t z hz hno
  have htwice :
      2 * costNumerator (bankTrialLocalNext ring root)
          bankTrialLocalTerminal z t ≤
        2 * (((8 * (compileAdvice q).b + 11) * n) * n ^ t) := by
    calc
      2 * costNumerator (bankTrialLocalNext ring root)
          bankTrialLocalTerminal z t ≤
        n ^ t * (2 * bankTrialDurationWorkerRankPotential n z +
          bankTrialDurationRecoveryTwinOccupation n z) := hcost
      _ ≤ n ^ t * (2 * ((4 * (compileAdvice q).b + 5) * n) +
          8 * (compileAdvice q).b * n) :=
        Nat.mul_le_mul_left (n ^ t) hstartCap
      _ ≤ n ^ t * (2 * ((8 * (compileAdvice q).b + 11) * n)) :=
        Nat.mul_le_mul_left (n ^ t)
          (bankTrialDurationKHeadCombinedAllowance
            (compileAdvice q).b n)
      _ = 2 * (((8 * (compileAdvice q).b + 11) * n) * n ^ t) := by
        simp only [Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm]
  exact bankTrialDurationKHeadTwiceCancel _ _ htwice

/-- C.8 part C: the previously open post-cut budget, with
the coefficient unchanged. No additional Prop is assumed. -/
theorem bankTrialDurationKHeadPostCutBudgetHolds
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hpositive : 0 < (compileAdvice q).K)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b) :
    BankTrialDurationKHeadPostCutBudget (q := q)
      ring root := by
  intro S hclean hsmall hlarge T cut hcut t
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hrows : BankTrialDurationWorkerRankEdgeRows
      (q := q) ring root :=
    bankTrialDurationKHeadWorkerRows
      ring root hsmall hw hpositive hwidth
  have hz : BankTrialDurationReachable ring root S
      (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S)) := ⟨cut, rfl⟩
  have hlive := bankTrialDurationKHeadFirstCutLive
    ring root S hsmall hlarge hclean T cut hcut
  have hno := bankTrialDurationKHeadCutNoLaterClassZero
    ring root S hsmall hlarge hwidth hclean T cut hcut
  exact bankTrialDurationKHeadCutRelativeStageCost
    ring root hsmall hw hrows S hclean
    (bankTrialLocalRun ring root cut (bankTrialLocalStart S))
    hz hlive hno t

end L3

#print axioms L3.bankTrialDurationKHeadFirstCutLive
#print axioms L3.bankTrialDurationKHeadRecoveryTwinTerminalClock
#print axioms L3.bankTrialDurationKHeadRecoveryTwinDrift
#print axioms L3.bankTrialDurationKHeadCutRelativeStageCost
#print axioms L3.bankTrialDurationKHeadPostCutBudgetHolds

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- A GOOD first-exit classification has a concrete prefix on the
original scheduler tape where the designated return predicate holds. -/
private theorem bankTrialDurationKHeadFirstGoodPrefix
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (o : BankTrialC5ActualOrigin n q) :
    ∀ (word : List (Fin n)) (z : BankTrialLocalState q),
      bankTrialC5WorkerFirstExit ring root o word z = some true →
      ∃ pre suffix : List (Fin n),
        word = pre ++ suffix ∧
        bankTrialC5ActualReturned o
          (bankTrialLocalRun ring root pre z) := by
  intro word
  induction word with
  | nil =>
      intro z hgood
      by_cases hret : bankTrialC5ActualReturned o z
      · exact ⟨[], [], rfl, hret⟩
      · simp only [bankTrialC5WorkerFirstExit,
          if_neg hret] at hgood
        split at hgood <;> cases hgood
  | cons e tail ih =>
      intro z hgood
      by_cases hret : bankTrialC5ActualReturned o z
      · exact ⟨[], e :: tail, rfl, hret⟩
      · by_cases hbad : bankTrialC5ActualBadExit o z
        · have hfalse :
            bankTrialC5WorkerFirstExit ring root o
              (e :: tail) z = some false := by
            simp [bankTrialC5WorkerFirstExit, hret, hbad]
          rw [hfalse] at hgood
          cases hgood
        · have htail :
            bankTrialC5WorkerFirstExit ring root o tail
              (bankTrialLocalNext ring root z e) = some true := by
            simpa only [bankTrialC5WorkerFirstExit,
              if_neg hret, if_neg hbad] using hgood
          obtain ⟨u, v, hdecomp, hreturned⟩ :=
            ih (bankTrialLocalNext ring root z e) htail
          refine ⟨e :: u, v, ?_, ?_⟩
          · rw [hdecomp]
            rfl
          · change bankTrialC5ActualReturned o
              (bankTrialLocalRun ring root u
                (bankTrialLocalNext ring root z e))
            exact hreturned

/-- The first-bit-one kth HEAD emits an actual K-tagged increment.
This uses the CLEAN origin guard rather than inventing an origin
for a workerless zero-bit HEAD. -/
theorem bankTrialDurationKHeadOneCutSelected
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n))
    (hgate : BankTrialProbabilityArmedGate
      (bankTrialLocalRun ring root pre (bankTrialLocalStart S)))
    (hcount : bankTrialLiveHeadCount ring root pre
      (bankTrialLocalStart S) + 1 = (compileAdvice q).K)
    (hone : bankTrialLiveWaveBit
      (bankTrialLocalRun ring root pre (bankTrialLocalStart S)).bank
        ⟨0, bankTrialWindowWidthPos q⟩ = true) :
    ∃ o : BankTrialC5ActualOrigin n q,
      o ∈ bankTrialDurationKHeadActualStarts ring root S
        (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
        root ∧ o.increment = true := by
  have hstart := bankTrialSuccessReachableArmedStart
    ring root S hlarge hclean pre
    (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
    rfl hgate
  have hstage := bankTrialC5ArmedHeadOneStage ring root
    (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
    hstart hone
  obtain ⟨begun, hlive⟩ := hgate.1
  have hmode : bankTrialLiveWaveRootMode
      (bankTrialLocalRun ring root pre
        (bankTrialLocalStart S)).bank = .ARMED := hgate.2
  obtain ⟨nextBegun, hnextLive⟩ := hstage.1
  have hnextMode :
      bankTrialLiveWaveRootMode
        (bankTrialLocalNext ring root
          (bankTrialLocalRun ring root pre
            (bankTrialLocalStart S)) root).bank = .IWAIT :=
    hstage.2.2.1
  have hguard :
      BankTrialLocalClean q S ∧
      (∃ w : List (Fin n),
        bankTrialLocalRun ring root w (bankTrialLocalStart S) =
          bankTrialLocalRun ring root pre (bankTrialLocalStart S)) ∧
      root = root ∧
      (∃ oldBegun newBegun : Bool,
        (bankTrialLocalRun ring root pre
          (bankTrialLocalStart S)).phase = .live oldBegun ∧
        (bankTrialLocalNext ring root
          (bankTrialLocalRun ring root pre
            (bankTrialLocalStart S)) root).phase = .live newBegun) ∧
      ((bankTrialLiveWaveRootMode
          (bankTrialLocalRun ring root pre
            (bankTrialLocalStart S)).bank = .ARMED ∧
        bankTrialLiveWaveRootMode
          (bankTrialLocalNext ring root
            (bankTrialLocalRun ring root pre
              (bankTrialLocalStart S)) root).bank = .IWAIT) ∨
       (bankTrialLiveWaveRootMode
          (bankTrialLocalRun ring root pre
            (bankTrialLocalStart S)).bank = .CSTART ∧
        bankTrialLiveWaveRootMode
          (bankTrialLocalNext ring root
            (bankTrialLocalRun ring root pre
              (bankTrialLocalStart S)) root).bank = .CWAIT)) :=
    ⟨hclean, ⟨pre, rfl⟩, rfl,
      ⟨begun, nextBegun, hlive, hnextLive⟩,
      Or.inl ⟨hmode, hnextMode⟩⟩
  have hnonempty :
      bankTrialC5ActualStarts ring root S
        (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
        root ≠ [] := by
    unfold bankTrialC5ActualStarts
    rw [if_pos hguard]
    simp
  cases hs : bankTrialC5ActualStarts ring root S
      (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
      root with
  | nil =>
      exact False.elim (hnonempty hs)
  | cons o more =>
      have ho : o ∈ bankTrialC5ActualStarts ring root S
          (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
          root := by
        rw [hs]
        simp
      have hinc : o.increment = true := by
        rw [bankTrialC5ActualIncrementTagExact
          ring root S
          (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
          root o ho, hmode]
        rfl
      have htag : o.heads = (compileAdvice q).K := by
        rw [bankTrialC5ActualOriginHeadCountExact
          ring root S hsp hlarge hwidth hclean pre
          (bankTrialLocalRun ring root pre
            (bankTrialLocalStart S)) rfl root o ho]
        rw [bankTrialC5StrengthenedSnocHeads,
          if_pos (show BankTrialProbabilityArmedGate
            (bankTrialLocalRun ring root pre
              (bankTrialLocalStart S)) ∧ root = root
            from ⟨hgate, rfl⟩)]
        exact hcount
      have hselected : o ∈
          bankTrialDurationKHeadActualStarts ring root S
            (bankTrialLocalRun ring root pre
              (bankTrialLocalStart S)) root := by
        unfold bankTrialDurationKHeadActualStarts
        exact List.mem_filter.mpr ⟨ho, beq_iff_eq.mpr htag⟩
      exact ⟨o, hselected, hinc⟩

/-- Digit one, pointwise. A BAD first exit charges the kth
increment itself; NONE contradicts a LOST endpoint; a GOOD
first exit yields a reachable LIVE/CSTART cut with exactly K
heads, whose subsequent LOST suffix has a comparator timeout. -/
theorem bankTrialDurationKHeadOneCutLostTimeoutWitness
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n)) (x : BankTrialLocalState q)
    (hx : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialDurationKHeadActualStarts
      ring root S x root)
    (hinc : o.increment = true)
    (suffix : List (Fin n))
    (hlost : (bankTrialLocalRun ring root suffix o.after).phase =
      .lost) :
    ∃ launchPre tail : List (Fin n),
      ∃ p : BankTrialC5ActualOrigin n q,
        ((pre ++ [root]) ++ suffix) =
          launchPre ++ (root :: tail) ∧
        p ∈ bankTrialDurationKHeadActualStarts ring root S
          (bankTrialLocalRun ring root launchPre
            (bankTrialLocalStart S)) root ∧
        bankTrialC5ActualTimeout ring root p tail = true := by
  obtain ⟨hsource, htag⟩ :=
    bankTrialDurationKHeadSelectedTag ring root S x root o ho
  have hpost :=
    bankTrialC5ActualStartPost ring root S x root o hsource
  have hafter :
      o.after = bankTrialLocalRun ring root (pre ++ [root])
        (bankTrialLocalStart S) := by
    calc
      o.after = bankTrialLocalNext ring root x root := hpost
      _ = bankTrialLocalRun ring root (pre ++ [root])
            (bankTrialLocalStart S) := by
        rw [bankTrialLocalRunAppend, ← hx]
        rfl
  have hcountPost :
      bankTrialLiveHeadCount ring root (pre ++ [root])
        (bankTrialLocalStart S) = (compileAdvice q).K :=
    (bankTrialC5ActualOriginHeadCountExact
      ring root S hsp hlarge hwidth hclean pre x hx root o
      hsource).symm.trans htag
  cases hs : bankTrialC5WorkerFirstExit ring root o suffix
      o.after with
  | none =>
      have hnonterminal :=
        bankTrialSuccessWorkerFirstExitNoneNonterminal
          ring root o suffix hs
      exact False.elim (hnonterminal (Or.inr hlost))
  | some result =>
      cases result with
      | false =>
          have hkernel := bankTrialC5ActualWorkerExcursionKernelHolds
            ring root S hsp hlarge hwidth hclean
          have htimeout := bankTrialC5FirstBadImpliesTimeout
            ring root S hkernel x root o hsource suffix hs
          refine ⟨pre, suffix, o, ?_, ?_, htimeout⟩
          · simp only [List.append_assoc, List.singleton_append]
          · rw [← hx]
            exact ho
      | true =>
          obtain ⟨u, v, hdecomp, hret⟩ :=
            bankTrialDurationKHeadFirstGoodPrefix
              ring root o suffix o.after hs
          unfold bankTrialC5ActualReturned at hret
          simp only [hinc, ↓reduceIte] at hret
          obtain ⟨begun, hlive, hmode⟩ := hret
          have hreach :
              bankTrialLocalRun ring root u o.after =
                bankTrialLocalRun ring root
                  ((pre ++ [root]) ++ u)
                  (bankTrialLocalStart S) := by
            rw [hafter]
            simp only [bankTrialLocalRunAppend]
          have hlower :
              (compileAdvice q).K ≤
              bankTrialLiveHeadCount ring root
                ((pre ++ [root]) ++ u) (bankTrialLocalStart S) := by
            rw [bankTrialLiveHeadCountAppend]
            omega
          have hupper :=
            bankTrialC5ActualAllWordsHeadCap
              ring root S hsp hlarge hwidth hclean
              ((pre ++ [root]) ++ u)
          have hcountCut :
              bankTrialLiveHeadCount ring root
                ((pre ++ [root]) ++ u) (bankTrialLocalStart S) =
                  (compileAdvice q).K :=
            Nat.le_antisymm hupper hlower
          have hlostRest :
              (bankTrialLocalRun ring root v
                (bankTrialLocalRun ring root u o.after)).phase =
                  .lost := by
            have hr :
                bankTrialLocalRun ring root suffix o.after =
                  bankTrialLocalRun ring root v
                    (bankTrialLocalRun ring root u o.after) := by
              rw [hdecomp, bankTrialLocalRunAppend]
            rw [← hr]
            exact hlost
          obtain ⟨a, b, hab, p, hp, hcomp, htimeout⟩ :=
            bankTrialDurationKHeadCStartLostTimeoutWitness
              ring root S hsp hlarge hwidth hclean
              ((pre ++ [root]) ++ u)
              (bankTrialLocalRun ring root u o.after)
              begun hreach hlive hmode hcountCut v hlostRest
          refine ⟨((pre ++ [root]) ++ u) ++ a, b, p,
            ?_, ?_, htimeout⟩
          · rw [hdecomp, hab]
            simp only [List.append_assoc, List.singleton_append,
              List.cons_append] <;> rfl
          · have hcompState :
                bankTrialLocalRun ring root a
                  (bankTrialLocalRun ring root u o.after) =
                bankTrialLocalRun ring root
                  (((pre ++ [root]) ++ u) ++ a)
                  (bankTrialLocalStart S) := by
              rw [bankTrialLocalRunAppend, ← hreach]
            rw [← hcompState]
            exact hp

/-- Every full K-head LOST word has a chronological K-tagged
origin whose timeout holds on the literal remaining suffix.
The workerless zero-bit branch charges its later comparator. -/
theorem bankTrialDurationKHeadLostTimeoutWord
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (word : List (Fin n))
    (hevent : bankTrialProbabilityHeadEvent ring root word
      (compileAdvice q).K (bankTrialLocalStart S))
    (hlost : (bankTrialLocalRun ring root word
      (bankTrialLocalStart S)).phase = .lost) :
    ∃ pre suffix : List (Fin n),
      ∃ o : BankTrialC5ActualOrigin n q,
        word = pre ++ (root :: suffix) ∧
        o ∈ bankTrialDurationKHeadActualStarts ring root S
          (bankTrialLocalRun ring root pre
            (bankTrialLocalStart S)) root ∧
        bankTrialC5ActualTimeout ring root o suffix = true := by
  obtain ⟨pre, tail, hword, hgate, hcount⟩ :=
    bankTrialDurationKHeadEventCut ring root S hsp word hevent
  have hwordRest : word = (pre ++ [root]) ++ tail := by
    rw [hword]
    simp only [List.append_assoc, List.singleton_append]
  have hfinal :
      (bankTrialLocalRun ring root
        ((pre ++ [root]) ++ tail) (bankTrialLocalStart S)).phase =
          .lost := by
    rw [← hwordRest]
    exact hlost
  cases hbit : bankTrialLiveWaveBit
      (bankTrialLocalRun ring root pre
        (bankTrialLocalStart S)).bank
      ⟨0, bankTrialWindowWidthPos q⟩ with
  | false =>
      obtain ⟨u, v, huv, o, ho, _, htimeout⟩ :=
        bankTrialDurationKHeadZeroCutLostTimeoutWitness
          ring root S hsp hlarge hwidth hclean
          pre tail hgate hcount hbit hfinal
      refine ⟨(pre ++ [root]) ++ u, v, o, ?_, ?_, htimeout⟩
      · rw [hwordRest, huv]
        simp only [List.append_assoc, List.singleton_append,
          List.cons_append] <;> rfl
      · have hnext :
            bankTrialLocalNext ring root
              (bankTrialLocalRun ring root pre
                (bankTrialLocalStart S)) root =
            bankTrialLocalRun ring root (pre ++ [root])
              (bankTrialLocalStart S) := by
          rw [bankTrialLocalRunAppend]
          rfl
        have hstate :
            bankTrialLocalRun ring root u
              (bankTrialLocalNext ring root
                (bankTrialLocalRun ring root pre
                  (bankTrialLocalStart S)) root) =
            bankTrialLocalRun ring root
              ((pre ++ [root]) ++ u)
              (bankTrialLocalStart S) := by
          rw [hnext]
          simp only [bankTrialLocalRunAppend]
        rw [← hstate]
        exact ho
  | true =>
      obtain ⟨o, ho, hinc⟩ :=
        bankTrialDurationKHeadOneCutSelected
          ring root S hsp hlarge hwidth hclean
          pre hgate hcount hbit
      have hsource :=
        (bankTrialDurationKHeadSelectedTag ring root S
          (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
          root o ho).1
      have hpost :=
        bankTrialC5ActualStartPost ring root S
          (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
          root o hsource
      have hlostSuffix :
          (bankTrialLocalRun ring root tail o.after).phase =
            .lost := by
        have hroot :
            bankTrialLocalRun ring root (pre ++ [root])
              (bankTrialLocalStart S) =
            bankTrialLocalNext ring root
              (bankTrialLocalRun ring root pre
                (bankTrialLocalStart S)) root := by
          rw [bankTrialLocalRunAppend]
          rfl
        rw [bankTrialLocalRunAppend] at hfinal
        rw [hroot] at hfinal
        rw [hpost]
        exact hfinal
      obtain ⟨launchPre, suffix, p, hdecomp, hp, htimeout⟩ :=
        bankTrialDurationKHeadOneCutLostTimeoutWitness
          ring root S hsp hlarge hwidth hclean pre
          (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
          rfl o ho hinc tail hlostSuffix
      exact ⟨launchPre, suffix, p,
        hwordRest.trans hdecomp, hp, htimeout⟩

private theorem bankTrialDurationPositiveMapSum
    {α : Type} (xs : List α) (f : α → Nat)
    (a : α) (ha : a ∈ xs) (hf : 0 < f a) :
    0 < (xs.map f).sum := by
  induction xs with
  | nil =>
      cases ha
  | cons x rest ih =>
      simp only [List.mem_cons] at ha
      simp only [List.map_cons, List.sum_cons]
      rcases ha with h | h
      · subst x
        omega
      · have ht := ih h
        omega

/-- A timed-out emitted origin contributes at least one success
to Prob.successfulOriginsWord, even though creation is stopped
at terminal prefixes. The nonterminal launch implies every
earlier prefix was nonterminal by terminal absorption. -/
private theorem bankTrialDurationKHeadTimedOriginPositive
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    ∀ (pre : List (Fin n)) (z : BankTrialLocalState q)
      (suffix : List (Fin n)) (o : BankTrialC5ActualOrigin n q),
      ¬ bankTrialLocalTerminal
        (bankTrialLocalRun ring root pre z) →
      o ∈ bankTrialDurationKHeadActualStarts ring root S
        (bankTrialLocalRun ring root pre z) root →
      bankTrialC5ActualTimeout ring root o suffix = true →
      0 < Prob.successfulOriginsWord
        (bankTrialLocalNext ring root) bankTrialLocalTerminal
        (bankTrialDurationKHeadActualStarts ring root S)
        (bankTrialC5ActualTimeout ring root)
        z (pre ++ (root :: suffix)) := by
  intro pre
  induction pre with
  | nil =>
      intro z suffix o hnon ho htimeout
      change ¬ bankTrialLocalTerminal z at hnon
      have hsum :
          0 < ((bankTrialDurationKHeadActualStarts ring root S
            z root).map (fun p =>
              Prob.indicator (bankTrialC5ActualTimeout ring root p
                suffix))).sum := by
        apply bankTrialDurationPositiveMapSum
          (bankTrialDurationKHeadActualStarts ring root S z root)
          (fun p => Prob.indicator
            (bankTrialC5ActualTimeout ring root p suffix))
          o ho
        simp [Prob.indicator, htimeout]
      change 0 < (if bankTrialLocalTerminal z then 0 else
        ((bankTrialDurationKHeadActualStarts ring root S
          z root).map (fun p =>
            Prob.indicator (bankTrialC5ActualTimeout ring root p
              suffix))).sum +
          Prob.successfulOriginsWord
            (bankTrialLocalNext ring root) bankTrialLocalTerminal
            (bankTrialDurationKHeadActualStarts ring root S)
            (bankTrialC5ActualTimeout ring root)
            (bankTrialLocalNext ring root z root) suffix)
      rw [if_neg hnon]
      omega
  | cons e rest ih =>
      intro z suffix o hnon ho htimeout
      have hbefore : ¬ bankTrialLocalTerminal z := by
        intro ht
        have habs := bankTrialLocalRunTerminalAbsorbs
          ring root (e :: rest) z ht
        apply hnon
        rw [habs]
        exact ht
      have htail :=
        ih (bankTrialLocalNext ring root z e) suffix o
          hnon ho htimeout
      change 0 < (if bankTrialLocalTerminal z then 0 else
        ((bankTrialDurationKHeadActualStarts ring root S
          z e).map (fun p =>
            Prob.indicator (bankTrialC5ActualTimeout ring root p
              (rest ++ (root :: suffix))))).sum +
          Prob.successfulOriginsWord
            (bankTrialLocalNext ring root) bankTrialLocalTerminal
            (bankTrialDurationKHeadActualStarts ring root S)
            (bankTrialC5ActualTimeout ring root)
            (bankTrialLocalNext ring root z e)
            (rest ++ (root :: suffix)))
      rw [if_neg hbefore]
      omega

/-- Direct pointwise inclusion: a K-head LOST indicator is at
most the non-resampled stopped-origin timeout event indicator. -/
theorem bankTrialDurationKHeadLostTimeoutPointwise
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (word : List (Fin n)) :
    (if bankTrialProbabilityHeadEvent ring root word
        (compileAdvice q).K (bankTrialLocalStart S) ∧
      (bankTrialLocalRun ring root word
        (bankTrialLocalStart S)).phase = .lost
     then 1 else 0) ≤
      Prob.originEventWord
        (bankTrialLocalNext ring root) bankTrialLocalTerminal
        (bankTrialDurationKHeadActualStarts ring root S)
        (bankTrialC5ActualTimeout ring root)
        (bankTrialLocalStart S) word := by
  by_cases h : bankTrialProbabilityHeadEvent ring root word
      (compileAdvice q).K (bankTrialLocalStart S) ∧
    (bankTrialLocalRun ring root word
      (bankTrialLocalStart S)).phase = .lost
  · obtain ⟨pre, suffix, o, hword, ho, htimeout⟩ :=
      bankTrialDurationKHeadLostTimeoutWord
        ring root S hsp hlarge hwidth hclean word h.1 h.2
    have hsource :=
      (bankTrialDurationKHeadSelectedTag ring root S
        (bankTrialLocalRun ring root pre
          (bankTrialLocalStart S)) root o ho).1
    have hnonterminal :=
      bankTrialC5ActualOriginNonterminal ring root S
        (bankTrialLocalRun ring root pre
          (bankTrialLocalStart S)) root o hsource
    have hpositive :
        0 < Prob.successfulOriginsWord
          (bankTrialLocalNext ring root) bankTrialLocalTerminal
          (bankTrialDurationKHeadActualStarts ring root S)
          (bankTrialC5ActualTimeout ring root)
          (bankTrialLocalStart S) word := by
      rw [hword]
      exact bankTrialDurationKHeadTimedOriginPositive
        ring root S pre (bankTrialLocalStart S)
        suffix o hnonterminal ho htimeout
    simp only [if_pos h]
    unfold Prob.originEventWord
    rw [if_neg (Nat.ne_of_gt hpositive)]
    exact Nat.le_refl 1
  · simp only [if_neg h]
    exact Nat.zero_le _

/-- First census conjunct, obtained by monotonicity of the SAME
length-T original-scheduler sum. -/
theorem bankTrialDurationKHeadLostCoveredByTimeout
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (T : Nat) :
    bankTrialDurationKHeadLostMass ring root S T ≤
      Prob.originEventNumerator
        (bankTrialLocalNext ring root) bankTrialLocalTerminal
        (bankTrialDurationKHeadActualStarts ring root S)
        (bankTrialC5ActualTimeout ring root)
        (bankTrialLocalStart S) T := by
  unfold bankTrialDurationKHeadLostMass
    Prob.originEventNumerator
  apply bankTrialProbabilityScheduleSumMono n T
  intro word
  exact bankTrialDurationKHeadLostTimeoutPointwise
    ring root S hsp hlarge hwidth hclean word

/-! The two-kind deterministic origin census. -/

private theorem bankTrialDurationFilterLengthLe
    {α : Type} (xs : List α) (p : α → Bool) :
    (xs.filter p).length ≤ xs.length := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons a rest ih =>
      simp only [List.filter_cons]
      split
      · simp only [List.length_cons]
        exact Nat.succ_le_succ ih
      · simp only [List.length_cons]
        exact Nat.le_trans ih (Nat.le_succ _)

private theorem bankTrialDurationBoolFilterPartition
    {α : Type} (xs : List α) (f : α → Bool) :
    (xs.filter (fun a => f a = true)).length +
      (xs.filter (fun a => f a = false)).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      rw [List.filter_cons, List.filter_cons]
      cases h : f a with
      | true =>
          rw [if_pos (by simp), if_neg (by simp)]
          simp only [List.length_cons]
          omega
      | false =>
          rw [if_neg (by simp), if_pos (by simp)]
          simp only [List.length_cons]
          omega

noncomputable def bankTrialDurationKHeadKindStarts
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (kind : Bool)
    (z : BankTrialLocalState q) (e : Fin n) :
    List (BankTrialC5ActualOrigin n q) :=
  (bankTrialDurationKHeadActualStarts ring root S z e).filter
    (fun o => o.increment = kind)

private theorem bankTrialDurationKHeadKindLengthLeOne
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (kind : Bool)
    (z : BankTrialLocalState q) (e : Fin n) :
    (bankTrialDurationKHeadKindStarts ring root S kind z e).length
      ≤ 1 := by
  unfold bankTrialDurationKHeadKindStarts
    bankTrialDurationKHeadActualStarts
  exact Nat.le_trans
    (bankTrialDurationFilterLengthLe
      ((bankTrialC5ActualStarts ring root S z e).filter
        (fun o => o.heads == (compileAdvice q).K))
      (fun o => o.increment = kind))
    (Nat.le_trans
      (bankTrialDurationFilterLengthLe
        (bankTrialC5ActualStarts ring root S z e)
        (fun o => o.heads == (compileAdvice q).K))
      (bankTrialC5ActualStartsLength ring root S z e))

/-- The two cannot-repeat facts are the only protocol-specific
ingredient in the per-kind census. -/
private theorem bankTrialDurationKHeadKindCannotRepeat
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (kind : Bool)
    (pre between : List (Fin n))
    (x y : BankTrialLocalState q)
    (hx : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (hy : y = bankTrialLocalRun ring root
      ((pre ++ [root]) ++ between) (bankTrialLocalStart S))
    (o p : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialDurationKHeadActualStarts ring root S x root)
    (hok : o.increment = kind)
    (e : Fin n)
    (hp : p ∈ bankTrialDurationKHeadActualStarts ring root S y e)
    (hpk : p.increment = kind) : False := by
  cases kind with
  | true =>
      exact bankTrialDurationKHeadIncrementCannotRepeat
        ring root S hsp hlarge hwidth hclean
        pre between x y hx hy o p ho hok e hp hpk
  | false =>
      exact bankTrialDurationKHeadComparatorCannotRepeat
        ring root S hsp hlarge hwidth hclean
        pre between x y hx hy o p ho hok e hp hpk

/-- Following a K-tagged origin, no later origin of the SAME kind
appears, on any continuation of the original tape. -/
private theorem bankTrialDurationKHeadNoLaterKind
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (kind : Bool) (pre : List (Fin n))
    (x : BankTrialLocalState q)
    (hx : x = bankTrialLocalRun ring root pre
      (bankTrialLocalStart S))
    (o : BankTrialC5ActualOrigin n q)
    (ho : o ∈ bankTrialDurationKHeadActualStarts
      ring root S x root)
    (hok : o.increment = kind) :
    ∀ between rest : List (Fin n),
      Prob.originsWord
        (bankTrialLocalNext ring root) bankTrialLocalTerminal
        (bankTrialDurationKHeadKindStarts ring root S kind)
        (bankTrialLocalRun ring root between o.after) rest = 0 := by
  have hsource :=
    (bankTrialDurationKHeadSelectedTag ring root S x root o ho).1
  have hpost :=
    bankTrialC5ActualStartPost ring root S x root o hsource
  have hafter :
      o.after = bankTrialLocalRun ring root (pre ++ [root])
        (bankTrialLocalStart S) := by
    calc
      o.after = bankTrialLocalNext ring root x root := hpost
      _ = bankTrialLocalRun ring root (pre ++ [root])
            (bankTrialLocalStart S) := by
        rw [bankTrialLocalRunAppend, ← hx]
        rfl
  intro between rest
  induction rest generalizing between with
  | nil => rfl
  | cons e tail ih =>
      have hy :
          bankTrialLocalRun ring root between o.after =
            bankTrialLocalRun ring root
              ((pre ++ [root]) ++ between)
              (bankTrialLocalStart S) := by
        rw [hafter]
        simp only [bankTrialLocalRunAppend]
      have hnone :
          bankTrialDurationKHeadKindStarts ring root S kind
            (bankTrialLocalRun ring root between o.after) e = [] := by
        cases hs : bankTrialDurationKHeadKindStarts ring root S
            kind (bankTrialLocalRun ring root between o.after)
            e with
        | nil => rfl
        | cons p others =>
            have hpKind : p ∈
                bankTrialDurationKHeadKindStarts ring root S
                  kind (bankTrialLocalRun ring root between o.after)
                  e := by
              rw [hs]
              simp
            unfold bankTrialDurationKHeadKindStarts at hpKind
            obtain ⟨hp, hpk⟩ := List.mem_filter.mp hpKind
            have hpkEq : p.increment = kind :=
              of_decide_eq_true hpk
            exact False.elim
              (bankTrialDurationKHeadKindCannotRepeat
                ring root S hsp hlarge hwidth hclean
                kind pre between x
                (bankTrialLocalRun ring root between o.after)
                hx hy o p ho hok e hp hpkEq)
      by_cases ht : bankTrialLocalTerminal
          (bankTrialLocalRun ring root between o.after)
      · simp only [Prob.originsWord, if_pos ht]
      · simp only [Prob.originsWord, if_neg ht]
        rw [hnone]
        simp only [List.length_nil, Nat.zero_add]
        have hnext :
            bankTrialLocalNext ring root
              (bankTrialLocalRun ring root between o.after) e =
            bankTrialLocalRun ring root (between ++ [e]) o.after := by
          rw [bankTrialLocalRunAppend]
          rfl
        rw [hnext]
        exact ih (between ++ [e])

/-- The stopped count of either kind is at most one. -/
private theorem bankTrialDurationKHeadKindCountLeOne
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (kind : Bool) :
    ∀ pre tail : List (Fin n),
      Prob.originsWord
        (bankTrialLocalNext ring root) bankTrialLocalTerminal
        (bankTrialDurationKHeadKindStarts ring root S kind)
        (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
        tail ≤ 1 := by
  intro pre tail
  induction tail generalizing pre with
  | nil =>
      exact Nat.zero_le _
  | cons e rest ih =>
      by_cases ht : bankTrialLocalTerminal
          (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
      · change (if bankTrialLocalTerminal
            (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
          then 0 else
            (bankTrialDurationKHeadKindStarts ring root S kind
              (bankTrialLocalRun ring root pre
                (bankTrialLocalStart S)) e).length +
              Prob.originsWord
                (bankTrialLocalNext ring root) bankTrialLocalTerminal
                (bankTrialDurationKHeadKindStarts ring root S kind)
                (bankTrialLocalNext ring root
                  (bankTrialLocalRun ring root pre
                    (bankTrialLocalStart S)) e) rest) ≤ 1
        rw [if_pos ht]
        exact Nat.zero_le _
      · have hlen := bankTrialDurationKHeadKindLengthLeOne
          ring root S kind
          (bankTrialLocalRun ring root pre (bankTrialLocalStart S)) e
        cases hs : bankTrialDurationKHeadKindStarts ring root S
            kind (bankTrialLocalRun ring root pre
              (bankTrialLocalStart S)) e with
        | nil =>
            change (if bankTrialLocalTerminal
                (bankTrialLocalRun ring root pre
                  (bankTrialLocalStart S))
              then 0 else
                (bankTrialDurationKHeadKindStarts ring root S kind
                  (bankTrialLocalRun ring root pre
                    (bankTrialLocalStart S)) e).length +
                  Prob.originsWord
                    (bankTrialLocalNext ring root)
                    bankTrialLocalTerminal
                    (bankTrialDurationKHeadKindStarts ring root S kind)
                    (bankTrialLocalNext ring root
                      (bankTrialLocalRun ring root pre
                        (bankTrialLocalStart S)) e) rest) ≤ 1
            rw [if_neg ht, hs]
            simp only [List.length_nil, Nat.zero_add]
            have hnext :
                bankTrialLocalNext ring root
                  (bankTrialLocalRun ring root pre
                    (bankTrialLocalStart S)) e =
                bankTrialLocalRun ring root (pre ++ [e])
                  (bankTrialLocalStart S) := by
              rw [bankTrialLocalRunAppend]
              rfl
            rw [hnext]
            exact ih (pre ++ [e])
        | cons o others =>
            have horigin :
                o ∈ bankTrialDurationKHeadKindStarts
                  ring root S kind
                  (bankTrialLocalRun ring root pre
                    (bankTrialLocalStart S)) e := by
              rw [hs]
              simp
            unfold bankTrialDurationKHeadKindStarts at horigin
            obtain ⟨ho, hok⟩ := List.mem_filter.mp horigin
            have hokEq : o.increment = kind :=
              of_decide_eq_true hok
            have hsource :=
              (bankTrialDurationKHeadSelectedTag ring root S
                (bankTrialLocalRun ring root pre
                  (bankTrialLocalStart S)) e o ho).1
            have he : e = root :=
              bankTrialC5ActualStartAtRoot ring root S
                (bankTrialLocalRun ring root pre
                  (bankTrialLocalStart S)) e o hsource
            subst e
            have hnil : others = [] := by
              rw [hs] at hlen
              cases others with
              | nil => rfl
              | cons p ps =>
                  simp only [List.length_cons] at hlen
                  omega
            have hpost :=
              bankTrialC5ActualStartPost ring root S
                (bankTrialLocalRun ring root pre
                  (bankTrialLocalStart S)) root o hsource
            have htailzero :
                Prob.originsWord
                  (bankTrialLocalNext ring root)
                  bankTrialLocalTerminal
                  (bankTrialDurationKHeadKindStarts ring root S kind)
                  (bankTrialLocalNext ring root
                    (bankTrialLocalRun ring root pre
                      (bankTrialLocalStart S)) root) rest = 0 := by
              rw [← hpost]
              exact bankTrialDurationKHeadNoLaterKind
                ring root S hsp hlarge hwidth hclean
                kind pre
                (bankTrialLocalRun ring root pre
                  (bankTrialLocalStart S)) rfl o ho hokEq [] rest
            change (if bankTrialLocalTerminal
                (bankTrialLocalRun ring root pre
                  (bankTrialLocalStart S))
              then 0 else
                (bankTrialDurationKHeadKindStarts ring root S kind
                  (bankTrialLocalRun ring root pre
                    (bankTrialLocalStart S)) root).length +
                Prob.originsWord
                  (bankTrialLocalNext ring root)
                  bankTrialLocalTerminal
                  (bankTrialDurationKHeadKindStarts ring root S kind)
                  (bankTrialLocalNext ring root
                    (bankTrialLocalRun ring root pre
                      (bankTrialLocalStart S)) root) rest) ≤ 1
            rw [if_neg ht, hs, hnil, htailzero]
            simp only [List.length_cons, List.length_nil]
            omega

/-- Every selected origin is exactly one of the two kinds.
The identity holds even on words which become terminal early. -/
private theorem bankTrialDurationKHeadOriginsSplit
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    ∀ (word : List (Fin n)) (z : BankTrialLocalState q),
      Prob.originsWord
        (bankTrialLocalNext ring root) bankTrialLocalTerminal
        (bankTrialDurationKHeadActualStarts ring root S) z word =
      Prob.originsWord
        (bankTrialLocalNext ring root) bankTrialLocalTerminal
        (bankTrialDurationKHeadKindStarts ring root S true) z word +
      Prob.originsWord
        (bankTrialLocalNext ring root) bankTrialLocalTerminal
        (bankTrialDurationKHeadKindStarts ring root S false) z word := by
  intro word
  induction word with
  | nil =>
      intro z
      rfl
  | cons e tail ih =>
      intro z
      by_cases ht : bankTrialLocalTerminal z
      · simp [Prob.originsWord, ht]
      · have hlength :
            (bankTrialDurationKHeadActualStarts ring root S z e).length =
            (bankTrialDurationKHeadKindStarts
              ring root S true z e).length +
            (bankTrialDurationKHeadKindStarts
              ring root S false z e).length := by
          unfold bankTrialDurationKHeadKindStarts
          exact (bankTrialDurationBoolFilterPartition
            (bankTrialDurationKHeadActualStarts ring root S z e)
            (fun o => o.increment)).symm
        simp only [Prob.originsWord, if_neg ht]
        rw [ih (bankTrialLocalNext ring root z e)]
        omega

/-- A selected origin on any prefix implies the HEAD event on
the whole word, by the existing append closure. Hence a word
without the K-head event has zero K-tagged origins. -/
private theorem bankTrialDurationKHeadNoOriginsWithoutHead
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    ∀ (pre rest : List (Fin n)),
      ¬ bankTrialProbabilityHeadEvent ring root
        (pre ++ rest) (compileAdvice q).K (bankTrialLocalStart S) →
      Prob.originsWord
        (bankTrialLocalNext ring root) bankTrialLocalTerminal
        (bankTrialDurationKHeadActualStarts ring root S)
        (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
        rest = 0 := by
  intro pre rest
  induction rest generalizing pre with
  | nil =>
      intro _
      rfl
  | cons e tail ih =>
      intro hnot
      have hnone :
          bankTrialDurationKHeadActualStarts ring root S
            (bankTrialLocalRun ring root pre
              (bankTrialLocalStart S)) e = [] := by
        cases hs : bankTrialDurationKHeadActualStarts ring root S
            (bankTrialLocalRun ring root pre
              (bankTrialLocalStart S)) e with
        | nil => rfl
        | cons o others =>
            have ho : o ∈ bankTrialDurationKHeadActualStarts
                ring root S (bankTrialLocalRun ring root pre
                  (bankTrialLocalStart S)) e := by
              rw [hs]
              simp
            have hhead := bankTrialDurationKHeadLaunchHasHeadEvent
              ring root S hsp hlarge hwidth hclean
              pre (bankTrialLocalRun ring root pre
                (bankTrialLocalStart S)) rfl e o ho
            have hfull := bankTrialDurationKHeadEventAppend
              ring root (pre ++ [e]) tail (compileAdvice q).K
              (bankTrialLocalStart S) hhead
            have hword :
                (pre ++ [e]) ++ tail = pre ++ (e :: tail) := by
              simp only [List.append_assoc, List.singleton_append]
            rw [hword] at hfull
            exact False.elim (hnot hfull)
      by_cases ht : bankTrialLocalTerminal
          (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
      · simp only [Prob.originsWord, if_pos ht]
      · simp only [Prob.originsWord, if_neg ht]
        rw [hnone]
        simp only [List.length_nil, Nat.zero_add]
        have hnext :
            bankTrialLocalNext ring root
              (bankTrialLocalRun ring root pre
                (bankTrialLocalStart S)) e =
            bankTrialLocalRun ring root (pre ++ [e])
              (bankTrialLocalStart S) := by
          rw [bankTrialLocalRunAppend]
          rfl
        rw [hnext]
        have hnotTail :
            ¬ bankTrialProbabilityHeadEvent ring root
              ((pre ++ [e]) ++ tail)
              (compileAdvice q).K (bankTrialLocalStart S) := by
          intro h
          apply hnot
          have hword :
              (pre ++ [e]) ++ tail = pre ++ (e :: tail) := by
            simp only [List.append_assoc, List.singleton_append]
          rw [hword] at h
          exact h
        exact ih (pre ++ [e]) hnotTail

/-- Pointwise second census conjunct: at most one K-increment
and one K-comparator; neither can occur off the K-head event. -/
theorem bankTrialDurationKHeadCountPointwise
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (word : List (Fin n)) :
    Prob.originsWord
      (bankTrialLocalNext ring root) bankTrialLocalTerminal
      (bankTrialDurationKHeadActualStarts ring root S)
      (bankTrialLocalStart S) word ≤
    2 * (if bankTrialProbabilityHeadEvent ring root word
        (compileAdvice q).K (bankTrialLocalStart S)
      then 1 else 0) := by
  have hsplit := bankTrialDurationKHeadOriginsSplit
    ring root S word (bankTrialLocalStart S)
  have hinc := bankTrialDurationKHeadKindCountLeOne
    ring root S hsp hlarge hwidth hclean true [] word
  have hcomp := bankTrialDurationKHeadKindCountLeOne
    ring root S hsp hlarge hwidth hclean false [] word
  simp only [bankTrialLocalRun] at hinc hcomp
  have htwo :
      Prob.originsWord
        (bankTrialLocalNext ring root) bankTrialLocalTerminal
        (bankTrialDurationKHeadActualStarts ring root S)
        (bankTrialLocalStart S) word ≤ 2 := by
    omega
  by_cases hhead : bankTrialProbabilityHeadEvent ring root word
      (compileAdvice q).K (bankTrialLocalStart S)
  · simpa only [if_pos hhead, Nat.mul_one] using htwo
  · have hzero := bankTrialDurationKHeadNoOriginsWithoutHead
      ring root S hsp hlarge hwidth hclean [] word
      (by simpa only [List.nil_append] using hhead)
    simp only [bankTrialLocalRun] at hzero
    rw [hzero, if_neg hhead]
    exact Nat.zero_le _

/-- Second census conjunct at original horizon T. The factor 2
is moved inside scheduleSum by its proved scale lemma. -/
theorem bankTrialDurationKHeadAtMostTwoLaunches
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (T : Nat) :
    Prob.originsNumerator
      (bankTrialLocalNext ring root) bankTrialLocalTerminal
      (bankTrialDurationKHeadActualStarts ring root S)
      (bankTrialLocalStart S) T ≤
      2 * bankTrialProbabilityHeadMass ring root
        (bankTrialLocalStart S) (compileAdvice q).K T := by
  unfold Prob.originsNumerator bankTrialProbabilityHeadMass
  rw [← bankTrialSuccessScheduleSumScale n T 2 (fun word =>
    if bankTrialProbabilityHeadEvent ring root word
        (compileAdvice q).K (bankTrialLocalStart S)
    then 1 else 0)]
  apply bankTrialProbabilityScheduleSumMono n T
  intro word
  exact bankTrialDurationKHeadCountPointwise
    ring root S hsp hlarge hwidth hclean word

/-- Both deterministic C.8 post-launch census conjuncts. -/
theorem bankTrialDurationKHeadPostLaunchCensusHolds
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    BankTrialDurationKHeadPostLaunchCensus ring root S := by
  intro T
  exact ⟨bankTrialDurationKHeadLostCoveredByTimeout
      ring root S hsp hlarge hwidth hclean T,
    bankTrialDurationKHeadAtMostTwoLaunches
      ring root S hsp hlarge hwidth hclean T⟩

/-- The unconditional spatial-band survival estimate follows
without an independent worker tape or a new rarity hypothesis. -/
theorem bankTrialDurationAllKHeadSurvivalEstimateHolds
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    BankTrialDurationAllKHeadSurvivalEstimate
      (q := q) ring root := by
  apply bankTrialDurationAllKHeadSurvivalOfCensus ring root hwidth
  intro S hclean hsp hlarge
  exact bankTrialDurationKHeadPostLaunchCensusHolds
    ring root S hsp hlarge hwidth hclean

end L3

#print axioms L3.bankTrialDurationKHeadOneCutSelected
#print axioms L3.bankTrialDurationKHeadOneCutLostTimeoutWitness
#print axioms L3.bankTrialDurationKHeadLostTimeoutWord
#print axioms L3.bankTrialDurationKHeadLostTimeoutPointwise
#print axioms L3.bankTrialDurationKHeadLostCoveredByTimeout
#print axioms L3.bankTrialDurationKHeadCountPointwise
#print axioms L3.bankTrialDurationKHeadAtMostTwoLaunches
#print axioms L3.bankTrialDurationKHeadPostLaunchCensusHolds
#print axioms L3.bankTrialDurationAllKHeadSurvivalEstimateHolds

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
G12e-C.
The only remaining mathematical premise in the final theorem is
BankTrialDurationKHeadAllHeadsMeanInequality below. It is NOT
established by the weighted-cut mass theorem alone.
-/

private def bankTrialDurationFirstCutMass
    {X : Type} {n : Nat} (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T : Nat) (pre : List (Fin n)) (x : X) : Nat :=
  ((Prob.firstStoppedPrefixes next stop T pre x).map
    (fun cut => n ^ (T - cut.length))).sum

private def bankTrialDurationFirstCutMoment
    {X : Type} {n : Nat} (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T : Nat) (pre : List (Fin n)) (x : X) : Nat :=
  ((Prob.firstStoppedPrefixes next stop T pre x).map
    (fun cut => cut.length * n ^ (T - cut.length))).sum

noncomputable def bankTrialDurationKHeadCutMoment
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) : Nat :=
  bankTrialDurationFirstCutMoment
    (bankTrialLocalNext ring root)
    (bankTrialDurationKHeadCutStop ring root S)
    T [] (bankTrialLocalStart S)

private theorem bankTrialDurationCutFlatMapSum
    {A B C : Type} (xs : List A) (ys : A → List B)
    (g : A → B → C) (f : C → Nat) :
    (((xs.flatMap (fun a => (ys a).map (g a))).map f)).sum =
      (xs.map (fun a =>
        ((ys a).map (fun b => f (g a b))).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih, Function.comp_def]

private theorem bankTrialDurationCutMapSumAdd
    {A : Type} (xs : List A) (f g : A → Nat) :
    (xs.map (fun a => f a + g a)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      omega

private theorem bankTrialDurationFirstCutMassSucc
    {X : Type} {n : Nat} (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T : Nat) (pre : List (Fin n)) (x : X) :
    bankTrialDurationFirstCutMass next stop (T + 1) pre x =
      if stop pre x then n ^ (T + 1)
      else (List.ofFn (fun e : Fin n =>
        bankTrialDurationFirstCutMass next stop T
          (pre ++ [e]) (next x e))).sum := by
  cases hs : stop pre x with
  | true =>
      simp [bankTrialDurationFirstCutMass,
        Prob.firstStoppedPrefixes, hs]
  | false =>
      simp only [Bool.false_eq_true, if_false]
      unfold bankTrialDurationFirstCutMass
      simp only [Prob.firstStoppedPrefixes, hs, Bool.false_eq_true, if_false]
      change
        ((((List.ofFn (fun e : Fin n => e)).flatMap
          (fun e =>
            (Prob.firstStoppedPrefixes next stop T
              (pre ++ [e]) (next x e)).map (List.cons e))).map
          (fun u => n ^ ((T + 1) - u.length))).sum) =
        (List.ofFn (fun e : Fin n =>
          ((Prob.firstStoppedPrefixes next stop T
            (pre ++ [e]) (next x e)).map
            (fun u => n ^ (T - u.length))).sum)).sum
      rw [bankTrialDurationCutFlatMapSum]
      simp only [List.map_ofFn, List.map_map, Function.comp_def]
      apply ofFn_sum_eq
      intro e
      apply bankTrialSuccessCutHistoryMapSumExt
      intro u
      change n ^ ((T + 1) - (e :: u).length) =
        n ^ (T - u.length)
      simp only [List.length_cons, Nat.succ_eq_add_one]
      congr 1
      omega

private theorem bankTrialDurationFirstCutMomentSucc
    {X : Type} {n : Nat} (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T : Nat) (pre : List (Fin n)) (x : X) :
    bankTrialDurationFirstCutMoment next stop (T + 1) pre x =
      if stop pre x then 0
      else (List.ofFn (fun e : Fin n =>
        bankTrialDurationFirstCutMoment next stop T
          (pre ++ [e]) (next x e) +
        bankTrialDurationFirstCutMass next stop T
          (pre ++ [e]) (next x e))).sum := by
  cases hs : stop pre x with
  | true =>
      simp [bankTrialDurationFirstCutMoment,
        Prob.firstStoppedPrefixes, hs]
  | false =>
      simp only [Bool.false_eq_true, if_false]
      unfold bankTrialDurationFirstCutMoment bankTrialDurationFirstCutMass
      simp only [Prob.firstStoppedPrefixes, hs, Bool.false_eq_true, if_false]
      change
        ((((List.ofFn (fun e : Fin n => e)).flatMap
          (fun e =>
            (Prob.firstStoppedPrefixes next stop T
              (pre ++ [e]) (next x e)).map (List.cons e))).map
          (fun u => u.length * n ^ ((T + 1) - u.length))).sum) =
        (List.ofFn (fun e : Fin n =>
          ((Prob.firstStoppedPrefixes next stop T
            (pre ++ [e]) (next x e)).map
            (fun u => u.length * n ^ (T - u.length))).sum +
          ((Prob.firstStoppedPrefixes next stop T
            (pre ++ [e]) (next x e)).map
            (fun u => n ^ (T - u.length))).sum)).sum
      rw [bankTrialDurationCutFlatMapSum]
      simp only [List.map_ofFn, List.map_map, Function.comp_def]
      apply ofFn_sum_eq
      intro e
      calc
        ((Prob.firstStoppedPrefixes next stop T
            (pre ++ [e]) (next x e)).map
          (fun u => (e :: u).length *
            n ^ ((T + 1) - (e :: u).length))).sum =
        ((Prob.firstStoppedPrefixes next stop T
            (pre ++ [e]) (next x e)).map
          (fun u => u.length * n ^ (T - u.length) +
            n ^ (T - u.length))).sum := by
              apply bankTrialSuccessCutHistoryMapSumExt
              intro u
              simp only [List.length_cons, Nat.succ_eq_add_one]
              rw [show T + 1 - (u.length + 1) =
                T - u.length by omega]
              rw [Nat.add_mul, Nat.one_mul]
        _ = _ := bankTrialDurationCutMapSumAdd _ _ _

private theorem bankTrialDurationFirstCutMassZero
    {X : Type} {n : Nat} (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (pre : List (Fin n)) (x : X) :
    bankTrialDurationFirstCutMass next stop 0 pre x =
      if stop pre x then 1 else 0 := by
  cases hs : stop pre x <;>
    simp [bankTrialDurationFirstCutMass,
      Prob.firstStoppedPrefixes, hs]

private theorem bankTrialDurationFirstCutMomentZero
    {X : Type} {n : Nat} (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (pre : List (Fin n)) (x : X) :
    bankTrialDurationFirstCutMoment next stop 0 pre x = 0 := by
  cases hs : stop pre x <;>
    simp [bankTrialDurationFirstCutMoment,
      Prob.firstStoppedPrefixes, hs]

private theorem bankTrialDurationFirstCutMassAtStop
    {X : Type} {n : Nat} (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T : Nat) (pre : List (Fin n)) (x : X)
    (hs : stop pre x = true) :
    bankTrialDurationFirstCutMass next stop T pre x = n ^ T := by
  cases T with
  | zero =>
      simp [bankTrialDurationFirstCutMass,
        Prob.firstStoppedPrefixes, hs]
  | succ t =>
      simp [bankTrialDurationFirstCutMass,
        Prob.firstStoppedPrefixes, hs]

private theorem bankTrialDurationFirstCutMomentAtStop
    {X : Type} {n : Nat} (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T : Nat) (pre : List (Fin n)) (x : X)
    (hs : stop pre x = true) :
    bankTrialDurationFirstCutMoment next stop T pre x = 0 := by
  cases T with
  | zero =>
      simp [bankTrialDurationFirstCutMoment,
        Prob.firstStoppedPrefixes, hs]
  | succ t =>
      simp [bankTrialDurationFirstCutMoment,
        Prob.firstStoppedPrefixes, hs]

private theorem bankTrialDurationCutConservationArithmetic
    (n t m r mp rp : Nat)
    (h : rp + n * (t + 1) * m =
      n * r + (t + 1) * mp) :
    (rp + mp) + n * ((t + 1) + 1) * m =
      n * (r + m) + ((t + 1) + 1) * mp := by
  have hstep :
      n * ((t + 1) + 1) * m =
        n * (t + 1) * m + n * m := by
    calc
      n * ((t + 1) + 1) * m =
          (n * (t + 1) + n) * m := by
            rw [Nat.mul_add, Nat.mul_one]
      _ = n * (t + 1) * m + n * m := Nat.add_mul _ _ _
  have hlast :
      ((t + 1) + 1) * mp = (t + 1) * mp + mp := by
    rw [Nat.add_mul, Nat.one_mul]
  have hdist : n * (r + m) = n * r + n * m := Nat.mul_add _ _ _
  rw [hstep, hlast, hdist]
  omega

/-- Exact first-cut length conservation, for any prefix-sensitive
Boolean stopping scanner on the original Fin n tape. -/
theorem bankTrialDurationFirstCutMomentConservation
    {X : Type} {n : Nat} (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool) :
    ∀ (T : Nat) (pre : List (Fin n)) (x : X),
      bankTrialDurationFirstCutMoment next stop (T + 1) pre x +
        n * (T + 1) *
          bankTrialDurationFirstCutMass next stop T pre x =
      n * bankTrialDurationFirstCutMoment next stop T pre x +
        (T + 1) *
          bankTrialDurationFirstCutMass next stop (T + 1) pre x := by
  intro T
  induction T with
  | zero =>
      intro pre x
      cases hs : stop pre x with
      | true =>
          rw [bankTrialDurationFirstCutMomentAtStop
                next stop 1 pre x hs,
              bankTrialDurationFirstCutMassAtStop
                next stop 0 pre x hs,
              bankTrialDurationFirstCutMomentAtStop
                next stop 0 pre x hs,
              bankTrialDurationFirstCutMassAtStop
                next stop 1 pre x hs]
          simp
      | false =>
          rw [bankTrialDurationFirstCutMomentSucc
                next stop 0 pre x,
              bankTrialDurationFirstCutMassSucc
                next stop 0 pre x,
              bankTrialDurationFirstCutMomentZero
                next stop pre x,
              bankTrialDurationFirstCutMassZero
                next stop pre x]
          simp only [hs, Bool.false_eq_true, if_false,
            Nat.mul_zero, Nat.zero_mul, Nat.zero_add,
            Nat.one_mul, Nat.add_zero]
          apply ofFn_sum_eq
          intro e
          rw [bankTrialDurationFirstCutMomentZero]
          exact Nat.zero_add _
  | succ t ih =>
      intro pre x
      cases hs : stop pre x with
      | true =>
          rw [bankTrialDurationFirstCutMomentAtStop
                next stop ((t + 1) + 1) pre x hs,
              bankTrialDurationFirstCutMassAtStop
                next stop (t + 1) pre x hs,
              bankTrialDurationFirstCutMomentAtStop
                next stop (t + 1) pre x hs,
              bankTrialDurationFirstCutMassAtStop
                next stop ((t + 1) + 1) pre x hs]
          simp only [Nat.zero_add, Nat.mul_zero]
          simp only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm,
            Nat.mul_left_comm]
      | false =>
          rw [bankTrialDurationFirstCutMomentSucc
                next stop (t + 1) pre x,
              bankTrialDurationFirstCutMassSucc
                next stop t pre x,
              bankTrialDurationFirstCutMomentSucc
                next stop t pre x,
              bankTrialDurationFirstCutMassSucc
                next stop (t + 1) pre x]
          simp only [hs, Bool.false_eq_true, if_false]
          calc
            (List.ofFn (fun e : Fin n =>
                bankTrialDurationFirstCutMoment next stop
                  (t + 1) (pre ++ [e]) (next x e) +
                bankTrialDurationFirstCutMass next stop
                  (t + 1) (pre ++ [e]) (next x e))).sum +
              n * ((t + 1) + 1) *
                (List.ofFn (fun e : Fin n =>
                  bankTrialDurationFirstCutMass next stop
                    t (pre ++ [e]) (next x e))).sum =
            (List.ofFn (fun e : Fin n =>
              (bankTrialDurationFirstCutMoment next stop
                  (t + 1) (pre ++ [e]) (next x e) +
                bankTrialDurationFirstCutMass next stop
                  (t + 1) (pre ++ [e]) (next x e)) +
              n * ((t + 1) + 1) *
                bankTrialDurationFirstCutMass next stop
                  t (pre ++ [e]) (next x e))).sum := by
                    rw [← ofFn_sum_mul_left]
                    rw [← ofFn_sum_add]
            _ =
            (List.ofFn (fun e : Fin n =>
              n * (bankTrialDurationFirstCutMoment next stop
                  t (pre ++ [e]) (next x e) +
                bankTrialDurationFirstCutMass next stop
                  t (pre ++ [e]) (next x e)) +
              ((t + 1) + 1) *
                bankTrialDurationFirstCutMass next stop
                  (t + 1) (pre ++ [e]) (next x e))).sum := by
                    apply ofFn_sum_eq
                    intro e
                    exact bankTrialDurationCutConservationArithmetic
                      n t
                      (bankTrialDurationFirstCutMass next stop
                        t (pre ++ [e]) (next x e))
                      (bankTrialDurationFirstCutMoment next stop
                        t (pre ++ [e]) (next x e))
                      (bankTrialDurationFirstCutMass next stop
                        (t + 1) (pre ++ [e]) (next x e))
                      (bankTrialDurationFirstCutMoment next stop
                        (t + 1) (pre ++ [e]) (next x e))
                      (ih (pre ++ [e]) (next x e))
            _ =
              n * (List.ofFn (fun e : Fin n =>
                bankTrialDurationFirstCutMoment next stop
                  t (pre ++ [e]) (next x e) +
                bankTrialDurationFirstCutMass next stop
                  t (pre ++ [e]) (next x e))).sum +
              ((t + 1) + 1) *
                (List.ofFn (fun e : Fin n =>
                  bankTrialDurationFirstCutMass next stop
                    (t + 1) (pre ++ [e]) (next x e))).sum := by
                    rw [ofFn_sum_add, ofFn_sum_mul_left,
                      ofFn_sum_mul_left]

private theorem bankTrialDurationFirstCutLengthLe
    {X : Type} {n : Nat} (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool) :
    ∀ (T : Nat) (pre : List (Fin n)) (x : X)
      (cut : List (Fin n)),
      cut ∈ Prob.firstStoppedPrefixes next stop T pre x →
      cut.length ≤ T := by
  intro T
  induction T with
  | zero =>
      intro pre x cut hc
      cases hs : stop pre x with
      | true =>
          have heq : cut = [] := by
            simpa [Prob.firstStoppedPrefixes, hs] using hc
          rw [heq]
          exact Nat.le_refl _
      | false =>
          have hempty : cut ∈ ([] : List (List (Fin n))) := by
            simpa [Prob.firstStoppedPrefixes, hs] using hc
          cases hempty
  | succ t ih =>
      intro pre x cut hc
      cases hs : stop pre x with
      | true =>
          have heq : cut = [] := by
            simpa [Prob.firstStoppedPrefixes, hs] using hc
          rw [heq]
          exact Nat.zero_le _
      | false =>
          have hflat : cut ∈
              (List.ofFn (fun e : Fin n => e)).flatMap
                (fun e =>
                  (Prob.firstStoppedPrefixes next stop t
                    (pre ++ [e]) (next x e)).map (List.cons e)) := by
              simpa [Prob.firstStoppedPrefixes, hs] using hc
          obtain ⟨e, _, hem⟩ := List.mem_flatMap.mp hflat
          obtain ⟨tail, htail, heq⟩ := List.mem_map.mp hem
          rw [← heq]
          have hlen := ih (pre ++ [e]) (next x e) tail htail
          simp only [List.length_cons]
          omega

theorem bankTrialDurationFirstCutMomentLeHorizon
    {X : Type} {n : Nat} (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T : Nat) (pre : List (Fin n)) (x : X) :
    bankTrialDurationFirstCutMoment next stop T pre x ≤
      T * bankTrialDurationFirstCutMass next stop T pre x := by
  unfold bankTrialDurationFirstCutMoment bankTrialDurationFirstCutMass
  calc
    ((Prob.firstStoppedPrefixes next stop T pre x).map
      (fun cut => cut.length * n ^ (T - cut.length))).sum ≤
    ((Prob.firstStoppedPrefixes next stop T pre x).map
      (fun cut => T * n ^ (T - cut.length))).sum :=
        bankTrialSuccessMapSumMonotone _ _ _
          (fun cut hc =>
            Nat.mul_le_mul_right (n ^ (T - cut.length))
              (bankTrialDurationFirstCutLengthLe
                next stop T pre x cut hc))
    _ = T * ((Prob.firstStoppedPrefixes next stop T pre x).map
      (fun cut => n ^ (T - cut.length))).sum :=
        bankTrialSuccessListMapScale _ T _

private theorem bankTrialDurationCutRatioFromConservation
    (n T m r mp rp : Nat)
    (hm : n * m ≤ mp)
    (hcons : rp + n * (T + 1) * m =
      n * r + (T + 1) * mp)
    (hbound : r ≤ T * m) :
    r * mp ≤ rp * m := by
  have hmass : mp = n * m + (mp - n * m) := by omega
  have hswap : n * (T + 1) * m =
      (T + 1) * (n * m) := by
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hr : rp = n * r + (T + 1) * (mp - n * m) := by
    rw [hmass] at hcons
    rw [Nat.mul_add (T + 1) (n * m) (mp - n * m)] at hcons
    rw [hswap] at hcons
    omega
  rw [hmass, hr]
  exact bankTrialDurationKHeadRatioGrowthArithmetic
    n T m r (mp - n * m) hbound

/-- (a) Physical first-K-head conditional mean is nondecreasing,
in cross-multiplied Nat form, even at zero-mass horizons. -/
theorem bankTrialDurationKHeadRatioMonotone
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) :
    bankTrialDurationKHeadCutMoment ring root S T *
      bankTrialProbabilityHeadMass ring root
        (bankTrialLocalStart S) (compileAdvice q).K (T + 1) ≤
    bankTrialDurationKHeadCutMoment ring root S (T + 1) *
      bankTrialProbabilityHeadMass ring root
        (bankTrialLocalStart S) (compileAdvice q).K T := by
  rw [bankTrialDurationKHeadMassCutFactorization ring root S (T + 1),
      bankTrialDurationKHeadMassCutFactorization ring root S T]
  change
    bankTrialDurationFirstCutMoment
        (bankTrialLocalNext ring root)
        (bankTrialDurationKHeadCutStop ring root S)
        T [] (bankTrialLocalStart S) *
      bankTrialDurationFirstCutMass
        (bankTrialLocalNext ring root)
        (bankTrialDurationKHeadCutStop ring root S)
        (T + 1) [] (bankTrialLocalStart S) ≤
    bankTrialDurationFirstCutMoment
        (bankTrialLocalNext ring root)
        (bankTrialDurationKHeadCutStop ring root S)
        (T + 1) [] (bankTrialLocalStart S) *
      bankTrialDurationFirstCutMass
        (bankTrialLocalNext ring root)
        (bankTrialDurationKHeadCutStop ring root S)
        T [] (bankTrialLocalStart S)
  apply bankTrialDurationCutRatioFromConservation n T
  · have hm := bankTrialDurationKHeadMassStepMono
      ring root T (compileAdvice q).K (bankTrialLocalStart S)
    rw [bankTrialDurationKHeadMassCutFactorization ring root S T,
      bankTrialDurationKHeadMassCutFactorization ring root S (T + 1)]
      at hm
    exact hm
  · exact bankTrialDurationFirstCutMomentConservation
      (bankTrialLocalNext ring root)
      (bankTrialDurationKHeadCutStop ring root S)
      T [] (bankTrialLocalStart S)
  · exact bankTrialDurationFirstCutMomentLeHorizon
      (bankTrialLocalNext ring root)
      (bankTrialDurationKHeadCutStop ring root S)
      T [] (bankTrialLocalStart S)

/-- (b) Existing G11c certificate, explicitly packaged. -/
theorem bankTrialDurationKHeadNearFairCertificate
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsmall : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    ∃ Tstar : Nat, ∀ T : Nat, Tstar ≤ T →
      1023 * n ^ T ≤
        (1024 * 2 ^ (compileAdvice q).K) *
          bankTrialProbabilityHeadMass ring root
            (bankTrialLocalStart S) (compileAdvice q).K T :=
  bankTrialDurationKHeadNearFairEventually
    ring root S hsmall hlarge hwidth hclean

/-- (c), the ONE open inequality. The constant is one n per
decision race, plus (4b+7)n for each of K-1 intervening
worker/launch stages. Its derivation from boundedMean and
the chronological 2^(ARMED-count) change of measure is still
required; no independence is assumed here. -/
def BankTrialDurationKHeadAllHeadsMeanInequality
    {n q : Nat} (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    BankTrialLocalClean q S →
    (compileAdvice q).useSmall = false →
    2 * (compileAdvice q).bankLeaseCap ≤ n →
    ∀ T : Nat,
      2 ^ (compileAdvice q).K *
        bankTrialDurationKHeadCutMoment ring root S T ≤
      n ^ T * (((compileAdvice q).K +
        ((compileAdvice q).K - 1) *
          (4 * (compileAdvice q).b + 7)) * n)

private theorem bankTrialDurationCutMarginOpaque
    (a c post k n : Nat)
    (htwo : 2 * c = post + a)
    (hbase : 1024 ≤ 1023 * a)
    (hstep : 1024 * (a + 1) ≤ 1023 * c) :
    1024 * (((k + 1) + k * a) * n) ≤
      1023 * ((c * ((k + 1) + 1) * n) - post * n) := by
  have hpre : (k + 1) + k * a = 1 + k * (a + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hpost : c * ((k + 1) + 1) =
      post + (a + k * c) := by
    have heq : c * ((k + 1) + 1) = k * c + 2 * c := by
      simp only [Nat.mul_add, Nat.mul_one]
      rw [Nat.mul_comm c k]
      omega
    rw [heq, htwo]
    omega
  have hsub : c * ((k + 1) + 1) * n - post * n =
      (a + k * c) * n := by
    rw [hpost, Nat.add_mul]
    omega
  have hscalar :
      1024 * ((k + 1) + k * a) ≤
        1023 * (a + k * c) := by
    rw [hpre]
    calc
      1024 * (1 + k * (a + 1)) =
          1024 + k * (1024 * (a + 1)) := by
            rw [Nat.mul_add, Nat.mul_one]
            simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ 1023 * a + k * (1023 * c) :=
        Nat.add_le_add hbase (Nat.mul_le_mul_left k hstep)
      _ = 1023 * (a + k * c) := by
        rw [Nat.mul_add]
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hsub]
  have hscaled := Nat.mul_le_mul_right n hscalar
  simpa only [Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm] using hscaled

/-- (d), opaque-coefficient margin, valid even for b below 17. -/
theorem bankTrialDurationKHeadNearFairMargin
    (b K n : Nat) (hpositive : 0 < K) :
    1024 * ((K + (K - 1) * (4 * b + 7)) * n) ≤
      1023 * (((6 * b + 9) * (K + 1) * n) -
        ((8 * b + 11) * n)) := by
  cases K with
  | zero => cases hpositive
  | succ k =>
      have htwo :
          2 * (6 * b + 9) =
            (8 * b + 11) + (4 * b + 7) := by omega
      have hbase : 1024 ≤ 1023 * (4 * b + 7) := by omega
      have hstep :
          1024 * ((4 * b + 7) + 1) ≤
            1023 * (6 * b + 9) := by omega
      have hsub : (k + 1) - 1 = k := by omega
      have hm := bankTrialDurationCutMarginOpaque
        (4 * b + 7) (6 * b + 9) (8 * b + 11)
        k n htwo hbase hstep
      simpa only [Nat.succ_eq_add_one, hsub] using hm

private theorem bankTrialDurationCutLateArithmetic
    (W R M C A N : Nat)
    (hW : 0 < W)
    (hnear : 1023 * N ≤ 1024 * W * M)
    (hpre : W * R ≤ N * C)
    (hmargin : 1024 * C ≤ 1023 * A) :
    R ≤ M * A := by
  have hmul : (1023 * W) * R ≤
      (1023 * W) * (M * A) := by
    calc
      (1023 * W) * R = 1023 * (W * R) := by
        simp only [Nat.mul_assoc]
      _ ≤ 1023 * (N * C) :=
        Nat.mul_le_mul_left 1023 hpre
      _ = (1023 * N) * C := by
        simp only [Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm]
      _ ≤ (1024 * W * M) * C :=
        Nat.mul_le_mul_right C hnear
      _ = (W * M) * (1024 * C) := by
        simp only [Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm]
      _ ≤ (W * M) * (1023 * A) :=
        Nat.mul_le_mul_left (W * M) hmargin
      _ = (1023 * W) * (M * A) := by
        simp only [Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm]
  have hpos : 0 < 1023 * W := by omega
  exact Nat.le_of_mul_le_mul_left hmul hpos

/-- Eventual, actual-original-clock pre-cut bound from the
ONE change-of-measure inequality and the existing near-fair
mass certificate. No Nat division is used. -/
theorem bankTrialDurationKHeadLateCutBoundOfMean
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hpositive : 0 < (compileAdvice q).K)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hsmall : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hmean : BankTrialDurationKHeadAllHeadsMeanInequality
      (q := q) ring root) :
    ∃ Tstar : Nat, ∀ T : Nat, Tstar ≤ T →
      bankTrialDurationKHeadCutMoment ring root S T ≤
        bankTrialProbabilityHeadMass ring root
          (bankTrialLocalStart S) (compileAdvice q).K T *
          (((6 * (compileAdvice q).b + 9) *
            ((compileAdvice q).K + 1) * n) -
           ((8 * (compileAdvice q).b + 11) * n)) := by
  obtain ⟨Tstar, hnear⟩ :=
    bankTrialDurationKHeadNearFairCertificate
      ring root S hsmall hlarge hwidth hclean
  refine ⟨Tstar, ?_⟩
  intro T hT
  exact bankTrialDurationCutLateArithmetic
    (2 ^ (compileAdvice q).K)
    (bankTrialDurationKHeadCutMoment ring root S T)
    (bankTrialProbabilityHeadMass ring root
      (bankTrialLocalStart S) (compileAdvice q).K T)
    (((compileAdvice q).K +
      ((compileAdvice q).K - 1) *
        (4 * (compileAdvice q).b + 7)) * n)
    (((6 * (compileAdvice q).b + 9) *
      ((compileAdvice q).K + 1) * n) -
     ((8 * (compileAdvice q).b + 11) * n))
    (n ^ T)
    (Nat.pow_pos (by omega))
    (by simpa only [Nat.mul_assoc] using hnear T hT)
    (hmean S hclean hsmall hlarge T)
    (bankTrialDurationKHeadNearFairMargin
      (compileAdvice q).b (compileAdvice q).K n hpositive)

private theorem bankTrialDurationCutBackwardArithmetic
    (t m r mp rp A : Nat)
    (hm : m ≤ mp)
    (hbound : r ≤ t * m)
    (hratio : r * mp ≤ rp * m)
    (hnext : rp ≤ mp * A) :
    r ≤ m * A := by
  by_cases hz : mp = 0
  · have hmzero : m = 0 := by omega
    have hrzero : r = 0 := by
      rw [hmzero] at hbound
      omega
    rw [hrzero]
    exact Nat.zero_le _
  · have hpos : 0 < mp := by omega
    have hmul : mp * r ≤ mp * (m * A) := by
      calc
        mp * r = r * mp := Nat.mul_comm _ _
        _ ≤ rp * m := hratio
        _ ≤ (mp * A) * m := Nat.mul_le_mul_right m hnext
        _ = mp * (m * A) := by
          simp only [Nat.mul_assoc, Nat.mul_comm,
            Nat.mul_left_comm]
    exact Nat.le_of_mul_le_mul_left hmul hpos

private theorem bankTrialDurationCutAllHorizonFromLate
    (mass moment : Nat → Nat) (A Tstar : Nat)
    (hmass : ∀ t, mass t ≤ mass (t + 1))
    (hbound : ∀ t, moment t ≤ t * mass t)
    (hratio : ∀ t, moment t * mass (t + 1) ≤
      moment (t + 1) * mass t)
    (hlate : ∀ t, Tstar ≤ t → moment t ≤ mass t * A) :
    ∀ t, moment t ≤ mass t * A := by
  have hback : ∀ t, moment (t + 1) ≤
      mass (t + 1) * A →
      moment t ≤ mass t * A := by
    intro t hnxt
    exact bankTrialDurationCutBackwardArithmetic
      t (mass t) (moment t)
      (mass (t + 1)) (moment (t + 1)) A
      (hmass t) (hbound t) (hratio t) hnxt
  have hiterate : ∀ t d : Nat,
      moment (t + d) ≤ mass (t + d) * A →
      moment t ≤ mass t * A := by
    intro t d
    induction d with
    | zero =>
        intro h
        simpa only [Nat.add_zero] using h
    | succ d ih =>
        intro h
        have hlast : moment (t + d) ≤
            mass (t + d) * A := by
          apply hback (t + d)
          simpa only [Nat.add_assoc] using h
        exact ih hlast
  intro t
  by_cases ht : Tstar ≤ t
  · exact hlate t ht
  · have hle : t ≤ Tstar := by omega
    have heq : t + (Tstar - t) = Tstar := by omega
    apply hiterate t (Tstar - t)
    rw [heq]
    exact hlate Tstar (Nat.le_refl _)

/-- Final reduction. This is conditional on exactly the
named all-heads change-of-measure inequality above; it is not
an unconditional proof of G12e-C. -/
theorem bankTrialDurationKHeadCutLengthChargeHolds
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hpositive : 0 < (compileAdvice q).K)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hmean : BankTrialDurationKHeadAllHeadsMeanInequality
      (q := q) ring root) :
    BankTrialDurationKHeadCutLengthCharge (q := q)
      ring root := by
  intro S hclean hsmall hlarge T
  change bankTrialDurationKHeadCutMoment ring root S T ≤
    bankTrialProbabilityHeadMass ring root
      (bankTrialLocalStart S) (compileAdvice q).K T *
      (((6 * (compileAdvice q).b + 9) *
        ((compileAdvice q).K + 1) * n) -
       ((8 * (compileAdvice q).b + 11) * n))
  obtain ⟨Tstar, hlate⟩ :=
    bankTrialDurationKHeadLateCutBoundOfMean
      ring root S hpositive hwidth hclean hsmall hlarge hmean
  apply bankTrialDurationCutAllHorizonFromLate
    (fun t => bankTrialProbabilityHeadMass ring root
      (bankTrialLocalStart S) (compileAdvice q).K t)
    (fun t => bankTrialDurationKHeadCutMoment ring root S t)
    (((6 * (compileAdvice q).b + 9) *
      ((compileAdvice q).K + 1) * n) -
     ((8 * (compileAdvice q).b + 11) * n)) Tstar
  · intro t
    have hm := bankTrialDurationKHeadMassStepMono
      ring root t (compileAdvice q).K (bankTrialLocalStart S)
    have hunit :
        bankTrialProbabilityHeadMass ring root
            (bankTrialLocalStart S) (compileAdvice q).K t ≤
          n * bankTrialProbabilityHeadMass ring root
            (bankTrialLocalStart S) (compileAdvice q).K t := by
      calc
        _ = 1 * bankTrialProbabilityHeadMass ring root
            (bankTrialLocalStart S) (compileAdvice q).K t :=
              (Nat.one_mul _).symm
        _ ≤ _ := Nat.mul_le_mul_right _
          (by omega : 1 ≤ n)
    exact Nat.le_trans hunit hm
  · intro t
    rw [bankTrialDurationKHeadMassCutFactorization ring root S t]
    change bankTrialDurationFirstCutMoment
        (bankTrialLocalNext ring root)
        (bankTrialDurationKHeadCutStop ring root S)
        t [] (bankTrialLocalStart S) ≤
      t * bankTrialDurationFirstCutMass
        (bankTrialLocalNext ring root)
        (bankTrialDurationKHeadCutStop ring root S)
        t [] (bankTrialLocalStart S)
    exact bankTrialDurationFirstCutMomentLeHorizon
      (bankTrialLocalNext ring root)
      (bankTrialDurationKHeadCutStop ring root S)
      t [] (bankTrialLocalStart S)
  · intro t
    exact bankTrialDurationKHeadRatioMonotone ring root S t
  · exact hlate

end L3

#print axioms L3.bankTrialDurationFirstCutMomentConservation
#print axioms L3.bankTrialDurationFirstCutMomentLeHorizon
#print axioms L3.bankTrialDurationKHeadRatioMonotone
#print axioms L3.bankTrialDurationKHeadNearFairCertificate
#print axioms L3.bankTrialDurationKHeadNearFairMargin
#print axioms L3.bankTrialDurationKHeadLateCutBoundOfMean
#print axioms L3.bankTrialDurationKHeadCutLengthChargeHolds

namespace L3

open Classical
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-!
TILTED-BELLMAN.
All probabilities are finite Nat masses on the original Fin n
scheduler. Neither a restarted tape nor independence is used.
-/

/-- On a word completing the remaining k heads this is the
number of letters through the first k-th head, and it is zero
on words which never complete the event. -/
noncomputable def bankTrialDurationTiltedHeadCost {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    List (Fin n) → Nat → BankTrialLocalState q → Nat
  | [], _, _ => 0
  | _ :: _, 0, _ => 0
  | e :: w, k + 1, z =>
      if BankTrialProbabilityArmedGate z then
        if e = root then
          (if bankTrialProbabilityHeadEvent ring root w k
              (bankTrialLocalNext ring root z e) then 1 else 0) +
            bankTrialDurationTiltedHeadCost ring root w k
              (bankTrialLocalNext ring root z e)
        else if ring.rightNeighbor e = root then 0
        else
          (if bankTrialProbabilityHeadEvent ring root w (k + 1)
              (bankTrialLocalNext ring root z e) then 1 else 0) +
            bankTrialDurationTiltedHeadCost ring root w (k + 1)
              (bankTrialLocalNext ring root z e)
      else
        (if bankTrialProbabilityHeadEvent ring root w (k + 1)
            (bankTrialLocalNext ring root z e) then 1 else 0) +
          bankTrialDurationTiltedHeadCost ring root w (k + 1)
            (bankTrialLocalNext ring root z e)

/-- No remaining heads: no pre-head occupation is charged. -/
theorem bankTrialDurationTiltedCostZeroBudget
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (w : List (Fin n)) (z : BankTrialLocalState q) :
    bankTrialDurationTiltedHeadCost ring root w 0 z = 0 := by
  cases w with
  | nil => rfl
  | cons e tail => rfl

/-- Essential non-LIVE interface: a word which cannot complete
the corresponding head event carries zero tilted cost. -/
theorem bankTrialDurationTiltedCostZeroUnlessHead
    {n q : Nat} (ring : DirectedRing n) (root : Fin n) :
    ∀ (w : List (Fin n)) (k : Nat)
      (z : BankTrialLocalState q),
      ¬ bankTrialProbabilityHeadEvent ring root w k z →
      bankTrialDurationTiltedHeadCost ring root w k z = 0 := by
  intro w
  induction w with
  | nil =>
      intro k z _
      rfl
  | cons e w ih =>
      intro k z hnot
      cases k with
      | zero =>
          rfl
      | succ k =>
          by_cases hg : BankTrialProbabilityArmedGate z
          · by_cases he : e = root
            · have htail :
                  ¬ bankTrialProbabilityHeadEvent ring root w k
                    (bankTrialLocalNext ring root z e) := by
                intro h
                apply hnot
                simpa [bankTrialProbabilityHeadEvent, hg, he]
                  using h
              have hcost :=
                ih k (bankTrialLocalNext ring root z e) htail
              simp only [bankTrialDurationTiltedHeadCost,
                if_pos hg, if_pos he]
              rw [if_neg htail, hcost]
            · by_cases hi : ring.rightNeighbor e = root
              · simp [bankTrialDurationTiltedHeadCost,
                  hg, he, hi]
              · have htail :
                    ¬ bankTrialProbabilityHeadEvent ring root w
                      (k + 1)
                      (bankTrialLocalNext ring root z e) := by
                  intro h
                  apply hnot
                  simpa [bankTrialProbabilityHeadEvent,
                    hg, he, hi] using h
                have hcost :=
                  ih (k + 1)
                    (bankTrialLocalNext ring root z e) htail
                simp [bankTrialDurationTiltedHeadCost,
                  hg, he, hi, htail, hcost]
          · have htail :
                ¬ bankTrialProbabilityHeadEvent ring root w
                  (k + 1)
                  (bankTrialLocalNext ring root z e) := by
              intro h
              apply hnot
              simpa [bankTrialProbabilityHeadEvent, hg] using h
            have hcost :=
              ih (k + 1)
                (bankTrialLocalNext ring root z e) htail
            simp [bankTrialDurationTiltedHeadCost,
              hg, htail, hcost]

/-- The exact one-letter occupation contribution, using the
same old gate and the same physical successor as HeadEvent. -/
noncomputable def bankTrialDurationTiltedNextOccupation
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q) (k T : Nat) (e : Fin n) : Nat :=
  if BankTrialProbabilityArmedGate z then
    if e = root then
      bankTrialProbabilityHeadMass ring root
        (bankTrialLocalNext ring root z e) k T +
      Prob.scheduleSum n T (fun w =>
        bankTrialDurationTiltedHeadCost ring root w k
          (bankTrialLocalNext ring root z e))
    else if ring.rightNeighbor e = root then 0
    else
      bankTrialProbabilityHeadMass ring root
        (bankTrialLocalNext ring root z e) (k + 1) T +
      Prob.scheduleSum n T (fun w =>
        bankTrialDurationTiltedHeadCost ring root w (k + 1)
          (bankTrialLocalNext ring root z e))
  else
    bankTrialProbabilityHeadMass ring root
      (bankTrialLocalNext ring root z e) (k + 1) T +
    Prob.scheduleSum n T (fun w =>
      bankTrialDurationTiltedHeadCost ring root w (k + 1)
        (bankTrialLocalNext ring root z e))

/-- Exact Bellman decomposition before applying any inequality:
each surviving child contributes head-event mass plus future
tilted cost; incoming failure contributes zero. -/
theorem bankTrialDurationTiltedNextOccupationExact
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q) (k T : Nat) :
    Prob.scheduleSum n (T + 1) (fun w =>
      bankTrialDurationTiltedHeadCost ring root w (k + 1) z) =
      (List.ofFn (bankTrialDurationTiltedNextOccupation
        ring root z k T)).sum := by
  rw [bankTrialProbabilityScheduleSumFirst]
  apply ofFn_sum_eq
  intro e
  unfold bankTrialDurationTiltedNextOccupation
  by_cases hg : BankTrialProbabilityArmedGate z
  · by_cases he : e = root
    · simp only [bankTrialDurationTiltedHeadCost,
        if_pos hg, if_pos he]
      rw [bankTrialC5ScheduleSumAdd]
      rfl
    · by_cases hi : ring.rightNeighbor e = root
      · simp only [bankTrialDurationTiltedHeadCost,
          if_pos hg, if_neg he, if_pos hi]
        rw [bankTrialProbabilityScheduleSumConst]
        simp
      · simp only [bankTrialDurationTiltedHeadCost,
          if_pos hg, if_neg he, if_neg hi]
        rw [bankTrialC5ScheduleSumAdd]
        rfl
  · simp only [bankTrialDurationTiltedHeadCost, if_neg hg]
    rw [bankTrialC5ScheduleSumAdd]
    rfl

/-- All arithmetic involving the two exponent-weighted summands
is isolated from powers and arbitrary oracle states. -/
theorem bankTrialDurationTiltedChildArithmetic
    (weight mass cost horizon allowance : Nat)
    (hmass : weight * mass ≤ horizon)
    (hcost : weight * cost ≤ horizon * allowance) :
    weight * (mass + cost) ≤
      horizon * (allowance + 1) := by
  calc
    weight * (mass + cost) =
        weight * mass + weight * cost := by
          rw [Nat.mul_add]
    _ ≤ horizon + horizon * allowance :=
      Nat.add_le_add hmass hcost
    _ = horizon * (allowance + 1) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]

/-- The outgoing incident consumes one head, hence the factor 2
from doubling the previous tilted weight. -/
theorem bankTrialDurationTiltedRootArithmetic
    (weight mass cost horizon allowance : Nat)
    (h : weight * (mass + cost) ≤
      horizon * (allowance + 1)) :
    (2 * weight) * (mass + cost) ≤
      horizon * (2 * (allowance + 1)) := by
  calc
    (2 * weight) * (mass + cost) =
        2 * (weight * (mass + cost)) := by
          rw [Nat.mul_assoc]
    _ ≤ 2 * (horizon * (allowance + 1)) :=
      Nat.mul_le_mul_left 2 h
    _ = horizon * (2 * (allowance + 1)) := by
      simp only [Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm]

/-- The upper bound on the e-th Bellman row required by the
hypotheses in the requested abstract theorem. -/
noncomputable def bankTrialDurationTiltedBellmanRow
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (F : BankTrialLocalState q → Nat → Nat)
    (z : BankTrialLocalState q) (k : Nat) (e : Fin n) : Nat :=
  if BankTrialProbabilityArmedGate z then
    if e = root then
      2 * (F (bankTrialLocalNext ring root z e) k + 1)
    else if ring.rightNeighbor e = root then 0
    else F (bankTrialLocalNext ring root z e) (k + 1) + 1
  else F (bankTrialLocalNext ring root z e) (k + 1) + 1

/-- Abstract, exact TILTED-BELLMAN induction on the original
scheduler. A head consumes one power of two; incoming death has
zero contribution; all other letters preserve the head count.
No probabilistic independence or extra stopping theorem. -/
theorem bankTrialDurationTiltedBellman {n q : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (G : BankTrialLocalState q → Prop)
    (F : BankTrialLocalState q → Nat → Nat)
    (hclosed : ∀ z, G z → ∀ e : Fin n,
      G (bankTrialLocalNext ring root z e))
    (hdead : ∀ z, G z → ¬ (∃ begun : Bool,
      z.phase = .live begun) →
      ∀ (w : List (Fin n)) (k : Nat),
        ¬ bankTrialProbabilityHeadEvent ring root w (k + 1) z)
    (hgate : ∀ z, G z → BankTrialProbabilityArmedGate z →
      ∀ k : Nat,
      (List.ofFn (fun e : Fin n =>
        if e = root then
          2 * (F (bankTrialLocalNext ring root z e) k + 1)
        else if ring.rightNeighbor e = root then 0
        else F (bankTrialLocalNext ring root z e) (k + 1) + 1)).sum ≤
        n * F z (k + 1))
    (hlive : ∀ z, G z →
      (∃ begun : Bool, z.phase = .live begun) →
      ¬ BankTrialProbabilityArmedGate z → ∀ k : Nat,
      (List.ofFn (fun e : Fin n =>
        F (bankTrialLocalNext ring root z e) (k + 1) + 1)).sum ≤
        n * F z (k + 1)) :
    ∀ (T k : Nat) (z : BankTrialLocalState q), G z →
      2 ^ k * Prob.scheduleSum n T (fun w =>
        bankTrialDurationTiltedHeadCost ring root w k z) ≤
      n ^ T * F z k := by
  intro T
  induction T with
  | zero =>
      intro k z _
      rw [bankTrialProbabilityScheduleSumZero]
      simp only [bankTrialDurationTiltedHeadCost,
        Nat.mul_zero, Nat.zero_le]
  | succ T ih =>
      intro k z hz
      cases k with
      | zero =>
          have hfun :
              (fun w : List (Fin n) =>
                bankTrialDurationTiltedHeadCost ring root w 0 z) =
              (fun _ => 0) := by
            funext w
            exact bankTrialDurationTiltedCostZeroBudget
              ring root w z
          rw [hfun, bankTrialProbabilityScheduleSumConst]
          simp only [Nat.mul_zero, Nat.zero_le]
      | succ k =>
          by_cases hliveZ :
              ∃ begun : Bool, z.phase = .live begun
          · have hchild : ∀ (j : Nat) (e : Fin n),
                2 ^ j *
                  (bankTrialProbabilityHeadMass ring root
                    (bankTrialLocalNext ring root z e) j T +
                   Prob.scheduleSum n T (fun w =>
                     bankTrialDurationTiltedHeadCost ring root
                       w j (bankTrialLocalNext ring root z e))) ≤
                n ^ T * (F (bankTrialLocalNext ring root z e)
                  j + 1) := by
              intro j e
              exact bankTrialDurationTiltedChildArithmetic
                (2 ^ j)
                (bankTrialProbabilityHeadMass ring root
                  (bankTrialLocalNext ring root z e) j T)
                (Prob.scheduleSum n T (fun w =>
                  bankTrialDurationTiltedHeadCost ring root
                    w j (bankTrialLocalNext ring root z e)))
                (n ^ T)
                (F (bankTrialLocalNext ring root z e) j)
                (bankTrialProbabilityHeadMassBound
                  ring hn root T j
                  (bankTrialLocalNext ring root z e))
                (ih j (bankTrialLocalNext ring root z e)
                  (hclosed z hz e))
            have hrow : ∀ e : Fin n,
                2 ^ (k + 1) *
                  bankTrialDurationTiltedNextOccupation
                    ring root z k T e ≤
                n ^ T *
                  bankTrialDurationTiltedBellmanRow
                    ring root F z k e := by
              intro e
              unfold bankTrialDurationTiltedNextOccupation
                bankTrialDurationTiltedBellmanRow
              by_cases hg : BankTrialProbabilityArmedGate z
              · by_cases he : e = root
                · simp only [if_pos hg, if_pos he]
                  calc
                    2 ^ (k + 1) *
                        (bankTrialProbabilityHeadMass ring root
                            (bankTrialLocalNext ring root z e)
                            k T +
                         Prob.scheduleSum n T (fun w =>
                           bankTrialDurationTiltedHeadCost
                             ring root w k
                             (bankTrialLocalNext ring root z e))) =
                      (2 * 2 ^ k) *
                        (bankTrialProbabilityHeadMass ring root
                            (bankTrialLocalNext ring root z e)
                            k T +
                         Prob.scheduleSum n T (fun w =>
                           bankTrialDurationTiltedHeadCost
                             ring root w k
                             (bankTrialLocalNext ring root z e))) := by
                          rw [Nat.pow_succ,
                            Nat.mul_comm (2 ^ k) 2]
                    _ ≤ n ^ T *
                        (2 * (F (bankTrialLocalNext ring root z e)
                          k + 1)) :=
                      bankTrialDurationTiltedRootArithmetic
                        (2 ^ k)
                        (bankTrialProbabilityHeadMass ring root
                          (bankTrialLocalNext ring root z e) k T)
                        (Prob.scheduleSum n T (fun w =>
                          bankTrialDurationTiltedHeadCost ring root
                            w k (bankTrialLocalNext ring root z e)))
                        (n ^ T)
                        (F (bankTrialLocalNext ring root z e) k)
                        (hchild k e)
                · by_cases hi : ring.rightNeighbor e = root
                  · simp only [if_pos hg, if_neg he,
                      if_pos hi, Nat.mul_zero, Nat.le_refl]
                  · simpa only [if_pos hg, if_neg he,
                      if_neg hi] using hchild (k + 1) e
              · simpa only [if_neg hg] using hchild (k + 1) e
            have hrowSum :
                (List.ofFn (bankTrialDurationTiltedBellmanRow
                  ring root F z k)).sum ≤
                  n * F z (k + 1) := by
              unfold bankTrialDurationTiltedBellmanRow
              by_cases hg : BankTrialProbabilityArmedGate z
              · simpa only [if_pos hg] using hgate z hz hg k
              · simpa only [if_neg hg] using
                  hlive z hz hliveZ hg k
            calc
              2 ^ (k + 1) *
                  Prob.scheduleSum n (T + 1) (fun w =>
                    bankTrialDurationTiltedHeadCost ring root
                      w (k + 1) z) =
                2 ^ (k + 1) *
                  (List.ofFn (bankTrialDurationTiltedNextOccupation
                    ring root z k T)).sum := by
                      rw [bankTrialDurationTiltedNextOccupationExact]
              _ = (List.ofFn (fun e : Fin n =>
                    2 ^ (k + 1) *
                      bankTrialDurationTiltedNextOccupation
                        ring root z k T e)).sum :=
                  (ofFn_sum_mul_left (2 ^ (k + 1)) _).symm
              _ ≤ (List.ofFn (fun e : Fin n =>
                    n ^ T * bankTrialDurationTiltedBellmanRow
                      ring root F z k e)).sum :=
                  ofFn_sum_le _ _ hrow
              _ = n ^ T *
                    (List.ofFn (bankTrialDurationTiltedBellmanRow
                      ring root F z k)).sum :=
                  ofFn_sum_mul_left (n ^ T) _
              _ ≤ n ^ T * (n * F z (k + 1)) :=
                  Nat.mul_le_mul_left (n ^ T) hrowSum
              _ = n ^ (T + 1) * F z (k + 1) := by
                  rw [Nat.pow_succ]
                  rw [Nat.mul_assoc]
          · have hnone (w : List (Fin n)) :
                bankTrialDurationTiltedHeadCost
                  ring root w (k + 1) z = 0 :=
              bankTrialDurationTiltedCostZeroUnlessHead
                ring root w (k + 1) z
                (hdead z hz hliveZ w k)
            have hfun :
                (fun w : List (Fin n) =>
                  bankTrialDurationTiltedHeadCost
                    ring root w (k + 1) z) =
                (fun _ => 0) := by
              funext w
              exact hnone w
            rw [hfun, bankTrialProbabilityScheduleSumConst]
            simp only [Nat.mul_zero, Nat.zero_le]

/-- The proposed concrete tilted potential, separate from the
abstract Bellman theorem. Its physical hgate/hlive drift rows
are NOT asserted merely from this definition. -/
noncomputable def bankTrialDurationTiltedPotential (n : Nat)
    {q : Nat} (z : BankTrialLocalState q) (k : Nat) : Nat :=
  if k = 0 then 0 else
  match z.phase with
  | .live _ =>
      n * bankTrialDurationWorkerRemaining z +
        (k + (k - 1) * bankTrialDurationWorkerLimit q) * n
  | .recovery => 0
  | .won => 0
  | .lost => 0

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false


private theorem bankTrialDurationTiltedNonliveNext {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialLocalState q)
    (hdead : ¬ (∃ begun : Bool, z.phase = .live begun)) :
    ¬ (∃ begun : Bool,
      (bankTrialLocalNext ring root z e).phase = .live begun) := by
  classical
  cases z with
  | mk B phase =>
      cases phase with
      | live begun =>
          exact False.elim (hdead ⟨begun, rfl⟩)
      | recovery =>
          unfold bankTrialLocalNext
          dsimp only
          split <;> (try split) <;>
            (intro h; rcases h with ⟨begun, heq⟩; cases heq)
      | won =>
          have ht : bankTrialLocalTerminal
              (⟨B, .won⟩ : BankTrialLocalState q) :=
            Or.inl rfl
          rw [bankTrialLocalTerminalAbsorbs ring root e _ ht]
          intro h
          rcases h with ⟨begun, heq⟩
          cases heq
      | lost =>
          have ht : bankTrialLocalTerminal
              (⟨B, .lost⟩ : BankTrialLocalState q) :=
            Or.inr rfl
          rw [bankTrialLocalTerminalAbsorbs ring root e _ ht]
          intro h
          rcases h with ⟨begun, heq⟩
          cases heq

private theorem bankTrialDurationTiltedNonliveHeadAux {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (w : List (Fin n)) (z : BankTrialLocalState q),
      ¬ (∃ begun : Bool, z.phase = .live begun) →
      ∀ k : Nat,
        ¬ bankTrialProbabilityHeadEvent ring root w (k + 1) z := by
  intro w
  induction w with
  | nil =>
      intro z hdead k h
      change k + 1 = 0 at h
      omega
  | cons e tail ih =>
      intro z hdead k h
      have hnogate : ¬ BankTrialProbabilityArmedGate z := by
        intro hg
        exact hdead hg.1
      have hnext :=
        bankTrialDurationTiltedNonliveNext ring root e z hdead
      have htail : bankTrialProbabilityHeadEvent ring root tail
          (k + 1) (bankTrialLocalNext ring root z e) := by
        simpa only [bankTrialProbabilityHeadEvent,
          if_neg hnogate] using h
      exact ih (bankTrialLocalNext ring root z e) hnext k htail

theorem bankTrialDurationTiltedPotentialDead {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q)
    (hdead : ¬ (∃ begun : Bool, z.phase = .live begun)) :
    ∀ (w : List (Fin n)) (k : Nat),
      ¬ bankTrialProbabilityHeadEvent ring root w (k + 1) z := by
  intro w k
  exact bankTrialDurationTiltedNonliveHeadAux ring root w z hdead k

private theorem bankTrialDurationTiltedLiveNotTerminal {q : Nat}
    (z : BankTrialLocalState q)
    (hlive : ∃ begun : Bool, z.phase = .live begun) :
    ¬ bankTrialLocalTerminal z := by
  obtain ⟨begun, hphase⟩ := hlive
  intro ht
  rcases ht with h | h
  · rw [hphase] at h
    cases h
  · rw [hphase] at h
    cases h

private theorem bankTrialDurationTiltedGateClassZero {q : Nat}
    (z : BankTrialLocalState q)
    (hg : BankTrialProbabilityArmedGate z) :
    bankTrialDurationClass z = 0 := by
  rcases hg with ⟨⟨begun, hphase⟩, hm⟩
  cases z with
  | mk B phase =>
      cases phase with
      | live old =>
          change (if (B.fields ⟨0, by omega⟩).1 = .ARMED
            then 0 else 1) = 0
          exact if_pos hm
      | recovery => cases hphase
      | won => cases hphase
      | lost => cases hphase

private theorem bankTrialDurationTiltedLiveClassOne {q : Nat}
    (z : BankTrialLocalState q)
    (hlive : ∃ begun : Bool, z.phase = .live begun)
    (hnotgate : ¬ BankTrialProbabilityArmedGate z) :
    bankTrialDurationClass z = 1 := by
  obtain ⟨begun, hphase⟩ := hlive
  have hm : (z.bank.fields ⟨0, by omega⟩).1 ≠ .ARMED := by
    intro armed
    exact hnotgate ⟨⟨begun, hphase⟩, armed⟩
  cases z with
  | mk B phase =>
      cases phase with
      | live old =>
          change (if (B.fields ⟨0, by omega⟩).1 = .ARMED
            then 0 else 1) = 1
          exact if_neg hm
      | recovery => cases hphase
      | won => cases hphase
      | lost => cases hphase

private theorem bankTrialDurationTiltedPotentialUpper
    (n : Nat) {q : Nat} (z : BankTrialLocalState q)
    (k : Nat) (hk : 1 ≤ k) :
    bankTrialDurationTiltedPotential n z k ≤
      n * bankTrialDurationWorkerRemaining z +
        (k + (k - 1) * bankTrialDurationWorkerLimit q) * n := by
  unfold bankTrialDurationTiltedPotential
  rw [if_neg (show k ≠ 0 by omega)]
  split
  · exact Nat.le_refl _
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _

private theorem bankTrialDurationTiltedPotentialLiveValue
    (n : Nat) {q : Nat} (z : BankTrialLocalState q)
    (k : Nat) (hlive : ∃ begun : Bool, z.phase = .live begun)
    (hk : 1 ≤ k) :
    bankTrialDurationTiltedPotential n z k =
      n * bankTrialDurationWorkerRemaining z +
        (k + (k - 1) * bankTrialDurationWorkerLimit q) * n := by
  obtain ⟨begun, hphase⟩ := hlive
  unfold bankTrialDurationTiltedPotential
  rw [if_neg (show k ≠ 0 by omega)]
  rw [hphase]

private theorem bankTrialDurationTiltedPotentialGateValue
    (n : Nat) {q : Nat} (z : BankTrialLocalState q)
    (k : Nat) (hg : BankTrialProbabilityArmedGate z)
    (hk : 1 ≤ k) :
    bankTrialDurationTiltedPotential n z k =
      (k + (k - 1) * bankTrialDurationWorkerLimit q) * n := by
  obtain ⟨begun, hphase⟩ := hg.1
  have hremaining := bankTrialDurationWorkerRemainingClassZero z
    (bankTrialDurationTiltedGateClassZero z hg)
  unfold bankTrialDurationTiltedPotential
  rw [if_neg (show k ≠ 0 by omega)]
  rw [hphase]
  rw [hremaining, Nat.mul_zero, Nat.zero_add]

/-- Sum of one exceptional spike over the native Fin n alphabet. -/
private theorem bankTrialDurationTiltedSpikeSum (n : Nat) :
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

/-- Two distinguished letters; the incoming letter is distinct. -/
private theorem bankTrialDurationTiltedTwoPortSum {n : Nat}
    (hn : 2 ≤ n) (a b : Fin n) (hab : a ≠ b)
    (R C : Nat) :
    (List.ofFn (fun e : Fin n =>
      if e = a then R else if e = b then 0 else C)).sum =
        R + (n - 2) * C := by
  classical
  have hremoved :
      (List.ofFn (fun e : Fin n =>
        if e = a then 0 else if e = b then 0 else C)).sum =
          (n - 2) * C := by
    have hpoint : ∀ e : Fin n,
        (if e = a then 0 else if e = b then 0 else C) +
          ((if e = a then C else 0) +
           (if e = b then C else 0)) = C := by
      intro e
      by_cases ha : e = a
      · have hb : e ≠ b := by
          intro he
          exact hab (ha.symm.trans he)
        simp [ha, hb, hab]
      · by_cases hb : e = b
        · simp [ha, hb, Ne.symm hab]
        · simp [ha, hb]
    have hsum :
        (List.ofFn (fun e : Fin n =>
          if e = a then 0 else if e = b then 0 else C)).sum +
        ((List.ofFn (fun e : Fin n =>
          if e = a then C else 0)).sum +
         (List.ofFn (fun e : Fin n =>
          if e = b then C else 0)).sum) = n * C := by
      calc
        _ = (List.ofFn (fun e : Fin n =>
          (if e = a then 0 else if e = b then 0 else C) +
          ((if e = a then C else 0) +
           (if e = b then C else 0)))).sum := by
            rw [ofFn_sum_add, ofFn_sum_add]
        _ = (List.ofFn (fun _ : Fin n => C)).sum := by
          apply ofFn_sum_eq
          exact hpoint
        _ = n * C := ofFn_sum_const n C
    rw [bankTrialDurationTiltedSpikeSum n a C,
      bankTrialDurationTiltedSpikeSum n b C] at hsum
    have hcount : n = (n - 2) + 2 := by omega
    have hmul : n * C = (n - 2) * C + 2 * C := by
      have h := congrArg (fun t : Nat => t * C) hcount
      rw [Nat.add_mul] at h
      exact h
    omega
  calc
    (List.ofFn (fun e : Fin n =>
      if e = a then R else if e = b then 0 else C)).sum =
      (List.ofFn (fun e : Fin n =>
        (if e = a then R else 0) +
        (if e = a then 0 else if e = b then 0 else C))).sum := by
          apply ofFn_sum_eq
          intro e
          by_cases ha : e = a <;> simp [ha]
    _ = (List.ofFn (fun e : Fin n =>
          if e = a then R else 0)).sum +
        (List.ofFn (fun e : Fin n =>
          if e = a then 0 else if e = b then 0 else C)).sum := by
          rw [ofFn_sum_add]
    _ = R + (n - 2) * C := by
          rw [bankTrialDurationTiltedSpikeSum n a R, hremoved]

private theorem bankTrialDurationTiltedTwoPortBound {n : Nat}
    (hn : 2 ≤ n) (a b : Fin n) (hab : a ≠ b)
    (f : Fin n → Nat) (R C B : Nat)
    (ha : f a ≤ R) (hb : f b = 0)
    (ho : ∀ e : Fin n, e ≠ a → e ≠ b → f e ≤ C)
    (hscalar : R + (n - 2) * C ≤ n * B) :
    (List.ofFn f).sum ≤ n * B := by
  classical
  have hpoint : ∀ e : Fin n,
      f e ≤ if e = a then R else if e = b then 0 else C := by
    intro e
    by_cases he : e = a
    · rw [if_pos he, he]
      exact ha
    · by_cases hf : e = b
      · have h0 : f e = 0 := by rw [hf]; exact hb
        rw [if_neg he, if_pos hf, h0]
        exact Nat.le_refl 0
      · rw [if_neg he, if_neg hf]
        exact ho e he hf
  have hsum := ofFn_sum_le f
    (fun e : Fin n => if e = a then R else if e = b then 0 else C)
    hpoint
  rw [bankTrialDurationTiltedTwoPortSum hn a b hab R C] at hsum
  exact Nat.le_trans hsum hscalar

/-- A nominated strict edge pays one unit in the entire list sum. -/
private theorem bankTrialDurationTiltedNominatedPay {n : Nat}
    (rank : Fin n → Nat) (current : Nat)
    (hmono : ∀ e, rank e ≤ current)
    (hdrop : ∃ e, rank e + 1 ≤ current) :
    1 + (List.ofFn rank).sum ≤ n * current := by
  classical
  obtain ⟨chosen, hchosen⟩ := hdrop
  have hpoint : ∀ e : Fin n,
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
    (fun _ : Fin n => current) hpoint
  rw [ofFn_sum_add, bankTrialDurationTiltedSpikeSum n chosen 1,
    ofFn_sum_const] at hsum
  omega

/-- The only multiplicative step in the live list-sum bound. -/
private theorem bankTrialDurationTiltedLiveSumArithmetic {n : Nat}
    (current A : Nat) (rank : Fin n → Nat)
    (hpay : 1 + (List.ofFn rank).sum ≤ n * current) :
    (List.ofFn (fun e : Fin n => n * rank e + A + 1)).sum ≤
      n * (n * current + A) := by
  calc
    (List.ofFn (fun e : Fin n => n * rank e + A + 1)).sum =
      (List.ofFn (fun e : Fin n => n * rank e + (A + 1))).sum := by
        apply ofFn_sum_eq
        intro e
        omega
    _ = n * (List.ofFn rank).sum + n * (A + 1) := by
          rw [ofFn_sum_add, ofFn_sum_mul_left, ofFn_sum_const]
    _ = n * ((List.ofFn rank).sum + 1 + A) := by
          simp only [Nat.mul_add, Nat.mul_one]
          omega
    _ ≤ n * (n * current + A) :=
          Nat.mul_le_mul_left n (by omega)

/-- The gate budget for k=0: the root has only its one letter cost. -/
private theorem bankTrialDurationTiltedGateZeroArithmetic
    (n : Nat) (hn : 2 ≤ n) :
    2 + (n - 2) * (n + 1) ≤ n * n := by
  have hcount : n = (n - 2) + 2 := by omega
  have hmul : n * n = (n - 2) * n + 2 * n := by
    have h := congrArg (fun t : Nat => t * n) hcount
    rw [Nat.add_mul] at h
    exact h
  have hother : (n - 2) * (n + 1) =
      (n - 2) * n + (n - 2) := by
    rw [Nat.mul_add, Nat.mul_one]
  rw [hother, hmul]
  omega

/-- The exact one-head increase of the affine K-head charge. -/
private theorem bankTrialDurationTiltedAdvanceArithmetic
    (n L k : Nat) (hk : 1 ≤ k) :
    ((k + 1) + ((k + 1) - 1) * L) * n =
      (k + (k - 1) * L) * n + n + n * L := by
  have hpred : k = (k - 1) + 1 := by omega
  have hmul : k * L = (k - 1) * L + L := by
    have h := congrArg (fun t : Nat => t * L) hpred
    rw [Nat.add_mul, Nat.one_mul] at h
    exact h
  calc
    ((k + 1) + ((k + 1) - 1) * L) * n =
      ((k + (k - 1) * L) + (1 + L)) * n := by
        have hs : (k + 1) - 1 = k := by omega
        rw [hs, hmul]
        congr 1
        omega
    _ = (k + (k - 1) * L) * n + (1 + L) * n := by
          rw [Nat.add_mul]
    _ = (k + (k - 1) * L) * n + n + n * L := by
          have h1 : (1 + L) * n = n + n * L := by
            rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm L n]
          rw [h1]
          omega

/-- Scalar gate drift with the two-port loss explicitly retained. -/
private theorem bankTrialDurationTiltedGateAdvanceBoundArithmetic
    (n L A B : Nat) (hn : 2 ≤ n)
    (hstep : B = A + n + n * L) :
    2 * (n * L + A + 1) + (n - 2) * (B + 1) ≤ n * B := by
  have hcount : n = (n - 2) + 2 := by omega
  have htotal : n * B = (n - 2) * B + 2 * B := by
    have h := congrArg (fun t : Nat => t * B) hcount
    rw [Nat.add_mul] at h
    exact h
  have hother : (n - 2) * (B + 1) =
      (n - 2) * B + (n - 2) := by
    rw [Nat.mul_add, Nat.mul_one]
  have hroot : 2 * (n * L + A + 1) =
      2 * (n * L) + 2 * A + 2 := by
    simp only [Nat.mul_add, Nat.mul_one]
  have htwice : 2 * B = 2 * A + 2 * n + 2 * (n * L) := by
    rw [hstep]
    simp only [Nat.mul_add]
  rw [hroot, hother, htotal, htwice]
  omega

/-- The reverse ring-neighbor identity needed to identify the tail. -/
private theorem bankTrialDurationTiltedLeftAfterRight {n : Nat}
    (ring : DirectedRing n) (e : Fin n) :
    ring.leftNeighbor (ring.rightNeighbor e) = e := by
  apply Fin.ext
  change (((e.val + 1) % n + n - 1) % n) = e.val
  have heq :
      (e.val + 1) % n + n - 1 =
        (e.val + 1) % n + (n - 1) := by
    have hn := ring.hn
    omega
  rw [heq, Nat.mod_add_mod]
  have heq' : e.val + 1 + (n - 1) = e.val + n := by
    have hn := ring.hn
    omega
  rw [heq', Nat.add_mod]
  simp [Nat.mod_eq_of_lt e.isLt]

theorem bankTrialDurationTiltedPotentialGateDrift {n q : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hrows : BankTrialDurationWorkerRankEdgeRows (q := q) ring root)
    (hclean : BankTrialLocalClean q S)
    (z : BankTrialLocalState q)
    (hreach : BankTrialDurationReachable ring root S z)
    (hgate : BankTrialProbabilityArmedGate z) (k : Nat) :
    (List.ofFn (fun e : Fin n =>
      if e = root then
        2 * (bankTrialDurationTiltedPotential n
          (bankTrialLocalNext ring root z e) k + 1)
      else if ring.rightNeighbor e = root then 0
      else bankTrialDurationTiltedPotential n
        (bankTrialLocalNext ring root z e) (k + 1) + 1)).sum ≤
    n * bankTrialDurationTiltedPotential n z (k + 1) := by
  classical
  have hnot := bankTrialDurationTiltedLiveNotTerminal z hgate.1
  have hclass := bankTrialDurationTiltedGateClassZero z hgate
  have hrowszero :=
    (hrows S hclean z hreach hnot).1 hclass
  have hchild : ∀ e : Fin n, e ≠ root →
      bankTrialDurationTiltedPotential n
        (bankTrialLocalNext ring root z e) (k + 1) ≤
      ((k + 1) + ((k + 1) - 1) *
        bankTrialDurationWorkerLimit q) * n := by
    intro e he
    have hu := bankTrialDurationTiltedPotentialUpper n
      (bankTrialLocalNext ring root z e) (k + 1)
      (by omega)
    rw [hrowszero e he, Nat.mul_zero, Nat.zero_add] at hu
    exact hu
  have hports := bankTrialDurationIncomingPort ring hn root
  have hdistinct : root ≠ ring.leftNeighbor root := hports.2.symm
  have hvalue := bankTrialDurationTiltedPotentialGateValue n
    z (k + 1) hgate (by omega)
  have hcore : ∀ R : Nat,
      2 * (bankTrialDurationTiltedPotential n
        (bankTrialLocalNext ring root z root) k + 1) ≤ R →
      R + (n - 2) *
        (((k + 1) + ((k + 1) - 1) *
          bankTrialDurationWorkerLimit q) * n + 1) ≤
      n * (((k + 1) + ((k + 1) - 1) *
        bankTrialDurationWorkerLimit q) * n) →
      (List.ofFn (fun e : Fin n =>
        if e = root then
          2 * (bankTrialDurationTiltedPotential n
            (bankTrialLocalNext ring root z e) k + 1)
        else if ring.rightNeighbor e = root then 0
        else bankTrialDurationTiltedPotential n
          (bankTrialLocalNext ring root z e) (k + 1) + 1)).sum ≤
      n * bankTrialDurationTiltedPotential n z (k + 1) := by
    intro R hroot hscalar
    have hbound := bankTrialDurationTiltedTwoPortBound
      hn root (ring.leftNeighbor root) hdistinct
      (fun e : Fin n =>
        if e = root then
          2 * (bankTrialDurationTiltedPotential n
            (bankTrialLocalNext ring root z e) k + 1)
        else if ring.rightNeighbor e = root then 0
        else bankTrialDurationTiltedPotential n
          (bankTrialLocalNext ring root z e) (k + 1) + 1)
      R
      (((k + 1) + ((k + 1) - 1) *
        bankTrialDurationWorkerLimit q) * n + 1)
      (((k + 1) + ((k + 1) - 1) *
        bankTrialDurationWorkerLimit q) * n)
      (by rw [if_pos rfl]; exact hroot)
      (by
        have ht : ring.leftNeighbor root ≠ root :=
          Ne.symm hdistinct
        simp only [if_neg ht, if_pos hports.1])
      (by
        intro e he htail
        have hno : ring.rightNeighbor e ≠ root := by
          intro hi
          apply htail
          have hh := congrArg ring.leftNeighbor hi
          rw [bankTrialDurationTiltedLeftAfterRight ring e] at hh
          exact hh
        simp only [if_neg he, if_neg hno]
        exact Nat.add_le_add_right (hchild e he) 1)
      hscalar
    rw [hvalue]
    exact hbound
  by_cases hkzero : k = 0
  · subst k
    apply hcore 2
    · change 2 * (0 + 1) ≤ 2
      omega
    · simpa using bankTrialDurationTiltedGateZeroArithmetic n hn
  · have hk : 1 ≤ k := by omega
    have hrootCap :=
      bankTrialDurationWorkerRemainingCap
        (bankTrialLocalNext ring root z root)
    have hrootUpper :
        bankTrialDurationTiltedPotential n
          (bankTrialLocalNext ring root z root) k ≤
        n * bankTrialDurationWorkerLimit q +
          (k + (k - 1) * bankTrialDurationWorkerLimit q) * n := by
      exact Nat.le_trans
        (bankTrialDurationTiltedPotentialUpper n
          (bankTrialLocalNext ring root z root) k hk)
        (Nat.add_le_add_right
          (Nat.mul_le_mul_left n hrootCap) _)
    apply hcore (2 * (n * bankTrialDurationWorkerLimit q +
      (k + (k - 1) * bankTrialDurationWorkerLimit q) * n + 1))
    · exact Nat.mul_le_mul_left 2
        (Nat.add_le_add_right hrootUpper 1)
    · exact bankTrialDurationTiltedGateAdvanceBoundArithmetic
        n (bankTrialDurationWorkerLimit q)
        ((k + (k - 1) * bankTrialDurationWorkerLimit q) * n)
        (((k + 1) + ((k + 1) - 1) *
          bankTrialDurationWorkerLimit q) * n)
        hn
        (bankTrialDurationTiltedAdvanceArithmetic n
          (bankTrialDurationWorkerLimit q) k hk)

theorem bankTrialDurationTiltedPotentialLiveDrift {n q : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hrows : BankTrialDurationWorkerRankEdgeRows (q := q) ring root)
    (hclean : BankTrialLocalClean q S)
    (z : BankTrialLocalState q)
    (hreach : BankTrialDurationReachable ring root S z)
    (hlive : ∃ begun : Bool, z.phase = .live begun)
    (hnotgate : ¬ BankTrialProbabilityArmedGate z) (k : Nat) :
    (List.ofFn (fun e : Fin n =>
      bankTrialDurationTiltedPotential n
        (bankTrialLocalNext ring root z e) (k + 1) + 1)).sum ≤
    n * bankTrialDurationTiltedPotential n z (k + 1) := by
  classical
  have hnot := bankTrialDurationTiltedLiveNotTerminal z hlive
  have hclass :=
    bankTrialDurationTiltedLiveClassOne z hlive hnotgate
  obtain ⟨hmono, hdrop⟩ :=
    (hrows S hclean z hreach hnot).2 hclass
  have hpay := bankTrialDurationTiltedNominatedPay
    (fun e : Fin n =>
      bankTrialDurationWorkerRemaining
        (bankTrialLocalNext ring root z e))
    (bankTrialDurationWorkerRemaining z) hmono hdrop
  have hpoint : ∀ e : Fin n,
      bankTrialDurationTiltedPotential n
        (bankTrialLocalNext ring root z e) (k + 1) + 1 ≤
      n * bankTrialDurationWorkerRemaining
        (bankTrialLocalNext ring root z e) +
        (((k + 1) + ((k + 1) - 1) *
          bankTrialDurationWorkerLimit q) * n) + 1 := by
    intro e
    exact Nat.add_le_add_right
      (bankTrialDurationTiltedPotentialUpper n
        (bankTrialLocalNext ring root z e) (k + 1)
        (by omega)) 1
  have hsum := ofFn_sum_le
    (fun e : Fin n =>
      bankTrialDurationTiltedPotential n
        (bankTrialLocalNext ring root z e) (k + 1) + 1)
    (fun e : Fin n =>
      n * bankTrialDurationWorkerRemaining
        (bankTrialLocalNext ring root z e) +
        (((k + 1) + ((k + 1) - 1) *
          bankTrialDurationWorkerLimit q) * n) + 1)
    hpoint
  have hscalar := bankTrialDurationTiltedLiveSumArithmetic
    (bankTrialDurationWorkerRemaining z)
    (((k + 1) + ((k + 1) - 1) *
      bankTrialDurationWorkerLimit q) * n)
    (fun e : Fin n =>
      bankTrialDurationWorkerRemaining
        (bankTrialLocalNext ring root z e)) hpay
  have hvalue := bankTrialDurationTiltedPotentialLiveValue
    n z (k + 1) hlive (by omega)
  calc
    (List.ofFn (fun e : Fin n =>
      bankTrialDurationTiltedPotential n
        (bankTrialLocalNext ring root z e) (k + 1) + 1)).sum ≤
      (List.ofFn (fun e : Fin n =>
        n * bankTrialDurationWorkerRemaining
          (bankTrialLocalNext ring root z e) +
        (((k + 1) + ((k + 1) - 1) *
          bankTrialDurationWorkerLimit q) * n) + 1)).sum := hsum
    _ ≤ n * (n * bankTrialDurationWorkerRemaining z +
      (((k + 1) + ((k + 1) - 1) *
        bankTrialDurationWorkerLimit q) * n)) := hscalar
    _ = n * bankTrialDurationTiltedPotential n z (k + 1) := by
      rw [hvalue]

theorem bankTrialDurationTiltedPotentialStart {n q : Nat}
    (S : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (K : Nat) (hK : 1 ≤ K) :
    bankTrialDurationTiltedPotential n (bankTrialLocalStart S) K =
      (K + (K - 1) * bankTrialDurationWorkerLimit q) * n := by
  unfold bankTrialDurationTiltedPotential
  rw [if_neg (show K ≠ 0 by omega)]
  change n * bankTrialDurationWorkerRemaining
      (bankTrialLocalStart S) +
    (K + (K - 1) * bankTrialDurationWorkerLimit q) * n =
    (K + (K - 1) * bankTrialDurationWorkerLimit q) * n
  rw [bankTrialDurationWorkerRemainingClean S hclean]
  simp only [Nat.mul_zero, Nat.zero_add]

end L3

#print axioms L3.bankTrialDurationTiltedCostZeroBudget
#print axioms L3.bankTrialDurationTiltedCostZeroUnlessHead
#print axioms L3.bankTrialDurationTiltedNextOccupationExact
#print axioms L3.bankTrialDurationTiltedChildArithmetic
#print axioms L3.bankTrialDurationTiltedRootArithmetic
#print axioms L3.bankTrialDurationTiltedBellman
#print axioms L3.bankTrialDurationTiltedPotentialDead
#print axioms L3.bankTrialDurationTiltedPotentialGateDrift
#print axioms L3.bankTrialDurationTiltedPotentialLiveDrift
#print axioms L3.bankTrialDurationTiltedPotentialStart

namespace L3

open Classical

set_option autoImplicit false

/-- The original worker rank edge rows in the BANK production band,
assembled from the proved class-one and no-orphan theorems. -/
theorem bankTrialDurationWorkerRankEdgeRowsHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    BankTrialDurationWorkerRankEdgeRows (q := q) ring root :=
  bankTrialDurationRankRowsOfLeaseAwareNoOrphan ring root
    (bankTrialDurationNoReachableOrphanHolds
      ring root hsmall hw hpositive hK)
    (bankTrialDurationLeaseAwareRowsOfWeakAndServiceCoverage
      ring root hw
      (bankTrialDurationClassOneReferenceWeakRowsHolds
        ring root hw hpositive hK)
      (bankTrialDurationClassOneServiceCoverageHolds
        ring root hw hpositive hK))

/-- TILTED-BELLMAN closed: the 2^K-weighted first-K-head cut length
from a CLEAN start is at most n^T (K + (K-1) L) n, L = 4b+5. -/
theorem bankTrialDurationTiltedHeadCostBound {n q : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (hrows : BankTrialDurationWorkerRankEdgeRows (q := q) ring root)
    (S : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hK : 1 ≤ (compileAdvice q).K) (T : Nat) :
    2 ^ (compileAdvice q).K * Prob.scheduleSum n T (fun w =>
      bankTrialDurationTiltedHeadCost ring root w
        (compileAdvice q).K (bankTrialLocalStart S)) ≤
    n ^ T * (((compileAdvice q).K +
      ((compileAdvice q).K - 1) * bankTrialDurationWorkerLimit q) * n) := by
  have h := bankTrialDurationTiltedBellman ring hn root
    (BankTrialDurationReachable ring root S)
    (bankTrialDurationTiltedPotential n)
    (fun z hz e => bankTrialDurationReachableNext ring root S z hz e)
    (fun z _ hd => bankTrialDurationTiltedPotentialDead ring root z hd)
    (fun z hz hg k =>
      bankTrialDurationTiltedPotentialGateDrift
        ring hn root S hrows hclean z hz hg k)
    (fun z hz hl hng k =>
      bankTrialDurationTiltedPotentialLiveDrift
        ring hn root S hrows hclean z hz hl hng k)
    T (compileAdvice q).K (bankTrialLocalStart S) ⟨[], rfl⟩
  rw [bankTrialDurationTiltedPotentialStart S hclean _ hK] at h
  exact h

end L3

#print axioms L3.bankTrialDurationWorkerRankEdgeRowsHolds
#print axioms L3.bankTrialDurationTiltedHeadCostBound

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false


/-- A word which never earns the remaining heads has zero tilted cost. -/
theorem bankTrialDurationTiltedHeadCostNoEvent {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (w : List (Fin n)) (k : Nat) (z : BankTrialLocalState q),
      ¬ bankTrialProbabilityHeadEvent ring root w k z →
      bankTrialDurationTiltedHeadCost ring root w k z = 0 := by
  exact bankTrialDurationTiltedCostZeroUnlessHead ring root

/-- Public replacement for the earlier private cut-member event lemma. -/
theorem bankTrialDurationTiltedCutMemberEventAt
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    ∀ (T : Nat) (pre : List (Fin n))
      (z : BankTrialLocalState q) (cut : List (Fin n)),
      cut ∈ Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        (bankTrialDurationKHeadCutStop ring root S)
        T pre z →
      bankTrialProbabilityHeadEvent ring root
        (pre ++ cut) (compileAdvice q).K
        (bankTrialLocalStart S) := by
  intro T
  induction T with
  | zero =>
      intro pre z cut hcut
      by_cases hs :
          bankTrialDurationKHeadCutStop ring root S pre z = true
      · have hnil : cut = [] := by
          simpa only [Prob.firstStoppedPrefixes,
            if_pos hs, List.mem_singleton] using hcut
        rw [hnil, List.append_nil]
        change decide (bankTrialProbabilityHeadEvent
          ring root pre (compileAdvice q).K
            (bankTrialLocalStart S)) = true at hs
        exact of_decide_eq_true hs
      · have hempty : cut ∈
            ([] : List (List (Fin n))) := by
          simpa only [Prob.firstStoppedPrefixes,
            if_neg hs] using hcut
        cases hempty
  | succ t ih =>
      intro pre z cut hcut
      by_cases hs :
          bankTrialDurationKHeadCutStop ring root S pre z = true
      · have hnil : cut = [] := by
          simpa only [Prob.firstStoppedPrefixes,
            if_pos hs, List.mem_singleton] using hcut
        rw [hnil, List.append_nil]
        change decide (bankTrialProbabilityHeadEvent
          ring root pre (compileAdvice q).K
            (bankTrialLocalStart S)) = true at hs
        exact of_decide_eq_true hs
      · have hflat : cut ∈
            (List.ofFn (fun e : Fin n => e)).flatMap
              (fun e =>
                (Prob.firstStoppedPrefixes
                  (bankTrialLocalNext ring root)
                  (bankTrialDurationKHeadCutStop ring root S)
                  t (pre ++ [e])
                  (bankTrialLocalNext ring root z e)).map
                    (List.cons e)) := by
          simpa only [Prob.firstStoppedPrefixes,
            if_neg hs] using hcut
        obtain ⟨e, _, hem⟩ := List.mem_flatMap.mp hflat
        obtain ⟨tail, htail, heq⟩ := List.mem_map.mp hem
        rw [← heq]
        have hnext := ih (pre ++ [e])
          (bankTrialLocalNext ring root z e) tail htail
        simpa only [List.append_assoc, List.singleton_append]
          using hnext

/-- At an already accepted prefix, the tracked budget is zero. -/
private theorem bankTrialDurationTiltedCostAtStop
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (T : Nat) (pre : List (Fin n))
    (x : BankTrialLocalState q) (k : Nat)
    (z : BankTrialLocalState q) (cut : List (Fin n))
    (htrack : ∀ suffix : List (Fin n),
      bankTrialProbabilityHeadEvent ring root
        (pre ++ suffix) (compileAdvice q).K
        (bankTrialLocalStart S) ↔
      bankTrialProbabilityHeadEvent ring root suffix k z)
    (hs : bankTrialDurationKHeadCutStop ring root S pre x = true)
    (hmem : cut ∈ Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root)
      (bankTrialDurationKHeadCutStop ring root S)
      T pre x) :
    ∀ suffix : List (Fin n),
      bankTrialDurationTiltedHeadCost ring root
        (cut ++ suffix) k z = cut.length := by
  have hcut : cut = [] := by
    cases T with
    | zero =>
        simpa [Prob.firstStoppedPrefixes, hs] using hmem
    | succ t =>
        simpa [Prob.firstStoppedPrefixes, hs] using hmem
  have hh : bankTrialProbabilityHeadEvent ring root pre
      (compileAdvice q).K (bankTrialLocalStart S) := by
    change decide (bankTrialProbabilityHeadEvent
      ring root pre (compileAdvice q).K
      (bankTrialLocalStart S)) = true at hs
    exact of_decide_eq_true hs
  have hnil : bankTrialProbabilityHeadEvent ring root [] k z :=
    (htrack []).mp (by simpa only [List.append_nil] using hh)
  have hk : k = 0 := by
    cases k with
    | zero => rfl
    | succ j => simp [bankTrialProbabilityHeadEvent] at hnil
  subst cut
  subst k
  intro suffix
  cases suffix <;> rfl

/-- At each uncompleted prefix, the head predicate updates the
remaining budget on exactly the same observer transition.
A killed incoming edge cannot contain any selected cut. -/
theorem bankTrialDurationTiltedCutCostExact
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    ∀ (T : Nat) (pre : List (Fin n))
      (x : BankTrialLocalState q) (k : Nat)
      (z : BankTrialLocalState q) (cut : List (Fin n)),
      (∀ suffix : List (Fin n),
        bankTrialProbabilityHeadEvent ring root
          (pre ++ suffix) (compileAdvice q).K
          (bankTrialLocalStart S) ↔
        bankTrialProbabilityHeadEvent ring root suffix k z) →
      cut ∈ Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        (bankTrialDurationKHeadCutStop ring root S)
        T pre x →
      ∀ suffix : List (Fin n),
        bankTrialDurationTiltedHeadCost ring root
          (cut ++ suffix) k z = cut.length := by
  intro T
  induction T with
  | zero =>
      intro pre x k z cut htrack hmem
      by_cases hs :
          bankTrialDurationKHeadCutStop ring root S pre x = true
      · exact bankTrialDurationTiltedCostAtStop
          ring root S 0 pre x k z cut htrack hs hmem
      · have hempty : cut ∈
            ([] : List (List (Fin n))) := by
          simpa only [Prob.firstStoppedPrefixes, if_neg hs] using hmem
        cases hempty
  | succ t ih =>
      intro pre x k z cut htrack hmem
      by_cases hs :
          bankTrialDurationKHeadCutStop ring root S pre x = true
      · exact bankTrialDurationTiltedCostAtStop
          ring root S (t + 1) pre x k z cut htrack hs hmem
      · have hflat : cut ∈
            (List.ofFn (fun e : Fin n => e)).flatMap
              (fun e =>
                (Prob.firstStoppedPrefixes
                  (bankTrialLocalNext ring root)
                  (bankTrialDurationKHeadCutStop ring root S)
                  t (pre ++ [e])
                  (bankTrialLocalNext ring root x e)).map
                    (List.cons e)) := by
          simpa only [Prob.firstStoppedPrefixes, if_neg hs] using hmem
        obtain ⟨e, _, hem⟩ := List.mem_flatMap.mp hflat
        obtain ⟨tail, htail, heq⟩ := List.mem_map.mp hem
        subst cut
        have hpos : 0 < k := by
          cases k with
          | zero =>
              have hnil : bankTrialProbabilityHeadEvent ring root
                  [] 0 z := by simp [bankTrialProbabilityHeadEvent]
              have hh : bankTrialProbabilityHeadEvent ring root pre
                  (compileAdvice q).K (bankTrialLocalStart S) := by
                simpa only [List.append_nil] using (htrack []).mpr hnil
              have hstop :
                  bankTrialDurationKHeadCutStop ring root S pre x = true := by
                simp [bankTrialDurationKHeadCutStop, hh]
              exact False.elim (hs hstop)
          | succ k => omega
        cases k with
        | zero => omega
        | succ k =>
            have hgood (j : Nat)
                (hstepEvent : ∀ u : List (Fin n),
                  bankTrialProbabilityHeadEvent ring root
                    (e :: u) (k + 1) z ↔
                  bankTrialProbabilityHeadEvent ring root u j
                    (bankTrialLocalNext ring root z e))
                (hstepCost : ∀ u : List (Fin n),
                  bankTrialDurationTiltedHeadCost ring root
                    (e :: u) (k + 1) z =
                    (if bankTrialProbabilityHeadEvent ring root u j
                      (bankTrialLocalNext ring root z e) then 1 else 0) +
                    bankTrialDurationTiltedHeadCost ring root u j
                      (bankTrialLocalNext ring root z e)) :
                ∀ suffix : List (Fin n),
                  bankTrialDurationTiltedHeadCost ring root
                    ((e :: tail) ++ suffix) (k + 1) z =
                      (e :: tail).length := by
              intro suffix
              have htrack' (u : List (Fin n)) :
                  bankTrialProbabilityHeadEvent ring root
                    ((pre ++ [e]) ++ u) (compileAdvice q).K
                    (bankTrialLocalStart S) ↔
                  bankTrialProbabilityHeadEvent ring root u j
                    (bankTrialLocalNext ring root z e) := by
                have hh := (htrack (e :: u)).trans (hstepEvent u)
                simpa only [List.append_assoc, List.singleton_append] using hh
              have hchild := ih (pre ++ [e])
                (bankTrialLocalNext ring root x e)
                j (bankTrialLocalNext ring root z e)
                tail htrack' htail suffix
              have hfirst :
                  bankTrialProbabilityHeadEvent ring root
                    (pre ++ (e :: tail)) (compileAdvice q).K
                    (bankTrialLocalStart S) :=
                bankTrialDurationTiltedCutMemberEventAt
                  ring root S (t + 1) pre x (e :: tail) hmem
              have hfull := bankTrialDurationKHeadEventAppend
                ring root (pre ++ (e :: tail)) suffix
                (compileAdvice q).K (bankTrialLocalStart S) hfirst
              have hparent :
                  bankTrialProbabilityHeadEvent ring root
                    (e :: (tail ++ suffix)) (k + 1) z :=
                (htrack (e :: (tail ++ suffix))).mp
                  (by simpa only [List.append_assoc, List.cons_append]
                    using hfull)
              have hchildEvent :=
                (hstepEvent (tail ++ suffix)).mp hparent
              calc
                bankTrialDurationTiltedHeadCost ring root
                    ((e :: tail) ++ suffix) (k + 1) z =
                  (if bankTrialProbabilityHeadEvent ring root
                      (tail ++ suffix) j
                      (bankTrialLocalNext ring root z e)
                    then 1 else 0) +
                    bankTrialDurationTiltedHeadCost ring root
                      (tail ++ suffix) j
                      (bankTrialLocalNext ring root z e) := by
                        simpa only [List.cons_append]
                          using hstepCost (tail ++ suffix)
                _ = (e :: tail).length := by
                  rw [if_pos hchildEvent, hchild]
                  simp only [List.length_cons]
                  omega
            intro suffix
            by_cases hg : BankTrialProbabilityArmedGate z
            · by_cases he : e = root
              · exact hgood k
                  (fun u => by simp [bankTrialProbabilityHeadEvent, hg, he])
                  (fun u => by simp [bankTrialDurationTiltedHeadCost, hg, he])
                  suffix
              · by_cases hi : ring.rightNeighbor e = root
                · have hfirst :
                    bankTrialProbabilityHeadEvent ring root
                      (pre ++ (e :: tail)) (compileAdvice q).K
                      (bankTrialLocalStart S) :=
                    bankTrialDurationTiltedCutMemberEventAt
                      ring root S (t + 1) pre x (e :: tail) hmem
                  have hparent :=
                    (htrack (e :: tail)).mp hfirst
                  have hfalse : False := by
                    simpa [bankTrialProbabilityHeadEvent, hg, he, hi]
                      using hparent
                  exact False.elim hfalse
                · exact hgood (k + 1)
                    (fun u => by simp [bankTrialProbabilityHeadEvent, hg, he, hi])
                    (fun u => by simp [bankTrialDurationTiltedHeadCost, hg, he, hi])
                    suffix
            · exact hgood (k + 1)
                (fun u => by simp [bankTrialProbabilityHeadEvent, hg])
                (fun u => by simp [bankTrialDurationTiltedHeadCost, hg])
                suffix

/-- Extensionality of a finite mapped Nat sum, allowing equality
only on the selected cuts rather than on all possible lists. -/
private theorem bankTrialDurationTiltedMapSumOnCuts
    {A : Type} (xs : List A) (f g : A → Nat)
    (h : ∀ x, x ∈ xs → f x = g x) :
    (xs.map f).sum = (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx : f x = g x := h x (by simp)
      have ht : (xs.map f).sum = (xs.map g).sum :=
        ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons, List.sum_cons]
      rw [hx, ht]

/-- (b1) Tilted chronological occupation is exactly the
first-K-head cut length moment, including all original-tape
extensions and without a new independent experiment. -/
theorem bankTrialDurationTiltedHeadCostEqCutMoment
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) :
    bankTrialDurationKHeadCutMoment ring root S T =
      Prob.scheduleSum n T (fun w =>
        bankTrialDurationTiltedHeadCost ring root w
          (compileAdvice q).K (bankTrialLocalStart S)) := by
  change
    ((Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root)
      (bankTrialDurationKHeadCutStop ring root S)
      T [] (bankTrialLocalStart S)).map
        (fun cut => cut.length * n ^ (T - cut.length))).sum =
      Prob.scheduleSum n T (fun w =>
        bankTrialDurationTiltedHeadCost ring root w
          (compileAdvice q).K (bankTrialLocalStart S))
  calc
    ((Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        (bankTrialDurationKHeadCutStop ring root S)
        T [] (bankTrialLocalStart S)).map
          (fun cut => cut.length * n ^ (T - cut.length))).sum =
      ((Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        (bankTrialDurationKHeadCutStop ring root S)
        T [] (bankTrialLocalStart S)).map
          (fun cut =>
            Prob.scheduleSum n (T - cut.length) (fun suffix =>
              bankTrialDurationTiltedHeadCost ring root
                (cut ++ suffix) (compileAdvice q).K
                (bankTrialLocalStart S)))).sum := by
          apply bankTrialDurationTiltedMapSumOnCuts
          intro cut hcut
          have htrack : ∀ u : List (Fin n),
              bankTrialProbabilityHeadEvent ring root
                ([] ++ u) (compileAdvice q).K
                (bankTrialLocalStart S) ↔
              bankTrialProbabilityHeadEvent ring root u
                (compileAdvice q).K (bankTrialLocalStart S) := by
            intro u
            simp
          have hcost := bankTrialDurationTiltedCutCostExact
            ring root S T [] (bankTrialLocalStart S)
            (compileAdvice q).K (bankTrialLocalStart S)
            cut htrack hcut
          have hfun :
              (fun suffix : List (Fin n) =>
                bankTrialDurationTiltedHeadCost ring root
                  (cut ++ suffix) (compileAdvice q).K
                  (bankTrialLocalStart S)) =
              (fun _ : List (Fin n) => cut.length) := by
            funext suffix
            exact hcost suffix
          rw [hfun, bankTrialProbabilityScheduleSumConst,
            Nat.mul_comm]
    _ = Prob.scheduleSum n T (fun word =>
          if bankTrialProbabilityHeadEvent ring root word
              (compileAdvice q).K (bankTrialLocalStart S)
          then bankTrialDurationTiltedHeadCost ring root word
            (compileAdvice q).K (bankTrialLocalStart S)
          else 0) :=
      (bankTrialDurationKHeadWeightedCutFactorization
        ring root S
        (fun word => bankTrialDurationTiltedHeadCost ring root
          word (compileAdvice q).K (bankTrialLocalStart S)) T).symm
    _ = Prob.scheduleSum n T (fun word =>
          bankTrialDurationTiltedHeadCost ring root word
            (compileAdvice q).K (bankTrialLocalStart S)) := by
      apply congrArg (Prob.scheduleSum n T)
      funext word
      by_cases hh : bankTrialProbabilityHeadEvent ring root word
          (compileAdvice q).K (bankTrialLocalStart S)
      · simp [hh]
      · simp [hh, bankTrialDurationTiltedHeadCostNoEvent
          ring root word (compileAdvice q).K (bankTrialLocalStart S) hh]

/-- An opaque coefficient comparison; no large compileAdvice
power occurs in its arithmetic proof. -/
private theorem bankTrialDurationTiltedStartAllowance
    (k b n : Nat) :
    (k + (k - 1) * (4 * b + 5)) * n ≤
      (k + (k - 1) * (4 * b + 7)) * n := by
  have hc : 4 * b + 5 ≤ 4 * b + 7 := by omega
  exact Nat.mul_le_mul_right n
    (Nat.add_le_add_left (Nat.mul_le_mul_left (k - 1) hc) k)

/-- (b2) The Bellman consequence on each CLEAN-reachable set
implies the exact C.8 all-heads mean inequality. The argument
hbell is precisely the generic Bellman conclusion specialized
to reachable G and the tilted potential F; its drift premises
are supplied by the independent rounds. -/
theorem bankTrialDurationKHeadAllHeadsMeanInequalityOfTilted
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hpositive : 0 < (compileAdvice q).K)
    (hbell : ∀ (S : GrantBankReference.BankLocalReference
        (compileAdvice q).b) (T k : Nat)
        (z : BankTrialLocalState q),
      BankTrialDurationReachable ring root S z →
      2 ^ k * Prob.scheduleSum n T (fun w =>
        bankTrialDurationTiltedHeadCost ring root w k z) ≤
        n ^ T * bankTrialDurationTiltedPotential n z k) :
    BankTrialDurationKHeadAllHeadsMeanInequality
      (q := q) ring root := by
  intro S hclean _ _
  intro T
  have hreach : BankTrialDurationReachable ring root S
      (bankTrialLocalStart S) := ⟨[], rfl⟩
  have hbound := hbell S T (compileAdvice q).K
    (bankTrialLocalStart S) hreach
  rw [← bankTrialDurationTiltedHeadCostEqCutMoment ring root S T]
    at hbound
  have hlimit :
      bankTrialDurationWorkerLimit q =
        4 * (compileAdvice q).b + 5 := by
    unfold bankTrialDurationWorkerLimit
    omega
  have hstart :
      bankTrialDurationTiltedPotential n (bankTrialLocalStart S)
        (compileAdvice q).K =
      (((compileAdvice q).K +
        ((compileAdvice q).K - 1) *
          (4 * (compileAdvice q).b + 5)) * n) := by
    unfold bankTrialDurationTiltedPotential
    rw [if_neg (Nat.ne_of_gt hpositive)]
    change
      n * bankTrialDurationWorkerRemaining (bankTrialLocalStart S) +
        ((compileAdvice q).K +
          ((compileAdvice q).K - 1) *
            bankTrialDurationWorkerLimit q) * n =
      (((compileAdvice q).K +
        ((compileAdvice q).K - 1) *
          (4 * (compileAdvice q).b + 5)) * n)
    rw [bankTrialDurationWorkerRemainingClean S hclean, hlimit]
    simp
  rw [hstart] at hbound
  exact Nat.le_trans hbound
    (Nat.mul_le_mul_left (n ^ T)
      (bankTrialDurationTiltedStartAllowance
        (compileAdvice q).K (compileAdvice q).b n))

end L3

#print axioms L3.bankTrialDurationTiltedHeadCostNoEvent
#print axioms L3.bankTrialDurationTiltedCutMemberEventAt
#print axioms L3.bankTrialDurationTiltedCutCostExact
#print axioms L3.bankTrialDurationTiltedHeadCostEqCutMoment
#print axioms L3.bankTrialDurationKHeadAllHeadsMeanInequalityOfTilted

namespace L3

open Classical

set_option autoImplicit false

/-- G12e: the K-head mean inequality, from the tilted Bellman bound
and the bridge to the first-cut moment. The coefficient 4b+5 of the
proof sits below the stated 4b+7. -/
theorem bankTrialDurationKHeadAllHeadsMeanInequalityHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    BankTrialDurationKHeadAllHeadsMeanInequality (q := q) ring root := by
  have hn : 2 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    omega
  intro S hclean hsmall _ T
  rw [bankTrialDurationTiltedHeadCostEqCutMoment]
  have hb := bankTrialDurationTiltedHeadCostBound ring hn root
    (bankTrialDurationWorkerRankEdgeRowsHolds
      ring root hsmall hw hpositive hK)
    S hclean hpositive T
  refine Nat.le_trans hb (Nat.mul_le_mul_left _ ?_)
  apply Nat.mul_le_mul_right
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  unfold bankTrialDurationWorkerLimit
  omega

/-- G12e CLOSED: paper C.8, the success-conditioned trial duration
on the BANK band, (WON + ACTIVE) * (8b+12)(K+1)n. -/
theorem bankTrialDurationSuccessConditionalTargetHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hsmall : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    BankTrialDurationSuccessConditionalTarget (q := q) ring root := by
  have hn : 2 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    omega
  exact bankTrialDurationSuccessConditionalOfScaleCharge ring root
    hsmall hlarge
    (bankTrialDurationAllKHeadChargeAtSuccessScaleOfBudgets ring root
      (bankTrialDurationKHeadCutLengthChargeHolds ring root hn
        hpositive hK
        (bankTrialDurationKHeadAllHeadsMeanInequalityHolds
          ring root hw hpositive hK))
      (bankTrialDurationKHeadPostCutBudgetHolds ring root
        hpositive hK))
    (bankTrialDurationAllKHeadSurvivalEstimateHolds ring root hK)

end L3

#print axioms L3.bankTrialDurationKHeadAllHeadsMeanInequalityHolds
#print axioms L3.bankTrialDurationSuccessConditionalTargetHolds

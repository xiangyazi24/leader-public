import Leader.L3.Bank.TrialDuration

/-!
G12d, paper Appendix C (spatial-counter.tex on main), C.2 and C.6: recovery from
the actual reachable authenticated local cut costs at most (2L+2)n, L = 2b+2,
on the local trial observer from every CLEAN seed.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- In a nonterminal state, stage two is exactly RECOVERY;
WON and LOST have class two but are not charged. -/
theorem bankTrialDurationNonterminalRecoveryClass {q : Nat}
    (z : BankTrialLocalState q)
    (hnot : ¬ bankTrialLocalTerminal z) :
    bankTrialDurationClass z = 2 ↔ z.phase = .recovery := by
  cases z with
  | mk B phase =>
      cases phase with
      | live begun =>
          constructor
          · intro hc
            change
              (if (B.fields ⟨0, by omega⟩).1 = .ARMED
               then 0 else 1) = 2 at hc
            split at hc <;> omega
          · intro hp
            cases hp
      | recovery =>
          exact ⟨fun _ => rfl, fun _ => rfl⟩
      | won =>
          exact False.elim (hnot (Or.inl rfl))
      | lost =>
          exact False.elim (hnot (Or.inr rfl))

/-- Every CLEAN-reachable local RECOVERY snapshot has the
FULL clamped RESET/RWAIT front certificate, not merely a
mode-band property.  Only the distinct-ports hypothesis is used. -/
theorem bankTrialDurationReachableRecoveryCert {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (z : BankTrialLocalState q)
    (hreach : BankTrialDurationReachable ring root S z)
    (hrec : z.phase = .recovery) :
    BankTrialLocalRecoveryCert q z.bank := by
  obtain ⟨w, hw⟩ := hreach
  cases z with
  | mk B phase =>
      cases hrec
      exact bankTrialLocalRecoveryCertReachableOfStepPremise
        ring root
        (bankTrialLocalRecoveryCertStepPremise (q := q) ring root hn)
        S hclean w B hw

/-- RECOVERY never goes back to LIVE; it stays RECOVERY
or becomes one of the two absorbing observer states. -/
theorem bankTrialDurationRecoverySuccessor {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    (bankTrialLocalNext ring root
      (⟨B, .recovery⟩ : BankTrialLocalState q) e).phase =
        .recovery ∨
      bankTrialLocalTerminal
        (bankTrialLocalNext ring root
          (⟨B, .recovery⟩ : BankTrialLocalState q) e) := by
  have hzero :=
    bankTrialDurationRecoveryRacePotentialZero ring root e B
  cases hp : (bankTrialLocalNext ring root
      (⟨B, .recovery⟩ : BankTrialLocalState q) e).phase with
  | live begun =>
      unfold bankTrialDurationRacePotential at hzero
      rw [hp] at hzero
      exact False.elim ((Nat.ne_of_gt ring.hn) hzero)
  | recovery =>
      left
      simpa only [hp]
  | won =>
      right
      left
      simpa only [hp]
  | lost =>
      right
      right
      simpa only [hp]

/-- From a RECOVERY cut, all preterminal letters are charged
as stage two.  Thus its stage-two word charge is exactly the
standard stopped-time word charge, on the ORIGINAL Fin n tape. -/
theorem bankTrialDurationRecoveryWordCost {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (w : List (Fin n)) (z : BankTrialLocalState q),
      (z.phase = .recovery ∨ bankTrialLocalTerminal z) →
      bankTrialDurationStageWord ring root 2 z w =
        costWord (bankTrialLocalNext ring root)
          bankTrialLocalTerminal z w := by
  intro w
  induction w with
  | nil =>
      intro z _
      rfl
  | cons e es ih =>
      intro z hz
      rcases hz with hrec | hterminal
      · have hnot : ¬ bankTrialLocalTerminal z := by
          intro ht
          rcases ht with hw | hl
          · rw [hrec] at hw
            cases hw
          · rw [hrec] at hl
            cases hl
        have hc :
            bankTrialDurationClass z = 2 :=
          (bankTrialDurationNonterminalRecoveryClass z hnot).2 hrec
        have hnext :
            (bankTrialLocalNext ring root z e).phase = .recovery ∨
            bankTrialLocalTerminal (bankTrialLocalNext ring root z e) := by
          cases z with
          | mk B phase =>
              cases hrec
              exact bankTrialDurationRecoverySuccessor ring root e B
        have hs :
            bankTrialDurationStageWord ring root 2 z (e :: es) =
              1 + bankTrialDurationStageWord ring root 2
                (bankTrialLocalNext ring root z e) es := by
          simp only [bankTrialDurationStageWord,
            if_neg hnot, if_pos hc]
        have hr :
            costWord (bankTrialLocalNext ring root)
                bankTrialLocalTerminal z (e :: es) =
              1 + costWord (bankTrialLocalNext ring root)
                bankTrialLocalTerminal
                (bankTrialLocalNext ring root z e) es := by
          simp only [costWord,
            K2FiniteSafeEliminationExpected.rawCost, if_neg hnot]
        calc
          bankTrialDurationStageWord ring root 2 z (e :: es) =
              1 + bankTrialDurationStageWord ring root 2
                (bankTrialLocalNext ring root z e) es := hs
          _ = 1 + costWord (bankTrialLocalNext ring root)
                bankTrialLocalTerminal
                (bankTrialLocalNext ring root z e) es := by
                  rw [ih _ hnext]
          _ = costWord (bankTrialLocalNext ring root)
                bankTrialLocalTerminal z (e :: es) := hr.symm
      · have hs :
            bankTrialDurationStageWord ring root 2 z (e :: es) =
              0 := by
          simp only [bankTrialDurationStageWord, if_pos hterminal]
        have hr :
            costWord (bankTrialLocalNext ring root)
                bankTrialLocalTerminal z (e :: es) = 0 := by
          simp only [costWord,
            K2FiniteSafeEliminationExpected.rawCost, if_pos hterminal]
        exact hs.trans hr.symm

/-- Exactly (2L+2)n for L=2b+2. -/
def bankTrialDurationRecoveryAllowance (n q : Nat) : Nat :=
  (2 * (2 * (compileAdvice q).b + 2) + 2) * n

/-- The missing quantitative local C.2 statement, for each
authenticated reachable RECOVERY cut.  This is a Prop only,
NOT a theorem, and not an assumption of the pinned target. -/
def BankTrialDurationRecoveryCutBound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    BankTrialLocalClean q S →
    ∀ (z : BankTrialLocalState q),
      BankTrialDurationReachable ring root S z →
      z.phase = .recovery →
      ∀ T : Nat,
        costNumerator (bankTrialLocalNext ring root)
          bankTrialLocalTerminal z T ≤
          n ^ T * bankTrialDurationRecoveryAllowance n q

/-- The exact once-only recovery-entry accounting.  A uniform
local stopped-time bound at reachable RECOVERY cuts implies the
whole CLEAN-seeded stage-two mass bound without charging LIVE
prefixes or assuming independent scheduler tapes. -/
theorem bankTrialDurationRecoveryBudgetOfCutBound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hcut : BankTrialDurationRecoveryCutBound (q := q) ring root) :
    BankTrialDurationRecoveryBudget (q := q) ring root := by
  intro S hclean T
  have hbound :
      ∀ (U : Nat) (z : BankTrialLocalState q),
        BankTrialDurationReachable ring root S z →
        Prob.scheduleSum n U
          (bankTrialDurationStageWord ring root 2 z) ≤
          n ^ U * bankTrialDurationRecoveryAllowance n q := by
    intro U
    induction U with
    | zero =>
        intro z _
        rw [bankTrialProbabilityScheduleSumZero]
        exact Nat.zero_le _
    | succ U ih =>
        intro z hz
        by_cases hterminal : bankTrialLocalTerminal z
        · have hfun :
              bankTrialDurationStageWord ring root 2 z =
                (fun _ : List (Fin n) => 0) := by
            funext w
            cases w with
            | nil => rfl
            | cons e es =>
                simp only [bankTrialDurationStageWord,
                  if_pos hterminal]
          rw [hfun, bankTrialProbabilityScheduleSumConst]
          simp only [Nat.mul_zero]
          exact Nat.zero_le _
        · by_cases hrec : z.phase = .recovery
          · have heq :
                bankTrialDurationStageWord ring root 2 z =
                  costWord (bankTrialLocalNext ring root)
                    bankTrialLocalTerminal z := by
              funext w
              exact bankTrialDurationRecoveryWordCost ring root
                w z (Or.inl hrec)
            have hcost := hcut S hclean z hz hrec (U + 1)
            change
              Prob.scheduleSum n (U + 1)
                (costWord (bankTrialLocalNext ring root)
                  bankTrialLocalTerminal z) ≤
              n ^ (U + 1) *
                bankTrialDurationRecoveryAllowance n q at hcost
            rw [← heq] at hcost
            exact hcost
          · have hclass : bankTrialDurationClass z ≠ 2 := by
              intro htwo
              exact hrec
                ((bankTrialDurationNonterminalRecoveryClass
                  z hterminal).1 htwo)
            rw [bankTrialProbabilityScheduleSumFirst]
            have hstep (e : Fin n) :
                Prob.scheduleSum n U
                  (fun w : List (Fin n) =>
                    bankTrialDurationStageWord ring root 2
                      z (e :: w)) =
                Prob.scheduleSum n U
                  (bankTrialDurationStageWord ring root 2
                    (bankTrialLocalNext ring root z e)) := by
              have hfun :
                  (fun w : List (Fin n) =>
                    bankTrialDurationStageWord ring root 2
                      z (e :: w)) =
                  (bankTrialDurationStageWord ring root 2
                    (bankTrialLocalNext ring root z e)) := by
                funext w
                simp only [bankTrialDurationStageWord,
                  if_neg hterminal, if_neg hclass, Nat.zero_add]
              exact congrArg (Prob.scheduleSum n U) hfun
            have hsum :=
              FiniteUniformStoppingTree.ofFn_sum_eq
                (fun e : Fin n =>
                  Prob.scheduleSum n U
                    (fun w : List (Fin n) =>
                      bankTrialDurationStageWord ring root 2
                        z (e :: w)))
                (fun e : Fin n =>
                  Prob.scheduleSum n U
                    (bankTrialDurationStageWord ring root 2
                      (bankTrialLocalNext ring root z e)))
                hstep
            rw [hsum]
            have hchildren :=
              FiniteUniformStoppingTree.ofFn_sum_le
                (fun e : Fin n =>
                  Prob.scheduleSum n U
                    (bankTrialDurationStageWord ring root 2
                      (bankTrialLocalNext ring root z e)))
                (fun _ : Fin n =>
                  n ^ U * bankTrialDurationRecoveryAllowance n q)
                (fun e =>
                  ih (bankTrialLocalNext ring root z e)
                    (bankTrialDurationReachableNext
                      ring root S z hz e))
            calc
              (List.ofFn (fun e : Fin n =>
                Prob.scheduleSum n U
                  (bankTrialDurationStageWord ring root 2
                    (bankTrialLocalNext ring root z e)))).sum ≤
                  (List.ofFn (fun _ : Fin n =>
                    n ^ U *
                      bankTrialDurationRecoveryAllowance n q)).sum :=
                    hchildren
              _ = n ^ (U + 1) *
                  bankTrialDurationRecoveryAllowance n q := by
                rw [FiniteUniformStoppingTree.ofFn_sum_const,
                  Nat.pow_succ]
                ac_rfl
  have hstart :
      BankTrialDurationReachable ring root S
        (bankTrialLocalStart S) := ⟨[], rfl⟩
  have hresult := hbound T (bankTrialLocalStart S) hstart
  change bankTrialDurationStageMass ring root 2 S T ≤
    n ^ T * bankTrialDurationRecoveryAllowance n q at hresult
  exact hresult

/-- Stronger source-form obligation: all locally authenticated
RESET/RWAIT fronts obey C.2.  This still needs a new local
renewal/retry proof; the physical Counter result is not its type. -/
def BankTrialDurationAuthenticatedRecoveryBound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    BankTrialLocalRecoveryCert q B →
    ∀ T : Nat,
      costNumerator (bankTrialLocalNext ring root)
        bankTrialLocalTerminal
        (⟨B, .recovery⟩ : BankTrialLocalState q) T ≤
      n ^ T * bankTrialDurationRecoveryAllowance n q

/-- Genuine CLEAN-reachable recovery cuts inherit the stronger
authenticated-cut budget. This transfer uses 2 ≤ n only. -/
theorem bankTrialDurationRecoveryCutBoundOfAuthenticated
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hauth : BankTrialDurationAuthenticatedRecoveryBound (q := q) ring root) :
    BankTrialDurationRecoveryCutBound (q := q) ring root := by
  intro S hclean z hz hrec T
  cases z with
  | mk B phase =>
      cases hrec
      have hcert := bankTrialDurationReachableRecoveryCert
        ring root hn S hclean
        (⟨B, .recovery⟩ : BankTrialLocalState q) hz rfl
      exact hauth B hcert T

/-- The remaining dependency of the pinned theorem is exactly
the authenticated local RESET/RWAIT renewal estimate. -/
theorem bankTrialDurationRecoveryBudgetOfAuthenticated
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hauth : BankTrialDurationAuthenticatedRecoveryBound (q := q) ring root) :
    BankTrialDurationRecoveryBudget (q := q) ring root :=
  bankTrialDurationRecoveryBudgetOfCutBound (q := q) ring root
    (bankTrialDurationRecoveryCutBoundOfAuthenticated (q := q)
      ring root hn hauth)

/-- Exact additivity on the original finite scheduler-tape mass. -/
private theorem bankTrialDurationRecoveryScheduleAdd (n T : Nat)
    (f g : List (Fin n) → Nat) :
    Prob.scheduleSum n T (fun w => f w + g w) =
      Prob.scheduleSum n T f + Prob.scheduleSum n T g := by
  change FixedSpanRenewalPayload.wordSum n T
      (fun w => f w + g w) =
    FixedSpanRenewalPayload.wordSum n T f +
      FixedSpanRenewalPayload.wordSum n T g
  rw [← FixedSpanRenewalPayload.rawWord_sum n T
        (fun w => f w + g w),
      ← FixedSpanRenewalPayload.rawWord_sum n T f,
      ← FixedSpanRenewalPayload.rawWord_sum n T g,
      FiniteUniformStoppingTree.ofFn_sum_add]

/-- Without any recovery-progress premise, stage-two occupation
is at most the entire T-letter scheduler horizon.  This is
an unconditional but horizon-dependent bound, not C.6. -/
theorem bankTrialDurationRecoveryHorizonMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (T : Nat) (z : BankTrialLocalState q),
      Prob.scheduleSum n T
        (bankTrialDurationStageWord ring root 2 z) ≤
      n ^ T * T := by
  intro T
  induction T with
  | zero =>
      intro z
      rw [bankTrialProbabilityScheduleSumZero]
      simp [bankTrialDurationStageWord]
  | succ T ih =>
      intro z
      rw [bankTrialProbabilityScheduleSumFirst]
      have hchild (e : Fin n) :
          Prob.scheduleSum n T
            (fun w => bankTrialDurationStageWord
              ring root 2 z (e :: w)) ≤
          n ^ T * (T + 1) := by
        by_cases hterminal : bankTrialLocalTerminal z
        · have hzero :
              (fun w : List (Fin n) =>
                bankTrialDurationStageWord
                  ring root 2 z (e :: w)) =
              (fun _ : List (Fin n) => 0) := by
            funext w
            simp only [bankTrialDurationStageWord,
              if_pos hterminal]
          rw [hzero, bankTrialProbabilityScheduleSumConst]
          simp only [Nat.mul_zero]
          exact Nat.zero_le _
        · have hcharge :
              (if bankTrialDurationClass z = 2 then
                1 else 0) ≤ 1 := by
            split <;> omega
          have hstep :
              (fun w : List (Fin n) =>
                bankTrialDurationStageWord
                  ring root 2 z (e :: w)) =
              (fun w : List (Fin n) =>
                (if bankTrialDurationClass z = 2 then
                  1 else 0) +
                bankTrialDurationStageWord ring root 2
                  (bankTrialLocalNext ring root z e) w) := by
            funext w
            simp only [bankTrialDurationStageWord,
              if_neg hterminal]
          rw [hstep,
            bankTrialDurationRecoveryScheduleAdd n T
              (fun _ : List (Fin n) =>
                if bankTrialDurationClass z = 2 then
                  1 else 0)
              (bankTrialDurationStageWord ring root 2
                (bankTrialLocalNext ring root z e)),
            bankTrialProbabilityScheduleSumConst]
          calc
            n ^ T *
                (if bankTrialDurationClass z = 2 then
                  1 else 0) +
              Prob.scheduleSum n T
                (bankTrialDurationStageWord ring root 2
                  (bankTrialLocalNext ring root z e)) ≤
                n ^ T * 1 + n ^ T * T :=
              Nat.add_le_add
                (Nat.mul_le_mul_left (n ^ T) hcharge)
                (ih (bankTrialLocalNext ring root z e))
            _ = n ^ T * (T + 1) := by
              rw [Nat.mul_add]
              omega
      calc
        (List.ofFn (fun e : Fin n =>
          Prob.scheduleSum n T
            (fun w => bankTrialDurationStageWord
              ring root 2 z (e :: w)))).sum ≤
            (List.ofFn (fun _ : Fin n =>
              n ^ T * (T + 1))).sum :=
          FiniteUniformStoppingTree.ofFn_sum_le _ _
            hchild
        _ = n ^ (T + 1) * (T + 1) := by
          rw [FiniteUniformStoppingTree.ofFn_sum_const,
            Nat.pow_succ]
          ac_rfl

/-- The exact C.6 numerical allowance is automatic for
horizons no larger than the allowance itself.  Longer horizons
need the as-yet-unproved authenticated local renewal estimate. -/
theorem bankTrialDurationRecoveryShortHorizon {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat)
    (hT :
      T ≤ (2 * (2 * (compileAdvice q).b + 2) + 2) * n) :
    bankTrialDurationStageMass ring root 2 S T ≤
      n ^ T *
        ((2 * (2 * (compileAdvice q).b + 2) + 2) * n) := by
  have hcrude := bankTrialDurationRecoveryHorizonMass
    ring root T (bankTrialLocalStart S)
  change bankTrialDurationStageMass ring root 2 S T ≤
    n ^ T * T at hcrude
  exact Nat.le_trans hcrude
    (Nat.mul_le_mul_left (n ^ T) hT)

/-- A certified RWAIT recovery cut contains a valid abstract
reset front.  Its remaining productive-service rank is at most
2*b-1.  This is structural only: it does not bound how many
scheduler letters are needed to obtain those services. -/
theorem bankTrialDurationCertifiedRecoveryFrontRank {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalRecoveryCert q B)
    (hm : bankTrialLiveWaveRootMode B = .RWAIT) :
    ∃ stage : Counter.ResetClockStage,
      Counter.resetClockValid (compileAdvice q).b stage ∧
      (match stage with
       | .outward j => BankTrialLocalFrontOut q B j
       | .returning j => BankTrialLocalFrontBack q B j
       | .finished => False) ∧
      Counter.resetClockRank (compileAdvice q).b stage ≤
        2 * (compileAdvice q).b - 1 := by
  have hroot :
      (B.fields ⟨0, by omega⟩).1 = .RWAIT := hm
  rcases hc.2.2 with hreset | hwait
  · rw [hroot] at hreset
    cases hreset
  · rcases hwait with ⟨_, _, _, hfront⟩
    rcases hfront with ⟨j, hout⟩ | ⟨j, hback⟩
    · have hjpos : 1 ≤ j := hout.2.1
      have hjbound : j ≤ (compileAdvice q).b := hout.1
      refine ⟨.outward j, ⟨hjpos, hjbound⟩, hout, ?_⟩
      change 2 * (compileAdvice q).b - j ≤
        2 * (compileAdvice q).b - 1
      omega
    · have hjpos : 1 ≤ j := hback.2.1
      have hjbound : j ≤ (compileAdvice q).b := hback.1
      refine ⟨.returning j, ⟨hjpos, hjbound⟩, hback, ?_⟩
      change j ≤ 2 * (compileAdvice q).b - 1
      omega

theorem bankTrialDurationRecoveryTwiceChargedOfDrift {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (potential : BankTrialLocalState q → Nat)
    (hdrift : ∀ z : BankTrialLocalState q,
      BankTrialDurationReachable ring root S z →
      ¬ bankTrialLocalTerminal z →
      2 * n *
          (if bankTrialDurationClass z = 2 then 1 else 0) +
        (List.ofFn (fun e : Fin n =>
          potential (bankTrialLocalNext ring root z e))).sum ≤
        n * potential z) :
    ∀ (T : Nat) (z : BankTrialLocalState q),
      BankTrialDurationReachable ring root S z →
      2 * Prob.scheduleSum n T
          (bankTrialDurationStageWord ring root 2 z) ≤
        n ^ T * potential z := by
  intro T
  induction T with
  | zero =>
      intro z _
      rw [bankTrialProbabilityScheduleSumZero]
      simp only [bankTrialDurationStageWord,
        Nat.mul_zero, Nat.zero_le]
  | succ T ih =>
      intro z hz
      by_cases ht : bankTrialLocalTerminal z
      · have hfun :
            bankTrialDurationStageWord ring root 2 z =
              (fun _ : List (Fin n) => 0) := by
          funext word
          cases word with
          | nil => rfl
          | cons e rest =>
              simp only [bankTrialDurationStageWord, if_pos ht]
        rw [hfun, bankTrialProbabilityScheduleSumConst]
        simp only [Nat.mul_zero, Nat.zero_le]
      · rw [bankTrialProbabilityScheduleSumFirst]
        have hstep (e : Fin n) :
            Prob.scheduleSum n T
              (fun w : List (Fin n) =>
                bankTrialDurationStageWord ring root 2 z (e :: w)) =
              n ^ T *
                (if bankTrialDurationClass z = 2 then 1 else 0) +
              Prob.scheduleSum n T
                (bankTrialDurationStageWord ring root 2
                  (bankTrialLocalNext ring root z e)) := by
          have heq :
              (fun w : List (Fin n) =>
                bankTrialDurationStageWord ring root 2 z (e :: w)) =
              (fun w : List (Fin n) =>
                (if bankTrialDurationClass z = 2 then 1 else 0) +
                  bankTrialDurationStageWord ring root 2
                    (bankTrialLocalNext ring root z e) w) := by
            funext w
            simp only [bankTrialDurationStageWord, if_neg ht]
          rw [heq, bankTrialDurationRecoveryScheduleAdd,
            bankTrialProbabilityScheduleSumConst]
        have hchildren :
            2 * (List.ofFn (fun e : Fin n =>
              Prob.scheduleSum n T
                (bankTrialDurationStageWord ring root 2
                  (bankTrialLocalNext ring root z e)))).sum ≤
            n ^ T * (List.ofFn (fun e : Fin n =>
              potential (bankTrialLocalNext ring root z e))).sum := by
          calc
            2 * (List.ofFn (fun e : Fin n =>
              Prob.scheduleSum n T
                (bankTrialDurationStageWord ring root 2
                  (bankTrialLocalNext ring root z e)))).sum =
              (List.ofFn (fun e : Fin n =>
                2 * Prob.scheduleSum n T
                  (bankTrialDurationStageWord ring root 2
                    (bankTrialLocalNext ring root z e)))).sum := by
                  rw [FiniteUniformStoppingTree.ofFn_sum_mul_left]
            _ ≤ (List.ofFn (fun e : Fin n =>
                  n ^ T * potential
                    (bankTrialLocalNext ring root z e))).sum :=
              FiniteUniformStoppingTree.ofFn_sum_le _ _
                (fun e => ih (bankTrialLocalNext ring root z e)
                  (bankTrialDurationReachableNext ring root S z hz e))
            _ = n ^ T * (List.ofFn (fun e : Fin n =>
                  potential (bankTrialLocalNext ring root z e))).sum := by
              rw [FiniteUniformStoppingTree.ofFn_sum_mul_left]
        have hsum :=
          FiniteUniformStoppingTree.ofFn_sum_eq
            (fun e : Fin n =>
              Prob.scheduleSum n T
                (fun w : List (Fin n) =>
                  bankTrialDurationStageWord ring root 2 z (e :: w)))
            (fun e : Fin n =>
              n ^ T *
                  (if bankTrialDurationClass z = 2 then 1 else 0) +
              Prob.scheduleSum n T
                (bankTrialDurationStageWord ring root 2
                  (bankTrialLocalNext ring root z e)))
            hstep
        rw [hsum, FiniteUniformStoppingTree.ofFn_sum_add,
          FiniteUniformStoppingTree.ofFn_sum_const]
        calc
          2 * (n * (n ^ T *
              (if bankTrialDurationClass z = 2 then 1 else 0)) +
            (List.ofFn (fun e : Fin n =>
              Prob.scheduleSum n T
                (bankTrialDurationStageWord ring root 2
                  (bankTrialLocalNext ring root z e)))).sum) =
            n ^ T * (2 * n *
                (if bankTrialDurationClass z = 2 then 1 else 0)) +
            2 * (List.ofFn (fun e : Fin n =>
              Prob.scheduleSum n T
                (bankTrialDurationStageWord ring root 2
                  (bankTrialLocalNext ring root z e)))).sum := by
                  rw [Nat.mul_add]
                  ac_rfl
          _ ≤ n ^ T * (2 * n *
                (if bankTrialDurationClass z = 2 then 1 else 0)) +
            n ^ T * (List.ofFn (fun e : Fin n =>
              potential (bankTrialLocalNext ring root z e))).sum :=
              Nat.add_le_add_left hchildren _
          _ = n ^ T * (2 * n *
                (if bankTrialDurationClass z = 2 then 1 else 0) +
              (List.ofFn (fun e : Fin n =>
                potential (bankTrialLocalNext ring root z e))).sum) := by
                  rw [Nat.mul_add]
          _ ≤ n ^ T * (n * potential z) :=
              Nat.mul_le_mul_left _ (hdrift z hz ht)
          _ = n ^ (T + 1) * potential z := by
                  rw [Nat.pow_succ]
                  ac_rfl

def BankTrialDurationRecoveryOccupationCertificate {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ S : GrantBankReference.BankLocalReference
      (compileAdvice q).b,
    BankTrialLocalClean q S →
    ∃ potential : BankTrialLocalState q → Nat,
      potential (bankTrialLocalStart S) ≤
        8 * (compileAdvice q).b * n ∧
      ∀ z : BankTrialLocalState q,
        BankTrialDurationReachable ring root S z →
        ¬ bankTrialLocalTerminal z →
        2 * n *
            (if bankTrialDurationClass z = 2 then 1 else 0) +
          (List.ofFn (fun e : Fin n =>
            potential (bankTrialLocalNext ring root z e))).sum ≤
          n * potential z

theorem bankTrialDurationRecoveryBudgetOfOccupation
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hrows : BankTrialDurationRecoveryOccupationCertificate (q := q) ring root) :
    BankTrialDurationRecoveryBudget (q := q) ring root := by
  intro S hclean T
  obtain ⟨potential, hseed, hdrift⟩ := hrows S hclean
  have hreach :
      BankTrialDurationReachable ring root S
        (bankTrialLocalStart S) := ⟨[], rfl⟩
  have hcost := bankTrialDurationRecoveryTwiceChargedOfDrift
    ring root S potential hdrift T (bankTrialLocalStart S) hreach
  change 2 * bankTrialDurationStageMass ring root 2 S T ≤
    n ^ T * potential (bankTrialLocalStart S) at hcost
  have hcoeff :
      8 * (compileAdvice q).b * n ≤
        2 * ((2 * (2 * (compileAdvice q).b + 2) + 2) * n) := by
    have hscalar :
        8 * (compileAdvice q).b ≤
          2 * (2 * (2 * (compileAdvice q).b + 2) + 2) := by
      omega
    calc
      8 * (compileAdvice q).b * n ≤
        (2 * (2 * (2 * (compileAdvice q).b + 2) + 2)) * n :=
        Nat.mul_le_mul_right n hscalar
      _ = 2 * ((2 * (2 * (compileAdvice q).b + 2) + 2) * n) := by
        ac_rfl
  have htotal :
      2 * bankTrialDurationStageMass ring root 2 S T ≤
        2 * (n ^ T *
          ((2 * (2 * (compileAdvice q).b + 2) + 2) * n)) := by
    calc
      2 * bankTrialDurationStageMass ring root 2 S T ≤
        n ^ T * potential (bankTrialLocalStart S) := hcost
      _ ≤ n ^ T * (8 * (compileAdvice q).b * n) :=
        Nat.mul_le_mul_left _ hseed
      _ ≤ n ^ T *
          (2 * ((2 * (2 * (compileAdvice q).b + 2) + 2) * n)) :=
        Nat.mul_le_mul_left _ hcoeff
      _ = 2 * (n ^ T *
          ((2 * (2 * (compileAdvice q).b + 2) + 2) * n)) := by
        ac_rfl
  omega

theorem bankTrialDurationRecoveryTimeoutCredit
    (b r : Nat) (hb : 1 ≤ b) (hr : 1 ≤ r) :
    8 * b + 4 ≤ 4 * r + (13 * (b + 2) - 1) := by
  omega

theorem bankTrialDurationRecoveryLaunchCredit
    (b : Nat) (hb : 1 ≤ b) :
    4 * (2 * b - 1) + 4 = 8 * b := by
  omega

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- RESET has lease zero and arbitrary inherited digit scratch.
RWAIT has positive lease and a certified F/G front.  The F_j
suffix remains unrestricted, including inherited LIVE tokens. -/
def BankTrialDurationRecoveryFront (q : Nat)
    (z : BankTrialLocalState q) : Prop :=
  z.phase = .recovery ∧
  BankTrialLocalLeaseCap q z.bank ∧
  z.bank.success = false ∧
  (((z.bank.fields ⟨0, by omega⟩).1 = .RESET ∧
    (z.bank.fields ⟨0, by omega⟩).2.2.2 = 0) ∨
   ((z.bank.fields ⟨0, by omega⟩).1 = .RWAIT ∧
    1 ≤ (z.bank.fields ⟨0, by omega⟩).2.2.2 ∧
    ∃ stage : Counter.ResetClockStage,
      Counter.resetClockValid (compileAdvice q).b stage ∧
      (match stage with
       | .outward j => BankTrialLocalFrontOut q z.bank j
       | .returning j => BankTrialLocalFrontBack q z.bank j
       | .finished => False)))

/-- The measured state invariant strengthens the existing
certificate only by requiring RESET lease = 0. -/
theorem bankTrialDurationRecoveryFrontCert {q : Nat}
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z) :
    BankTrialLocalRecoveryCert q z.bank := by
  refine ⟨hf.2.1, hf.2.2.1, ?_⟩
  rcases hf.2.2.2 with hr | hw
  · exact Or.inl hr.1
  · rcases hw with ⟨hm, hp, stage, _, hstage⟩
    refine Or.inr ⟨hm, hp, hf.2.1 0 (by omega), ?_⟩
    cases stage with
    | outward j => exact Or.inl ⟨j, hstage⟩
    | returning j => exact Or.inr ⟨j, hstage⟩
    | finished => exact False.elim hstage

/-- A choice of the authenticated front, not a search over
the full Cartesian BANK alphabet. -/
noncomputable def bankTrialDurationRecoveryReadStage {q : Nat}
    (z : BankTrialLocalState q) :
    Option Counter.ResetClockStage := by
  classical
  exact
    if ho : ∃ j : Nat, BankTrialLocalFrontOut q z.bank j then
      some (.outward (Classical.choose ho))
    else if hb : ∃ j : Nat, BankTrialLocalFrontBack q z.bank j then
      some (.returning (Classical.choose hb))
    else none

noncomputable def bankTrialDurationRecoveryReadRank {q : Nat}
    (z : BankTrialLocalState q) : Nat :=
  match bankTrialDurationRecoveryReadStage z with
  | none => 0
  | some s => Counter.resetClockRank (compileAdvice q).b s

def bankTrialDurationRecoveryReadLease {q : Nat}
    (z : BankTrialLocalState q) : Nat :=
  (z.bank.fields ⟨0, by omega⟩).2.2.2

noncomputable def bankTrialDurationRecoveryNominated {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q) : Fin n :=
  match bankTrialDurationRecoveryReadStage z with
  | none => root
  | some stage =>
      Counter.resetClockNominated ring root (compileAdvice q).b stage

/-- The three abstract classes: RESET, an active rank/lease
front, and a terminal local observer. -/
inductive BankTrialDurationRecoveryClock where
  | reset
  | waiting (rank lease : Nat)
  | done
  deriving DecidableEq

noncomputable def bankTrialDurationRecoveryClockOf {q : Nat}
    (z : BankTrialLocalState q) :
    BankTrialDurationRecoveryClock := by
  classical
  exact
    if bankTrialLocalTerminal z then .done
    else if bankTrialLiveWaveRootMode z.bank = .RESET then .reset
    else if bankTrialLiveWaveRootMode z.bank = .RWAIT then
      .waiting (bankTrialDurationRecoveryReadRank z)
        (bankTrialDurationRecoveryReadLease z)
    else .done

/-- The scheduler letter is the same Fin n letter as the local
observer. The nominated edge is supplied by the read-off stage.
The three distinguished edges are assumed distinct for a
nonfinal front when the row theorem is discharged. -/
def bankTrialDurationRecoveryClockNext {n : Nat}
    (b : Nat) (root incoming chosen e : Fin n) :
    BankTrialDurationRecoveryClock →
      BankTrialDurationRecoveryClock
  | .done => .done
  | .reset =>
      if e = root then .waiting (2 * b - 1) (13 * (b + 2))
      else .reset
  | .waiting rank lease =>
      if rank = 1 ∧ e = root then .done
      else if e = chosen then .waiting (rank - 1) lease
      else if e = root ∨ e = incoming then
        if lease ≤ 1 then .reset
        else .waiting rank (lease - 1)
      else .waiting rank lease

/-- The remaining original-local row obligation. It includes
a genuine terminal-or-front closure and exact same-letter
clock projection, not a physical Counter simulation. -/
def BankTrialDurationRecoveryAllRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (z : BankTrialLocalState q) (e : Fin n),
    BankTrialDurationRecoveryFront q z →
      (bankTrialLocalTerminal (bankTrialLocalNext ring root z e) ∨
        BankTrialDurationRecoveryFront q
          (bankTrialLocalNext ring root z e)) ∧
      bankTrialDurationRecoveryClockOf
          (bankTrialLocalNext ring root z e) =
        bankTrialDurationRecoveryClockNext
          (compileAdvice q).b root
          (Counter.site ring root (n - 1))
          (bankTrialDurationRecoveryNominated ring root z)
          e (bankTrialDurationRecoveryClockOf z)

/-- Source-level service class: a certified front cannot set
the OLD CWAIT-only BANK success latch. -/
theorem bankTrialDurationRecoveryFrontNoWin {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root z.bank e).success = false := by
  exact bankTrialLocalRecoveryCertNoWin ring root e z.bank
    (bankTrialDurationRecoveryFrontCert z hf)

/-- Source-level RESET outgoing service produces a certified
new reset attempt, even with arbitrary inherited digit scratch.
The rank/lease equations are still part of AllRows. -/
theorem bankTrialDurationRecoveryResetLaunchCert {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n) (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hr : bankTrialLiveWaveRootMode z.bank = .RESET) :
    BankTrialLocalRecoveryCert q
      (bankTrialLocalNext ring root z root).bank := by
  have hc := bankTrialDurationRecoveryFrontCert z hf
  cases z with
  | mk B phase =>
      cases hf.1
      rw [bankTrialLocalNextRecoveryBank ring root root B]
      exact bankTrialLocalRecoveryCertLaunch
        ring root hn B hc.1 hc.2.1 hr

/-- Source-level outside-support service, not merely a clock
abstraction: the complete local observer state is unchanged. -/
theorem bankTrialDurationRecoveryOutside {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hout : ¬ Counter.Support q ring root e) :
    bankTrialLocalNext ring root z e = z := by
  cases z with
  | mk B phase =>
      obtain ⟨hphase, _, hfalse, hcases⟩ := hf
      cases hphase
      have hnotarmed :
          (B.fields ⟨0, by omega⟩).1 ≠ .ARMED := by
        intro h
        rcases hcases with hr | hw
        · rw [hr.1] at h
          cases h
        · rw [hw.1] at h
          cases h
      have hnotclean : ¬ BankTrialLocalClean q B := by
        intro hc
        exact hnotarmed hc.2.1
      have hfalse' : B.success = false := hfalse
      simp [bankTrialLocalNext,
        bankTrialLocalStepOutside ring root e B hout,
        hfalse', hnotclean]

/-! The following is a COMPLETE, independent pure-Nat
Bellman proof for the COUNTED reset/front clock. No stochastic
lemma, large power, or physical protocol theorem is used. -/

/-- The scalar reserve. Nat subtraction truncates at zero:
3*r-1 + max(0, 6*b-8-lease). -/
def bankTrialDurationClockScalar
    (b rank lease : Nat) : Nat :=
  (3 * rank - 1) + (6 * b - 8 - lease)

/-- The candidate with a linear budget: (6b-3)n at RESET.
A RWAIT potential may exceed that entry budget near expiry;
only the RESET entry is charged at the fixed coefficient. -/
def bankTrialDurationClockPotential (b n : Nat) :
    BankTrialDurationRecoveryClock → Nat
  | .reset => n * (6 * b - 3)
  | .waiting rank lease =>
      n * bankTrialDurationClockScalar b rank lease
  | .done => 0

def bankTrialDurationClockLeaseNext (rank lease : Nat) :
    BankTrialDurationRecoveryClock :=
  if lease = 1 then .reset else .waiting rank (lease - 1)

/-- Exactly the n successor-value slots of the ABSTRACT
counted rule. Distinct nominated/incoming/outgoing ports are
to be established by AllRows when lifted to the local model. -/
def bankTrialDurationClockRowSum (b n : Nat) :
    BankTrialDurationRecoveryClock → Nat
  | .reset =>
      (n - 1) * bankTrialDurationClockPotential b n .reset +
      bankTrialDurationClockPotential b n
        (.waiting (2 * b - 1) (13 * (b + 2)))
  | .waiting rank lease =>
      if rank = 1 then
        (n - 2) * bankTrialDurationClockPotential b n
          (.waiting rank lease) +
        bankTrialDurationClockPotential b n .done +
        bankTrialDurationClockPotential b n
          (bankTrialDurationClockLeaseNext rank lease)
      else
        (n - 3) * bankTrialDurationClockPotential b n
          (.waiting rank lease) +
        bankTrialDurationClockPotential b n
          (.waiting (rank - 1) lease) +
        2 * bankTrialDurationClockPotential b n
          (bankTrialDurationClockLeaseNext rank lease)
  | .done => 0

private theorem bankTrialDurationScaleOne
    (n A B : Nat) (hn : 1 ≤ n)
    (h : 1 + B ≤ A) :
    n + ((n - 1) * (n * A) + n * B) ≤ n * (n * A) := by
  have hbound : (n - 1) * A + (1 + B) ≤ n * A := by
    calc
      (n - 1) * A + (1 + B) ≤
          (n - 1) * A + A := Nat.add_le_add_left h _
      _ = n * A := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
  have hscaled := Nat.mul_le_mul_left n hbound
  calc
    n + ((n - 1) * (n * A) + n * B) =
        n * ((n - 1) * A + (1 + B)) := by
          simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
          ac_rfl
    _ ≤ n * (n * A) := hscaled

private theorem bankTrialDurationScaleTwo
    (n A B : Nat) (hn : 2 ≤ n)
    (h : 1 + B ≤ 2 * A) :
    n + ((n - 2) * (n * A) + n * B) ≤ n * (n * A) := by
  have hbound : (n - 2) * A + (1 + B) ≤ n * A := by
    calc
      (n - 2) * A + (1 + B) ≤
          (n - 2) * A + 2 * A := Nat.add_le_add_left h _
      _ = n * A := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hn]
  have hscaled := Nat.mul_le_mul_left n hbound
  calc
    n + ((n - 2) * (n * A) + n * B) =
        n * ((n - 2) * A + (1 + B)) := by
          simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
          ac_rfl
    _ ≤ n * (n * A) := hscaled

private theorem bankTrialDurationScaleThree
    (n A B C : Nat) (hn : 3 ≤ n)
    (h : 1 + B + 2 * C ≤ 3 * A) :
    n + ((n - 3) * (n * A) + n * B + 2 * (n * C)) ≤
      n * (n * A) := by
  have hbound :
      (n - 3) * A + (1 + B + 2 * C) ≤ n * A := by
    calc
      (n - 3) * A + (1 + B + 2 * C) ≤
          (n - 3) * A + 3 * A := Nat.add_le_add_left h _
      _ = n * A := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hn]
  have hscaled := Nat.mul_le_mul_left n hbound
  calc
    n + ((n - 3) * (n * A) + n * B + 2 * (n * C)) =
        n * ((n - 3) * A + (1 + B + 2 * C)) := by
          simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
          ac_rfl
    _ ≤ n * (n * A) := hscaled

/-- A fresh full-lease F_1 costs one root service from RESET
in the potential budget. -/
theorem bankTrialDurationClockResetScalar (b : Nat)
    (hb : 2 ≤ b) :
    1 + bankTrialDurationClockScalar b
      (2 * b - 1) (13 * (b + 2)) ≤ 6 * b - 3 := by
  unfold bankTrialDurationClockScalar
  omega

/-- Nonfinal front, positive remaining lease after a root tick. -/
theorem bankTrialDurationClockInteriorScalar
    (b rank lease : Nat) (hb : 2 ≤ b)
    (hr : 2 ≤ rank) (hl : 2 ≤ lease) :
    1 + bankTrialDurationClockScalar b (rank - 1) lease +
      2 * bankTrialDurationClockScalar b rank (lease - 1) ≤
    3 * bankTrialDurationClockScalar b rank lease := by
  unfold bankTrialDurationClockScalar
  omega

/-- Two root-incident expiry edges at lease one, and one
distinct nominated productive edge. -/
theorem bankTrialDurationClockTimeoutScalar
    (b rank : Nat) (hb : 2 ≤ b) (hr : 2 ≤ rank) :
    1 + bankTrialDurationClockScalar b (rank - 1) 1 +
      2 * (6 * b - 3) ≤
    3 * bankTrialDurationClockScalar b rank 1 := by
  unfold bankTrialDurationClockScalar
  omega

/-- At final rank only one root edge is unproductive. -/
theorem bankTrialDurationClockReturnScalar
    (b lease : Nat) (hb : 2 ≤ b) (hl : 2 ≤ lease) :
    1 + bankTrialDurationClockScalar b 1 (lease - 1) ≤
      2 * bankTrialDurationClockScalar b 1 lease := by
  unfold bankTrialDurationClockScalar
  omega

/-- Terminal root service dominates a lease-one timeout. -/
theorem bankTrialDurationClockReturnTimeoutScalar
    (b : Nat) (hb : 2 ≤ b) :
    1 + (6 * b - 3) ≤
      2 * bankTrialDurationClockScalar b 1 1 := by
  unfold bankTrialDurationClockScalar
  omega

/-- COMPLETE arithmetic Bellman drift for the four counted
edge classes on the abstract reset/rank/lease chain, valid
uniformly in the ring size n >= 3 and all positive rank/lease. -/
theorem bankTrialDurationClockBellman
    (b n : Nat) (hb : 2 ≤ b) (hn : 3 ≤ n)
    (s : BankTrialDurationRecoveryClock)
    (hs : s = .reset ∨
      ∃ rank lease : Nat,
        s = .waiting rank lease ∧
        1 ≤ rank ∧ 1 ≤ lease) :
    n + bankTrialDurationClockRowSum b n s ≤
      n * bankTrialDurationClockPotential b n s := by
  rcases hs with hreset | ⟨rank, lease, heq, hr, hl⟩
  · subst s
    have h := bankTrialDurationScaleOne n (6 * b - 3)
      (bankTrialDurationClockScalar b
        (2 * b - 1) (13 * (b + 2)))
      (by omega) (bankTrialDurationClockResetScalar b hb)
    simpa only [bankTrialDurationClockRowSum,
      bankTrialDurationClockPotential] using h
  · subst s
    by_cases hone : rank = 1
    · subst rank
      by_cases hlease : lease = 1
      · subst lease
        have h := bankTrialDurationScaleTwo n
          (bankTrialDurationClockScalar b 1 1)
          (6 * b - 3) (by omega)
          (bankTrialDurationClockReturnTimeoutScalar b hb)
        simpa only [bankTrialDurationClockRowSum,
          if_pos rfl, bankTrialDurationClockLeaseNext, ↓reduceIte,
          bankTrialDurationClockPotential, Nat.add_zero] using h
      · have hmore : 2 ≤ lease := by omega
        have h := bankTrialDurationScaleTwo n
          (bankTrialDurationClockScalar b 1 lease)
          (bankTrialDurationClockScalar b 1 (lease - 1))
          (by omega)
          (bankTrialDurationClockReturnScalar b lease hb hmore)
        simpa only [bankTrialDurationClockRowSum,
          if_pos rfl, bankTrialDurationClockLeaseNext,
          if_neg hlease, bankTrialDurationClockPotential, ↓reduceIte,
          Nat.add_zero] using h
    · have hrmore : 2 ≤ rank := by omega
      by_cases hlease : lease = 1
      · subst lease
        have h := bankTrialDurationScaleThree n
          (bankTrialDurationClockScalar b rank 1)
          (bankTrialDurationClockScalar b (rank - 1) 1)
          (6 * b - 3) hn
          (bankTrialDurationClockTimeoutScalar b rank hb hrmore)
        simpa only [bankTrialDurationClockRowSum,
          if_neg hone, bankTrialDurationClockLeaseNext,
          if_pos rfl, bankTrialDurationClockPotential, ↓reduceIte] using h
      · have hmore : 2 ≤ lease := by omega
        have h := bankTrialDurationScaleThree n
          (bankTrialDurationClockScalar b rank lease)
          (bankTrialDurationClockScalar b (rank - 1) lease)
          (bankTrialDurationClockScalar b rank (lease - 1))
          hn
          (bankTrialDurationClockInteriorScalar
            b rank lease hb hrmore hmore)
        simpa only [bankTrialDurationClockRowSum,
          if_neg hone, bankTrialDurationClockLeaseNext,
          if_neg hlease, bankTrialDurationClockPotential] using h

/-- Every genuine LIVE->RECOVERY entry is RESET.  Under
the front invariant its potential is exactly (6b-3)n. -/
theorem bankTrialDurationClockEntryAllowance
    (b n : Nat) :
    bankTrialDurationClockPotential b n .reset =
      (6 * b - 3) * n := by
  simp only [bankTrialDurationClockPotential, Nat.mul_comm]

end L3

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Away from root, incoming, and nominated edges the abstract
counted recovery clock is unchanged. -/
theorem bankTrialDurationRecoveryClockNextAway {n : Nat}
    (b : Nat) (root incoming chosen e : Fin n)
    (hr : e ≠ root) (hi : e ≠ incoming)
    (hc : e ≠ chosen) (s : BankTrialDurationRecoveryClock) :
    bankTrialDurationRecoveryClockNext b root incoming chosen e s = s := by
  cases s with
  | done => rfl
  | reset =>
      simp [bankTrialDurationRecoveryClockNext, hr]
  | waiting rank lease =>
      simp [bankTrialDurationRecoveryClockNext, hr, hi, hc]

/-- Outside Support, the full physical observer stutters, so the
authenticated recovery front and its read-off clock both stutter.
This does not yet identify the physical incoming label n-1 with
the corresponding edge test in the abstract clock. -/
theorem bankTrialDurationRecoveryOutsideFrontRow {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hout : ¬ Counter.Support q ring root e) :
    (bankTrialLocalTerminal
        (bankTrialLocalNext ring root z e) ∨
      BankTrialDurationRecoveryFront q
        (bankTrialLocalNext ring root z e)) ∧
    bankTrialDurationRecoveryClockOf
      (bankTrialLocalNext ring root z e) =
      bankTrialDurationRecoveryClockOf z := by
  have hframe := bankTrialDurationRecoveryOutside
    ring root e z hf hout
  rw [hframe]
  exact ⟨Or.inr hf, rfl⟩

/-- Root outgoing at the authenticated G_1 return: the physical
RECOVERY observer is LOST, not a new recovery epoch. -/
theorem bankTrialDurationRecoveryRootReturnTerminal {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (hn : 2 ≤ n)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RWAIT)
    (hback : BankTrialLocalFrontBack q z.bank 1) :
    bankTrialLocalTerminal
      (bankTrialLocalNext ring root z root) := by
  have hc := bankTrialDurationRecoveryFrontCert z hf
  cases z with
  | mk B phase =>
      cases hf.1
      have hnext := bankTrialLocalRecoveryGOneLoss
        ring root hn B hc hm hback
      rw [hnext]
      exact Or.inr rfl

/-- A certified RESET snapshot with zero lease is exactly the
RESET arm of the strengthened front invariant.  The remaining
entry obligation is proving zero lease on every first LIVE-to-
RECOVERY event, not merely the RESET mode-band. -/
theorem bankTrialDurationRecoveryResetFrontOfCert {q : Nat}
    (z : BankTrialLocalState q)
    (hphase : z.phase = .recovery)
    (hc : BankTrialLocalRecoveryCert q z.bank)
    (hm : bankTrialLiveWaveRootMode z.bank = .RESET)
    (hlease :
      (z.bank.fields ⟨0, by omega⟩).2.2.2 = 0) :
    BankTrialDurationRecoveryFront q z := by
  exact ⟨hphase, hc.1, hc.2.1, Or.inl ⟨hm, hlease⟩⟩

/-- Incoming-root RWAIT scalar row on the actual clamped BANK
reference.  Both decrement and timeout have exact root-field
equalities; inherited suffix digits are not assumed empty. -/
theorem bankTrialDurationRecoveryIncomingRootScalar {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (hc : BankTrialLocalLeaseCap q B)
    (hin : ring.rightNeighbor e = root) :
    ((1 < (B.fields ⟨0, by omega⟩).2.2.2 ∧
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨0, by omega⟩).1 = .RWAIT ∧
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨0, by omega⟩).2.2.2 =
        (B.fields ⟨0, by omega⟩).2.2.2 - 1) ∨
     ((B.fields ⟨0, by omega⟩).2.2.2 ≤ 1 ∧
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨0, by omega⟩).1 = .RESET ∧
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨0, by omega⟩).2.2.2 = 0)) := by
  have hfields := bankTrialDurationIncomingFieldsRow
    ring root e hw hin B hf
  have hraw := bankTrialLocalIncomingWaitRow q
    (GrantBankReference.bankLocalReferenceCell B
      ⟨0, by omega⟩) hm (hc 0 (by omega))
  by_cases hl : 1 < (B.fields ⟨0, by omega⟩).2.2.2
  · refine Or.inl ⟨hl, ?_, ?_⟩
    · rw [hfields]
      first | exact (hraw.1 hl).1 | (simp only [Fin.val_mk, ↓reduceIte]; exact (hraw.1 hl).1)
    · rw [hfields]
      first | exact (hraw.1 hl).2 | (simp only [Fin.val_mk, ↓reduceIte]; exact (hraw.1 hl).2)
  · have hle : (B.fields ⟨0, by omega⟩).2.2.2 ≤ 1 := by
      omega
    refine Or.inr ⟨hle, ?_, ?_⟩
    · rw [hfields]
      first | exact (hraw.2 hle).1 | (simp only [Fin.val_mk, ↓reduceIte]; exact (hraw.2 hle).1)
    · rw [hfields]
      first | exact (hraw.2 hle).2 | (simp only [Fin.val_mk, ↓reduceIte]; exact (hraw.2 hle).2)

/-- Nominated F_b top turn at source b-1: the real BANK pair
turns RR into RL, and the reset-front clock loses one rank. -/
theorem bankTrialDurationRecoveryNominatedTopTurn
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 2 ≤ b)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htop : y.role = b)
    (hsrc : x.tok = .E) (hdst : y.tok = .RR)
    (hbit : y.bit = false) :
    (bankPair x y y.role b theta).1.tok = .RL ∧
    (bankPair x y y.role b theta).2.tok = .E ∧
    Counter.resetClockRank b (.returning (b - 1)) + 1 =
      Counter.resetClockRank b (.outward b) := by
  have hr := bankTrialLocalRawTopTurn
    b theta x y hx hlt hy htop hsrc hdst hbit
  refine ⟨hr.1, hr.2.2.1, ?_⟩
  change b - 1 + 1 = 2 * b - b
  omega

/-- A selected ordinary interior E/E pair remains bit-zero and
empty on BOTH selected clamped reference fields. -/
theorem bankTrialDurationRecoveryInteriorEmptyPair {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrcBit : (B.fields ⟨j.val, by omega⟩).2.1 = false)
    (hsrcTok : (B.fields ⟨j.val, by omega⟩).2.2.1 = .E)
    (hdstBit : (B.fields ⟨j.val + 1, by omega⟩).2.1 = false)
    (hdstTok : (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .E) :
    (((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val, by omega⟩).2.1 = false ∧
     ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val, by omega⟩).2.2.1 = .E) ∧
    (((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val + 1, by omega⟩).2.1 = false ∧
     ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val + 1, by omega⟩).2.2.1 = .E) := by
  have hraw := bankTrialLocalRawEmptyHold
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by omega⟩)
    (by change 1 ≤ j.val; omega) j.isLt (by rfl)
    hsrcTok hdstTok hsrcBit hdstBit
  have hsource := bankTrialWindowInteriorSource ring root B hf j
  have htarget := bankTrialWindowInteriorResponder ring root hw B hf j
  have hcl := bankTrialLocalClampedData q
    ((GrantBankReference.bankLocalReferenceInternalPair q B j).1)
  have hcr := bankTrialLocalClampedData q
    ((GrantBankReference.bankLocalReferenceInternalPair q B j).2)
  constructor
  · constructor
    · rw [hsource]
      exact hcl.1.trans hraw.2.1
    · rw [hsource]
      exact hcl.2.trans hraw.1
  · constructor
    · rw [htarget]
      exact hcr.1.trans hraw.2.2.2
    · rw [htarget]
      exact hcr.2.trans hraw.2.2.1

/-- Top-source unary source row, including inherited suffix RR/RL
tokens: only IR is erased, other tokens and bits are frames. -/
theorem bankTrialDurationRecoveryTopSourceData {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hnotIR :
      (B.fields ⟨(compileAdvice q).b, by omega⟩).2.2.1 ≠ .IR) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root (compileAdvice q).b)).fields
        ⟨(compileAdvice q).b, by omega⟩).2.1 =
      (B.fields ⟨(compileAdvice q).b, by omega⟩).2.1 ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root (compileAdvice q).b)).fields
        ⟨(compileAdvice q).b, by omega⟩).2.2.1 =
      (B.fields ⟨(compileAdvice q).b, by omega⟩).2.2.1 := by
  have hfields := bankTrialDurationTopFieldsRow ring root hw B hf
  have hraw := bankTrialLocalTopDataRow q
    (GrantBankReference.bankLocalReferenceCell B
      ⟨(compileAdvice q).b, by omega⟩) hnotIR
  constructor
  · rw [hfields]
    first | exact hraw.1 | (simp only [Fin.val_mk, ↓reduceIte]; exact hraw.1)
  · rw [hfields]
    first | exact hraw.2 | (simp only [Fin.val_mk, ↓reduceIte]; exact hraw.2)

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

private theorem bankTrialDurationRecoveryWidthLarge (q : Nat) :
    1 < (compileAdvice q).b := by
  change 1 < (compileAdvice q).s + 11
  omega

/-- The unrestricted suffix of F_j does not introduce a second
outward front: its first RR is unique. -/
private theorem bankTrialDurationRecoveryOutUnique {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (j k : Nat)
    (hj : BankTrialLocalFrontOut q B j)
    (hk : BankTrialLocalFrontOut q B k) : j = k := by
  obtain ⟨hjb, hjpos, _, hjtok, hjprefix⟩ := hj
  obtain ⟨hkb, hkpos, _, hktok, hkprefix⟩ := hk
  by_cases hlt : j < k
  · have he := (hkprefix j hjpos hlt hjb).2
    rw [hjtok] at he
    cases he
  · by_cases hgt : k < j
    · have he := (hjprefix k hkpos hgt hkb).2
      rw [hktok] at he
      cases he
    · omega

/-- A G_j certificate has exactly one RL location. -/
private theorem bankTrialDurationRecoveryBackUnique {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (j k : Nat)
    (hj : BankTrialLocalFrontBack q B j)
    (hk : BankTrialLocalFrontBack q B k) : j = k := by
  obtain ⟨_, _, _, hjtok, hjother⟩ := hj
  obtain ⟨hkb, hkpos, _, hktok, _⟩ := hk
  by_cases heq : j = k
  · exact heq
  · have he := (hjother k hkpos hkb (Ne.symm heq)).2
    rw [hktok] at he
    cases he

/-- No array simultaneously carries an F and a G certificate. -/
private theorem bankTrialDurationRecoveryOutBackDisjoint {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (j k : Nat)
    (hj : BankTrialLocalFrontOut q B j)
    (hk : BankTrialLocalFrontBack q B k) : False := by
  obtain ⟨hjb, hjpos, _, hjtok, _⟩ := hj
  obtain ⟨_, _, _, hktok, hkother⟩ := hk
  by_cases heq : j = k
  · subst j
    rw [hktok] at hjtok
    cases hjtok
  · have he := (hkother j hjpos hjb heq).2
    rw [hjtok] at he
    cases he

/-- The choice-based reader nevertheless selects the literal F_j. -/
theorem bankTrialDurationRecoveryReadStageOut {q : Nat}
    (z : BankTrialLocalState q) (j : Nat)
    (hj : BankTrialLocalFrontOut q z.bank j) :
    bankTrialDurationRecoveryReadStage z = some (.outward j) := by
  classical
  unfold bankTrialDurationRecoveryReadStage
  split
  · rename_i hex
    have hh := Classical.choose_spec hex
    have heq :=
      bankTrialDurationRecoveryOutUnique z.bank
        (Classical.choose hex) j hh hj
    rw [heq]
  · rename_i hn
    exact False.elim (hn ⟨j, hj⟩)

/-- The reader selects G_j exactly when no outward front exists. -/
theorem bankTrialDurationRecoveryReadStageBack {q : Nat}
    (z : BankTrialLocalState q) (j : Nat)
    (hj : BankTrialLocalFrontBack q z.bank j) :
    bankTrialDurationRecoveryReadStage z = some (.returning j) := by
  classical
  unfold bankTrialDurationRecoveryReadStage
  split
  · rename_i hex
    exact False.elim
      (bankTrialDurationRecoveryOutBackDisjoint
        z.bank (Classical.choose hex) j
        (Classical.choose_spec hex) hj)
  · split
    · rename_i hex
      have hh := Classical.choose_spec hex
      have heq :=
        bankTrialDurationRecoveryBackUnique z.bank
          (Classical.choose hex) j hh hj
      rw [heq]
    · rename_i hn
      exact False.elim (hn ⟨j, hj⟩)

theorem bankTrialDurationRecoveryReadRankOut {q : Nat}
    (z : BankTrialLocalState q) (j : Nat)
    (hj : BankTrialLocalFrontOut q z.bank j) :
    bankTrialDurationRecoveryReadRank z =
      Counter.resetClockRank (compileAdvice q).b (.outward j) := by
  unfold bankTrialDurationRecoveryReadRank
  rw [bankTrialDurationRecoveryReadStageOut z j hj]

theorem bankTrialDurationRecoveryReadRankBack {q : Nat}
    (z : BankTrialLocalState q) (j : Nat)
    (hj : BankTrialLocalFrontBack q z.bank j) :
    bankTrialDurationRecoveryReadRank z =
      Counter.resetClockRank (compileAdvice q).b (.returning j) := by
  unfold bankTrialDurationRecoveryReadRank
  rw [bankTrialDurationRecoveryReadStageBack z j hj]

private theorem bankTrialDurationRecoveryFrontNotTerminal {q : Nat}
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z) :
    ¬ bankTrialLocalTerminal z := by
  intro ht
  rcases ht with hw | hl
  · rw [hf.1] at hw
    cases hw
  · rw [hf.1] at hl
    cases hl

theorem bankTrialDurationRecoveryClockResetOfFront {q : Nat}
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RESET) :
    bankTrialDurationRecoveryClockOf z = .reset := by
  classical
  simp [bankTrialDurationRecoveryClockOf,
    bankTrialDurationRecoveryFrontNotTerminal z hf, hm]

theorem bankTrialDurationRecoveryClockWaitOfFront {q : Nat}
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RWAIT) :
    bankTrialDurationRecoveryClockOf z =
      .waiting (bankTrialDurationRecoveryReadRank z)
        (bankTrialDurationRecoveryReadLease z) := by
  classical
  simp [bankTrialDurationRecoveryClockOf,
    bankTrialDurationRecoveryFrontNotTerminal z hf, hm]

private theorem bankTrialDurationRecoveryNoCleanAtBand {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RESET ∨
      (B.fields ⟨0, by omega⟩).1 = .RWAIT) :
    ¬ BankTrialLocalClean q B := by
  intro hc
  rcases hm with hr | hw
  · rw [hc.2.1] at hr
    cases hr
  · rw [hc.2.1] at hw
    cases hw

private theorem bankTrialDurationRecoveryNextPhaseAtBand {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hfalse : (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).success = false)
    (hm :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨0, by omega⟩).1 = .RESET ∨
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨0, by omega⟩).1 = .RWAIT) :
    (bankTrialLocalNext ring root
      (⟨B, .recovery⟩ : BankTrialLocalState q) e).phase =
      .recovery := by
  classical
  have hnot := bankTrialDurationRecoveryNoCleanAtBand
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e) hm
  simp [bankTrialLocalNext, hfalse, hnot]

private theorem bankTrialDurationRecoveryWaitLeasePositive {q : Nat}
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RWAIT) :
    1 ≤ bankTrialDurationRecoveryReadLease z := by
  rcases hf.2.2.2 with hr | hw
  · cases (hm.symm.trans hr.1)
  · exact hw.2.1

/-- RESET root-outgoing: literal mode, full launch lease,
and first RR digit, including inherited scratch. -/
theorem bankTrialDurationRecoveryResetOutgoingFields {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RESET) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B root).fields ⟨0, by omega⟩).1 = .RWAIT ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B root).fields ⟨0, by omega⟩).2.2.2 =
        (compileAdvice q).bankLeaseCap ∧
    BankTrialLocalFrontOut q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root) 1 := by
  have hn : 2 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    omega
  have hb : 1 ≤ (compileAdvice q).b :=
    Nat.le_of_lt (bankTrialDurationRecoveryWidthLarge q)
  have hs : Counter.Support q ring root root :=
    Or.inr ⟨0, Nat.zero_le _, rfl⟩
  have hrow := bankTrialLocalRawRootLaunch
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B ⟨0, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩)
    hb rfl rfl rfl hm
  have hmode :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B root).fields ⟨0, by omega⟩).1 = .RWAIT := by
    rw [bankTrialLocalStepField ring root root B hs hf,
      bankTrialLocalFieldRootOutgoing ring root B]
    change (GrantBankReference.bankLocalReferenceInternalPair q B
      ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).1.mode = .RWAIT
    exact hrow.1
  have hrawLease :
      (GrantBankReference.bankLocalReferenceInternalPair q B
        ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).1.lease =
        (compileAdvice q).bankLeaseCap := by
    exact hrow.2.1
  have hlease :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B root).fields ⟨0, by omega⟩).2.2.2 =
        (compileAdvice q).bankLeaseCap := by
    rw [bankTrialLocalStepField ring root root B hs hf,
      bankTrialLocalFieldRootOutgoing ring root B]
    exact (bankTrialLocalClampedLease q
      ((GrantBankReference.bankLocalReferenceInternalPair q B
        ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).1)
      (by omega)).trans hrawLease
  have hbit :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B root).fields
        ⟨1, Nat.lt_succ_of_le hb⟩).2.1 = false := by
    rw [bankTrialLocalStepField ring root root B hs hf,
      bankTrialLocalFieldOneOutgoing ring root hn B]
    change (GrantBankReference.bankLocalReferenceInternalPair q B
      ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).2.bit = false
    exact hrow.2.2.1
  have htok :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B root).fields
        ⟨1, Nat.lt_succ_of_le hb⟩).2.2.1 = .RR := by
    rw [bankTrialLocalStepField ring root root B hs hf,
      bankTrialLocalFieldOneOutgoing ring root hn B]
    change (GrantBankReference.bankLocalReferenceInternalPair q B
      ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).2.tok = .RR
    exact hrow.2.2.2
  refine ⟨hmode, hlease, ⟨hb, Nat.le_refl _, hbit, htok, ?_⟩⟩
  intro i hi hij hib
  omega

/-- Class (1): full RESET root-outgoing front, not just a
certificate for the underlying BANK successor. -/
theorem bankTrialDurationRecoveryResetOutgoingFront {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RESET) :
    BankTrialDurationRecoveryFront q
      (bankTrialLocalNext ring root z root) := by
  cases z with
  | mk B phase =>
      cases hf.1
      have hfields := bankTrialDurationRecoveryResetOutgoingFields
        ring root hw B hf.2.2.1 hm
      have hfalseStep := bankTrialDurationRecoveryFrontNoWin
        ring root root (⟨B, .recovery⟩ : BankTrialLocalState q) hf
      have hphase := bankTrialDurationRecoveryNextPhaseAtBand
        ring root root B hfalseStep (Or.inr hfields.1)
      have hcap := bankTrialLocalLeaseCapNext
        ring root root (⟨B, .recovery⟩ : BankTrialLocalState q)
        hf.2.1
      have hfalse :
          (bankTrialLocalNext ring root
            (⟨B, .recovery⟩ : BankTrialLocalState q) root).bank.success =
              false := by
        rw [bankTrialLocalNextRecoveryBank]
        exact hfalseStep
      have hmode :
          bankTrialLiveWaveRootMode
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q) root).bank =
            .RWAIT := by
        rw [bankTrialLocalNextRecoveryBank]
        exact hfields.1
      have hlease :
          ((bankTrialLocalNext ring root
            (⟨B, .recovery⟩ : BankTrialLocalState q) root).bank.fields
            ⟨0, by omega⟩).2.2.2 = (compileAdvice q).bankLeaseCap := by
        rw [bankTrialLocalNextRecoveryBank]
        exact hfields.2.1
      have hpositive :
          1 ≤ ((bankTrialLocalNext ring root
            (⟨B, .recovery⟩ : BankTrialLocalState q) root).bank.fields
            ⟨0, by omega⟩).2.2.2 := by
        rw [hlease]
        change 1 ≤ 13 * ((compileAdvice q).b + 2)
        omega
      have hfront :
          BankTrialLocalFrontOut q
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q) root).bank 1 := by
        rw [bankTrialLocalNextRecoveryBank]
        exact hfields.2.2
      have hv :
          Counter.resetClockValid (compileAdvice q).b
            (.outward 1) := by
        change 1 ≤ (1 : Nat) ∧ 1 ≤ (compileAdvice q).b
        exact ⟨Nat.le_refl _, Nat.le_of_lt (bankTrialDurationRecoveryWidthLarge q)⟩
      exact ⟨hphase, hcap, hfalse,
        Or.inr ⟨hmode, hpositive, .outward 1, hv, hfront⟩⟩

/-- Class (1), exact observer/clock RESET row on the original
root service, including inherited arbitrary digit scratch. -/
theorem bankTrialDurationRecoveryResetOutgoingRow {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RESET) :
    (bankTrialLocalTerminal (bankTrialLocalNext ring root z root) ∨
      BankTrialDurationRecoveryFront q
        (bankTrialLocalNext ring root z root)) ∧
    bankTrialDurationRecoveryClockOf
      (bankTrialLocalNext ring root z root) =
      bankTrialDurationRecoveryClockNext
        (compileAdvice q).b root
        (Counter.site ring root (n - 1))
        (bankTrialDurationRecoveryNominated ring root z)
        root (bankTrialDurationRecoveryClockOf z) := by
  cases z with
  | mk B phase =>
      cases hf.1
      have hfields := bankTrialDurationRecoveryResetOutgoingFields
        ring root hw B hf.2.2.1 hm
      have hfrontNext := bankTrialDurationRecoveryResetOutgoingFront
        ring root hw
        (⟨B, .recovery⟩ : BankTrialLocalState q) hf hm
      have hmode :
          bankTrialLiveWaveRootMode
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q) root).bank =
              .RWAIT := by
        rw [bankTrialLocalNextRecoveryBank]
        exact hfields.1
      have hfirst :
          BankTrialLocalFrontOut q
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q) root).bank 1 := by
        rw [bankTrialLocalNextRecoveryBank]
        exact hfields.2.2
      have hrank :
          bankTrialDurationRecoveryReadRank
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q) root) =
            2 * (compileAdvice q).b - 1 := by
        rw [bankTrialDurationRecoveryReadRankOut _ 1 hfirst]
        rfl
      have hlease :
          bankTrialDurationRecoveryReadLease
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q) root) =
            13 * ((compileAdvice q).b + 2) := by
        unfold bankTrialDurationRecoveryReadLease
        rw [bankTrialLocalNextRecoveryBank, hfields.2.1]
        rfl
      refine ⟨Or.inr hfrontNext, ?_⟩
      calc
        bankTrialDurationRecoveryClockOf
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q) root) =
            .waiting (2 * (compileAdvice q).b - 1)
              (13 * ((compileAdvice q).b + 2)) := by
                rw [bankTrialDurationRecoveryClockWaitOfFront
                  _ hfrontNext hmode, hrank, hlease]
        _ = bankTrialDurationRecoveryClockNext
            (compileAdvice q).b root
            (Counter.site ring root (n - 1))
            (bankTrialDurationRecoveryNominated ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q))
            root (bankTrialDurationRecoveryClockOf
              (⟨B, .recovery⟩ : BankTrialLocalState q)) := by
                rw [bankTrialDurationRecoveryClockResetOfFront
                  _ hf hm]
                simp [bankTrialDurationRecoveryClockNext]

/-- Class (2), incoming-root RWAIT: every positive-index digit
field is an exact frame, including all inherited suffix fields. -/
theorem bankTrialDurationRecoveryIncomingDigitFrame {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hin : ring.rightNeighbor e = root)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hf : B.success = false)
    (i : Fin ((compileAdvice q).b + 1))
    (hi : 0 < i.val) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields i = B.fields i := by
  rw [bankTrialDurationIncomingFieldsRow ring root e hw hin B hf]
  have hne : i.val ≠ 0 := by omega
  simp only [if_neg hne]

/-- Class (2), the scalar WATCHDOG equation on the full observer
bank, not merely on the underlying BANK reference. -/
theorem bankTrialDurationRecoveryIncomingObserverScalar {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hin : ring.rightNeighbor e = root)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RWAIT) :
    ((1 < bankTrialDurationRecoveryReadLease z ∧
      ((bankTrialLocalNext ring root z e).bank.fields
        ⟨0, by omega⟩).1 = .RWAIT ∧
      bankTrialDurationRecoveryReadLease
        (bankTrialLocalNext ring root z e) =
          bankTrialDurationRecoveryReadLease z - 1) ∨
     (bankTrialDurationRecoveryReadLease z ≤ 1 ∧
      ((bankTrialLocalNext ring root z e).bank.fields
        ⟨0, by omega⟩).1 = .RESET ∧
      bankTrialDurationRecoveryReadLease
        (bankTrialLocalNext ring root z e) = 0)) := by
  cases z with
  | mk B phase =>
      cases hf.1
      unfold bankTrialDurationRecoveryReadLease
      rw [bankTrialLocalNextRecoveryBank]
      exact bankTrialDurationRecoveryIncomingRootScalar
        ring root e hw B hf.2.2.1 hm hf.2.1 hin

/-- Class (2), G_1 root-outgoing return is precisely DONE;
there is no continuing RWAIT front at this boundary. -/
theorem bankTrialDurationRecoveryFinalReturnRow {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RWAIT)
    (hback : BankTrialLocalFrontBack q z.bank 1) :
    (bankTrialLocalTerminal (bankTrialLocalNext ring root z root) ∨
      BankTrialDurationRecoveryFront q
        (bankTrialLocalNext ring root z root)) ∧
    bankTrialDurationRecoveryClockOf
      (bankTrialLocalNext ring root z root) =
      bankTrialDurationRecoveryClockNext
        (compileAdvice q).b root
        (Counter.site ring root (n - 1))
        (bankTrialDurationRecoveryNominated ring root z)
        root (bankTrialDurationRecoveryClockOf z) := by
  have ht := bankTrialDurationRecoveryRootReturnTerminal
    ring root hn z hf hm hback
  have hd :
      bankTrialDurationRecoveryClockOf
        (bankTrialLocalNext ring root z root) = .done := by
    classical
    simp [bankTrialDurationRecoveryClockOf, ht]
  have hrank :
      bankTrialDurationRecoveryReadRank z = 1 := by
    rw [bankTrialDurationRecoveryReadRankBack z 1 hback]
    rfl
  refine ⟨Or.inl ht, ?_⟩
  calc
    bankTrialDurationRecoveryClockOf
        (bankTrialLocalNext ring root z root) = .done := hd
    _ = bankTrialDurationRecoveryClockNext
        (compileAdvice q).b root
        (Counter.site ring root (n - 1))
        (bankTrialDurationRecoveryNominated ring root z)
        root (bankTrialDurationRecoveryClockOf z) := by
          rw [bankTrialDurationRecoveryClockWaitOfFront z hf hm,
            hrank]
          simp [bankTrialDurationRecoveryClockNext]

/-- Class (3): the F_b self-test, on physical edge b-1.
No empty-suffix assumption is imposed (there is no suffix at b).
The actual reference becomes a full G_(b-1) array. -/
theorem bankTrialDurationRecoveryTopTurnFront {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (hfront : BankTrialLocalFrontOut q B (compileAdvice q).b) :
    BankTrialLocalFrontBack q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B
          (Counter.site ring root ((compileAdvice q).b - 1)))
      ((compileAdvice q).b - 1) := by
  have hwidth : 2 ≤ (compileAdvice q).b := by
    have hh := bankTrialDurationRecoveryWidthLarge q
    omega
  have hn : 2 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    omega
  have hpair := bankTrialLocalOutwardTopTurnPair
    ring root (Counter.site ring root ((compileAdvice q).b - 1))
    hn B hf (compileAdvice q).b hfront (by omega) rfl rfl
  refine ⟨(by omega), (by omega), hpair.1.1, hpair.1.2, ?_⟩
  intro i hi hib hneq
  by_cases hsame : i = (compileAdvice q).b
  · subst i
    exact hpair.2
  · by_cases hone : i = 1
    · subst i
      exact bankTrialLocalOutwardFirstSafe ring root
        (Counter.site ring root ((compileAdvice q).b - 1))
        hn B hf hm (compileAdvice q).b hfront (by omega)
    · exact bankTrialLocalFrontOutDeepPrefix ring root
        (Counter.site ring root ((compileAdvice q).b - 1))
        B hf (compileAdvice q).b i hfront
        (by omega) (by omega) hib

/-- Class (3), the complete actual observer/clock F_b top-turn row.
The selected service is site(root,b-1), not the unary top site. -/
theorem bankTrialDurationRecoveryTopTurnRow {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RWAIT)
    (hout : BankTrialLocalFrontOut q z.bank (compileAdvice q).b) :
    (bankTrialLocalTerminal
        (bankTrialLocalNext ring root z
          (Counter.site ring root ((compileAdvice q).b - 1))) ∨
      BankTrialDurationRecoveryFront q
        (bankTrialLocalNext ring root z
          (Counter.site ring root ((compileAdvice q).b - 1)))) ∧
    bankTrialDurationRecoveryClockOf
      (bankTrialLocalNext ring root z
        (Counter.site ring root ((compileAdvice q).b - 1))) =
      bankTrialDurationRecoveryClockNext
        (compileAdvice q).b root
        (Counter.site ring root (n - 1))
        (bankTrialDurationRecoveryNominated ring root z)
        (Counter.site ring root ((compileAdvice q).b - 1))
        (bankTrialDurationRecoveryClockOf z) := by
  cases z with
  | mk B phase =>
      cases hf.1
      have hwidth : 2 ≤ (compileAdvice q).b := by
        have hh := bankTrialDurationRecoveryWidthLarge q
        omega
      have hrootField :
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B
              (Counter.site ring root ((compileAdvice q).b - 1))).fields
              ⟨0, by omega⟩ = B.fields ⟨0, by omega⟩ := by
        have hprevLt : (compileAdvice q).b - 1 <
            (compileAdvice q).b := by omega
        have hprevPos : 0 < (compileAdvice q).b - 1 := by omega
        have hneqSrc : (0 : Nat) ≠ (compileAdvice q).b - 1 := by
          omega
        have hneqDst : (0 : Nat) ≠
            (compileAdvice q).b - 1 + 1 := by omega
        exact bankTrialWindowInteriorFrame ring root hw
          B hf.2.2.1
          ⟨(compileAdvice q).b - 1, hprevLt⟩ hprevPos
          ⟨0, by omega⟩ hneqSrc hneqDst
      have hmodeStep :
          ((GrantBankReference.bankLocalReferenceStepClamped
            ring root B
              (Counter.site ring root ((compileAdvice q).b - 1))).fields
              ⟨0, by omega⟩).1 = .RWAIT := by
        rw [hrootField]
        exact hm
      have hfalseStep := bankTrialDurationRecoveryFrontNoWin
        ring root
        (Counter.site ring root ((compileAdvice q).b - 1))
        (⟨B, .recovery⟩ : BankTrialLocalState q) hf
      have hphase := bankTrialDurationRecoveryNextPhaseAtBand
        ring root (Counter.site ring root ((compileAdvice q).b - 1))
        B hfalseStep (Or.inr hmodeStep)
      have hcap := bankTrialLocalLeaseCapNext ring root
        (Counter.site ring root ((compileAdvice q).b - 1))
        (⟨B, .recovery⟩ : BankTrialLocalState q) hf.2.1
      have hfalse :
          (bankTrialLocalNext ring root
            (⟨B, .recovery⟩ : BankTrialLocalState q)
            (Counter.site ring root ((compileAdvice q).b - 1))).bank.success =
              false := by
        rw [bankTrialLocalNextRecoveryBank]
        exact hfalseStep
      have hmode :
          bankTrialLiveWaveRootMode
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q)
              (Counter.site ring root ((compileAdvice q).b - 1))).bank =
              .RWAIT := by
        rw [bankTrialLocalNextRecoveryBank]
        exact hmodeStep
      have hpositive :
          1 ≤ ((bankTrialLocalNext ring root
            (⟨B, .recovery⟩ : BankTrialLocalState q)
            (Counter.site ring root ((compileAdvice q).b - 1))).bank.fields
            ⟨0, by omega⟩).2.2.2 := by
        rw [bankTrialLocalNextRecoveryBank, hrootField]
        exact bankTrialDurationRecoveryWaitLeasePositive
          (⟨B, .recovery⟩ : BankTrialLocalState q) hf hm
      have hback :
          BankTrialLocalFrontBack q
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q)
              (Counter.site ring root ((compileAdvice q).b - 1))).bank
            ((compileAdvice q).b - 1) := by
        rw [bankTrialLocalNextRecoveryBank]
        exact bankTrialDurationRecoveryTopTurnFront
          ring root hw B hf.2.2.1 hm hout
      have hv :
          Counter.resetClockValid (compileAdvice q).b
            (.returning ((compileAdvice q).b - 1)) := by
        change 1 ≤ (compileAdvice q).b - 1 ∧
          (compileAdvice q).b - 1 ≤ (compileAdvice q).b
        omega
      have hfrontNext :
          BankTrialDurationRecoveryFront q
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q)
              (Counter.site ring root ((compileAdvice q).b - 1))) :=
        ⟨hphase, hcap, hfalse,
          Or.inr ⟨hmode, hpositive,
            .returning ((compileAdvice q).b - 1), hv, hback⟩⟩
      have hrank :
          bankTrialDurationRecoveryReadRank
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q)
              (Counter.site ring root ((compileAdvice q).b - 1))) =
          bankTrialDurationRecoveryReadRank
            (⟨B, .recovery⟩ : BankTrialLocalState q) - 1 := by
        rw [bankTrialDurationRecoveryReadRankBack
          _ ((compileAdvice q).b - 1) hback,
          bankTrialDurationRecoveryReadRankOut
          _ (compileAdvice q).b hout]
        change (compileAdvice q).b - 1 =
          (2 * (compileAdvice q).b - (compileAdvice q).b) - 1
        omega
      have hlease :
          bankTrialDurationRecoveryReadLease
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q)
              (Counter.site ring root ((compileAdvice q).b - 1))) =
          bankTrialDurationRecoveryReadLease
            (⟨B, .recovery⟩ : BankTrialLocalState q) := by
        unfold bankTrialDurationRecoveryReadLease
        rw [bankTrialLocalNextRecoveryBank, hrootField]
      have hchosen :
          bankTrialDurationRecoveryNominated ring root
            (⟨B, .recovery⟩ : BankTrialLocalState q) =
          Counter.site ring root ((compileAdvice q).b - 1) := by
        unfold bankTrialDurationRecoveryNominated
        rw [bankTrialDurationRecoveryReadStageOut
          (⟨B, .recovery⟩ : BankTrialLocalState q)
          (compileAdvice q).b hout]
        simp [Counter.resetClockNominated]
      have hnotroot :
          Counter.site ring root ((compileAdvice q).b - 1) ≠ root := by
        have hprevLt : (compileAdvice q).b - 1 <
            (compileAdvice q).b := by omega
        have hprevPos : 0 < (compileAdvice q).b - 1 := by omega
        exact bankTrialWindowInteriorNotRoot ring root hw
          ⟨(compileAdvice q).b - 1, hprevLt⟩ hprevPos
      refine ⟨Or.inr hfrontNext, ?_⟩
      calc
        bankTrialDurationRecoveryClockOf
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q)
              (Counter.site ring root ((compileAdvice q).b - 1))) =
            .waiting
              (bankTrialDurationRecoveryReadRank
                (⟨B, .recovery⟩ : BankTrialLocalState q) - 1)
              (bankTrialDurationRecoveryReadLease
                (⟨B, .recovery⟩ : BankTrialLocalState q)) := by
                  rw [bankTrialDurationRecoveryClockWaitOfFront
                    _ hfrontNext hmode, hrank, hlease]
        _ = bankTrialDurationRecoveryClockNext
            (compileAdvice q).b root
            (Counter.site ring root (n - 1))
            (bankTrialDurationRecoveryNominated ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q))
            (Counter.site ring root ((compileAdvice q).b - 1))
            (bankTrialDurationRecoveryClockOf
              (⟨B, .recovery⟩ : BankTrialLocalState q)) := by
                rw [bankTrialDurationRecoveryClockWaitOfFront
                  _ hf hm, hchosen]
                simp [bankTrialDurationRecoveryClockNext, hnotroot]

/-- Requested literal F_b cut test: positive RWAIT lease, all
protected bits zero, all lower tokens E, top token RR. -/
theorem bankTrialDurationRecoveryTopCutTest {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RWAIT)
    (hpositive : 1 ≤ bankTrialDurationRecoveryReadLease z)
    (hbits : ∀ i : Nat, 1 ≤ i →
      (hib : i ≤ (compileAdvice q).b) →
      (z.bank.fields ⟨i, Nat.lt_succ_of_le hib⟩).2.1 = false)
    (hlower : ∀ i : Nat, 1 ≤ i →
      i < (compileAdvice q).b →
      (hib : i ≤ (compileAdvice q).b) →
      (z.bank.fields ⟨i, Nat.lt_succ_of_le hib⟩).2.2.1 = .E)
    (htop :
      (z.bank.fields ⟨(compileAdvice q).b, by omega⟩).2.2.1 = .RR) :
    (bankTrialLocalTerminal
        (bankTrialLocalNext ring root z
          (Counter.site ring root ((compileAdvice q).b - 1))) ∨
      BankTrialDurationRecoveryFront q
        (bankTrialLocalNext ring root z
          (Counter.site ring root ((compileAdvice q).b - 1)))) ∧
    bankTrialDurationRecoveryClockOf
      (bankTrialLocalNext ring root z
        (Counter.site ring root ((compileAdvice q).b - 1))) =
      bankTrialDurationRecoveryClockNext
        (compileAdvice q).b root
        (Counter.site ring root (n - 1))
        (bankTrialDurationRecoveryNominated ring root z)
        (Counter.site ring root ((compileAdvice q).b - 1))
        (bankTrialDurationRecoveryClockOf z) := by
  have hwidth : 2 ≤ (compileAdvice q).b := by
    have hh := bankTrialDurationRecoveryWidthLarge q
    omega
  have hout : BankTrialLocalFrontOut q z.bank (compileAdvice q).b := by
    refine ⟨Nat.le_refl _, (by omega), ?_, htop, ?_⟩
    · exact hbits (compileAdvice q).b (by omega) (by omega)
    · intro i hi hij hib
      exact ⟨hbits i hi hib, hlower i hi hij hib⟩
  exact bankTrialDurationRecoveryTopTurnRow ring root hw z hf hm hout

/-- A source-level frame of all digit data transfers every F_j
certificate, regardless of the unrestricted suffix. -/
private theorem bankTrialDurationRecoveryOutDigitFrame {q : Nat}
    (B C : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hframe : ∀ i : Fin ((compileAdvice q).b + 1),
      0 < i.val → C.fields i = B.fields i)
    (j : Nat) (hj : BankTrialLocalFrontOut q B j) :
    BankTrialLocalFrontOut q C j := by
  obtain ⟨hjb, hjpos, hbit, htok, hpre⟩ := hj
  refine ⟨hjb, hjpos, ?_, ?_, ?_⟩
  · rw [hframe ⟨j, Nat.lt_succ_of_le hjb⟩ hjpos]
    exact hbit
  · rw [hframe ⟨j, Nat.lt_succ_of_le hjb⟩ hjpos]
    exact htok
  · intro i hi hij hib
    rw [hframe ⟨i, Nat.lt_succ_of_le hib⟩ hi]
    exact hpre i hi hij hib

/-- A source-level positive-digit frame also preserves every
returning G_j certificate. -/
private theorem bankTrialDurationRecoveryBackDigitFrame {q : Nat}
    (B C : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hframe : ∀ i : Fin ((compileAdvice q).b + 1),
      0 < i.val → C.fields i = B.fields i)
    (j : Nat) (hj : BankTrialLocalFrontBack q B j) :
    BankTrialLocalFrontBack q C j := by
  obtain ⟨hjb, hjpos, hbit, htok, hother⟩ := hj
  refine ⟨hjb, hjpos, ?_, ?_, ?_⟩
  · rw [hframe ⟨j, Nat.lt_succ_of_le hjb⟩ hjpos]
    exact hbit
  · rw [hframe ⟨j, Nat.lt_succ_of_le hjb⟩ hjpos]
    exact htok
  · intro i hi hib hneq
    rw [hframe ⟨i, Nat.lt_succ_of_le hib⟩ hi]
    exact hother i hi hib hneq

/-- A digit frame transfers the *selected* reset-clock stage. -/
private theorem bankTrialDurationRecoveryStageDigitFrame {q : Nat}
    (B C : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hframe : ∀ i : Fin ((compileAdvice q).b + 1),
      0 < i.val → C.fields i = B.fields i)
    (stage : Counter.ResetClockStage)
    (hstage :
      match stage with
      | .outward j => BankTrialLocalFrontOut q B j
      | .returning j => BankTrialLocalFrontBack q B j
      | .finished => False) :
    (match stage with
      | .outward j => BankTrialLocalFrontOut q C j
      | .returning j => BankTrialLocalFrontBack q C j
      | .finished => False) := by
  cases stage with
  | outward j =>
      exact bankTrialDurationRecoveryOutDigitFrame B C hframe j hstage
  | returning j =>
      exact bankTrialDurationRecoveryBackDigitFrame B C hframe j hstage
  | finished =>
      exact False.elim hstage

/-- Rank is unchanged by a complete positive-digit frame when
the old state has an authenticated F/G stage. -/
private theorem bankTrialDurationRecoveryReadRankDigitFrame {q : Nat}
    (B C : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hframe : ∀ i : Fin ((compileAdvice q).b + 1),
      0 < i.val → C.fields i = B.fields i)
    (stage : Counter.ResetClockStage)
    (hstage :
      match stage with
      | .outward j => BankTrialLocalFrontOut q B j
      | .returning j => BankTrialLocalFrontBack q B j
      | .finished => False) :
    bankTrialDurationRecoveryReadRank
      (⟨C, .recovery⟩ : BankTrialLocalState q) =
    bankTrialDurationRecoveryReadRank
      (⟨B, .recovery⟩ : BankTrialLocalState q) := by
  cases stage with
  | outward j =>
      have hn := bankTrialDurationRecoveryOutDigitFrame
        B C hframe j hstage
      rw [bankTrialDurationRecoveryReadRankOut
          (⟨C, .recovery⟩ : BankTrialLocalState q) j hn,
        bankTrialDurationRecoveryReadRankOut
          (⟨B, .recovery⟩ : BankTrialLocalState q) j hstage]
  | returning j =>
      have hn := bankTrialDurationRecoveryBackDigitFrame
        B C hframe j hstage
      rw [bankTrialDurationRecoveryReadRankBack
          (⟨C, .recovery⟩ : BankTrialLocalState q) j hn,
        bankTrialDurationRecoveryReadRankBack
          (⟨B, .recovery⟩ : BankTrialLocalState q) j hstage]
  | finished =>
      exact False.elim hstage

/-- Modular coordinate of the physical clockwise site. -/
private theorem bankTrialDurationRecoverySiteValue {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ j : Nat,
      (Counter.site ring root j).val = (root.val + j) % n := by
  intro j
  induction j with
  | zero =>
      simp [Counter.site, Nat.mod_eq_of_lt root.isLt]
  | succ j ih =>
      change ((Counter.site ring root j).val + 1) % n =
        (root.val + (j + 1)) % n
      rw [ih, Nat.mod_add_mod]
      congr 1

/-- The logical predecessor at offset n-1 is the physical
incoming-root edge, not an extra abstract scheduler letter. -/
private theorem bankTrialDurationRecoveryLastIncoming {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ring.rightNeighbor (Counter.site ring root (n - 1)) = root := by
  have hn : 1 ≤ n := ring.hn
  have hindex : n - 1 + 1 = n := by omega
  have hfull : Counter.site ring root n = root := by
    apply Fin.ext
    rw [bankTrialDurationRecoverySiteValue ring root n]
    have hv : (root.val + n) % n = root.val := by
      rw [Nat.add_mod]
      simp [Nat.mod_eq_of_lt root.isLt]
    exact hv
  change Counter.site ring root (n - 1 + 1) = root
  rw [hindex]
  exact hfull

/-- Every incoming-root physical letter is exactly the clock's
distinguished site(root,n-1), by successor injectivity. -/
private theorem bankTrialDurationRecoveryIncomingLabel {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hin : ring.rightNeighbor e = root) :
    e = Counter.site ring root (n - 1) := by
  apply Counter.resetTrialNeighborInjective ring
  exact hin.trans (bankTrialDurationRecoveryLastIncoming ring root).symm

/-- The proper digit edges, including top-turn b-1, never
enter root when b+2 ≤ n. -/
private theorem bankTrialDurationRecoveryDigitNotIncoming {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (j : Nat) (hj : j < (compileAdvice q).b) :
    ring.rightNeighbor (Counter.site ring root j) ≠ root := by
  intro he
  have hsite : Counter.site ring root (j + 1) =
      Counter.site ring root 0 := by
    exact he
  have hh := bankTrialWindowSitesDistinct ring root hw
    (j + 1) 0 (by omega) (by omega) hsite
  omega

/-- The nominated edge for any RWAIT F/G front is not
incoming-root. The final G_1 nominee is the root outgoing. -/
private theorem bankTrialDurationRecoveryNominatedNotIncoming {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RWAIT) :
    ring.rightNeighbor
        (bankTrialDurationRecoveryNominated ring root z) ≠ root := by
  rcases hf.2.2.2 with hr | ⟨_, _, stage, hvalid, hstage⟩
  · cases (hm.symm.trans hr.1)
  cases stage with
  | outward j =>
      obtain ⟨hpos, hbound⟩ := hvalid
      have hread := bankTrialDurationRecoveryReadStageOut z j hstage
      unfold bankTrialDurationRecoveryNominated
      rw [hread]
      change ring.rightNeighbor
          (Counter.resetClockNominated ring root (compileAdvice q).b
            (.outward j)) ≠ root
      by_cases hj : j < (compileAdvice q).b
      · simp only [Counter.resetClockNominated, if_pos hj]
        exact bankTrialDurationRecoveryDigitNotIncoming
          ring root hw j hj
      · have heq : j = (compileAdvice q).b := by omega
        simp only [Counter.resetClockNominated, if_neg hj]
        exact bankTrialDurationRecoveryDigitNotIncoming
          ring root hw ((compileAdvice q).b - 1) (by omega)
  | returning j =>
      obtain ⟨hpos, hbound⟩ := hvalid
      have hread := bankTrialDurationRecoveryReadStageBack z j hstage
      unfold bankTrialDurationRecoveryNominated
      rw [hread]
      change ring.rightNeighbor
          (Counter.resetClockNominated ring root (compileAdvice q).b
            (.returning j)) ≠ root
      by_cases hj : 1 < j
      · simp only [Counter.resetClockNominated, if_pos hj]
        exact bankTrialDurationRecoveryDigitNotIncoming
          ring root hw (j - 1) (by omega)
      · simp only [Counter.resetClockNominated, if_neg hj]
        have hn : 2 ≤ n := by
          unfold BankTrialLiveWindowNonalias at hw
          omega
        exact Counter.resetRootPortDistinct ring root hn
  | finished =>
      exact False.elim hstage

theorem bankTrialDurationRecoveryIncomingObserverFront {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hin : ring.rightNeighbor e = root)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RWAIT) :
    BankTrialDurationRecoveryFront q
      (bankTrialLocalNext ring root z e) := by
  cases z with
  | mk B phase =>
      cases hf.1
      rcases hf.2.2.2 with hr | ⟨_, _, stage, hvalid, hstage⟩
      · cases (hm.symm.trans hr.1)
      have hfalseStep := bankTrialDurationRecoveryFrontNoWin
        ring root e (⟨B, .recovery⟩ : BankTrialLocalState q) hf
      have hcap := bankTrialLocalLeaseCapNext ring root e
        (⟨B, .recovery⟩ : BankTrialLocalState q) hf.2.1
      have hfalse :
          (bankTrialLocalNext ring root
            (⟨B, .recovery⟩ : BankTrialLocalState q) e).bank.success =
            false := by
        rw [bankTrialLocalNextRecoveryBank]
        exact hfalseStep
      have hrootStep := bankTrialDurationRecoveryIncomingRootScalar (q := q)
        ring root e hw B hf.2.2.1 hm hf.2.1 hin
      rcases hrootStep with ⟨hl, hmode, hlease⟩ |
          ⟨hl, hmode, hlease⟩
      · have hphase := bankTrialDurationRecoveryNextPhaseAtBand (q := q)
          ring root e B hfalseStep (Or.inr hmode)
        have hnewmode :
            bankTrialLiveWaveRootMode
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q) e).bank =
              .RWAIT := by
          rw [bankTrialLocalNextRecoveryBank]
          exact hmode
        have hnewlease :
            1 ≤ bankTrialDurationRecoveryReadLease
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q) e) := by
          unfold bankTrialDurationRecoveryReadLease
          rw [bankTrialLocalNextRecoveryBank, hlease]
          omega
        have hframe :
            ∀ i : Fin ((compileAdvice q).b + 1), 0 < i.val →
              (GrantBankReference.bankLocalReferenceStepClamped
                ring root B e).fields i = B.fields i := by
          intro i hi
          exact bankTrialDurationRecoveryIncomingDigitFrame (q := q)
            ring root e hw hin B hf.2.2.1 i hi
        have hstageNew :
            (match stage with
             | .outward j => BankTrialLocalFrontOut q
                (bankTrialLocalNext ring root
                  (⟨B, .recovery⟩ : BankTrialLocalState q) e).bank j
             | .returning j => BankTrialLocalFrontBack q
                (bankTrialLocalNext ring root
                  (⟨B, .recovery⟩ : BankTrialLocalState q) e).bank j
             | .finished => False) := by
          cases stage with
          | outward k =>
              simpa only [bankTrialLocalNextRecoveryBank] using
                (bankTrialDurationRecoveryOutDigitFrame (q := q)
                  B (GrantBankReference.bankLocalReferenceStepClamped
                    ring root B e) hframe k hstage)
          | returning k =>
              simpa only [bankTrialLocalNextRecoveryBank] using
                (bankTrialDurationRecoveryBackDigitFrame (q := q)
                  B (GrantBankReference.bankLocalReferenceStepClamped
                    ring root B e) hframe k hstage)
          | finished =>
              exact False.elim hstage
        refine ⟨hphase, hcap, hfalse, ?_⟩
        right
        refine ⟨?_, ?_, stage, ?_, ?_⟩
        · exact hnewmode
        · exact hnewlease
        · exact hvalid
        · cases stage with
          | outward k =>
              exact hstageNew
          | returning k =>
              exact hstageNew
          | finished =>
              exact False.elim hstageNew
      · have hphase := bankTrialDurationRecoveryNextPhaseAtBand (q := q)
          ring root e B hfalseStep (Or.inl hmode)
        have hnewmode :
            bankTrialLiveWaveRootMode
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q) e).bank =
              .RESET := by
          rw [bankTrialLocalNextRecoveryBank]
          exact hmode
        have hnewlease :
            ((bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q) e).bank.fields
              ⟨0, by omega⟩).2.2.2 = 0 := by
          rw [bankTrialLocalNextRecoveryBank]
          exact hlease
        exact ⟨hphase, hcap, hfalse,
          Or.inl ⟨hnewmode, hnewlease⟩⟩

/-- The incoming-root RWAIT observer has exactly the proposed
clock transition. This checks the nonaliased F_b cut as well:
an arriving root watchdog tick does not consume its RR top. -/
theorem bankTrialDurationRecoveryIncomingObserverRow {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hin : ring.rightNeighbor e = root)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RWAIT) :
    (bankTrialLocalTerminal (bankTrialLocalNext ring root z e) ∨
      BankTrialDurationRecoveryFront q
        (bankTrialLocalNext ring root z e)) ∧
    bankTrialDurationRecoveryClockOf
        (bankTrialLocalNext ring root z e) =
      bankTrialDurationRecoveryClockNext
        (compileAdvice q).b root
        (Counter.site ring root (n - 1))
        (bankTrialDurationRecoveryNominated ring root z)
        e (bankTrialDurationRecoveryClockOf z) := by
  have hfrontNext :=
    bankTrialDurationRecoveryIncomingObserverFront
      ring root e hw hin z hf hm
  have hn : 2 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    omega
  have hnotroot : e ≠ root := by
    intro he
    rw [he] at hin
    exact (Counter.resetRootPortDistinct ring root hn) hin
  have hnotchosen :
      e ≠ bankTrialDurationRecoveryNominated ring root z := by
    intro he
    rw [he] at hin
    exact (bankTrialDurationRecoveryNominatedNotIncoming
      ring root hw z hf hm) hin
  have hfirstGuard :
      ¬ (bankTrialDurationRecoveryReadRank z = 1 ∧ e = root) := by
    intro h
    exact hnotroot h.2
  have hrootor :
      e = root ∨ e = Counter.site ring root (n - 1) :=
    Or.inr (bankTrialDurationRecoveryIncomingLabel ring root e hin)
  cases z with
  | mk B phase =>
      cases hf.1
      rcases hf.2.2.2 with hr | ⟨_, _, stage, hvalid, hstage⟩
      · cases (hm.symm.trans hr.1)
      have hfalseStep := bankTrialDurationRecoveryFrontNoWin
        ring root e (⟨B, .recovery⟩ : BankTrialLocalState q) hf
      have hscalar := bankTrialDurationRecoveryIncomingRootScalar
        ring root e hw B hf.2.2.1 hm hf.2.1 hin
      have hframe :
          ∀ i : Fin ((compileAdvice q).b + 1), 0 < i.val →
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B e).fields i = B.fields i := by
        intro i hi
        exact bankTrialDurationRecoveryIncomingDigitFrame
          ring root e hw hin B hf.2.2.1 i hi
      have hrank :
          bankTrialDurationRecoveryReadRank
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q) e) =
          bankTrialDurationRecoveryReadRank
            (⟨B, .recovery⟩ : BankTrialLocalState q) := by
        change bankTrialDurationRecoveryReadRank
          (⟨(bankTrialLocalNext ring root
            (⟨B, .recovery⟩ : BankTrialLocalState q) e).bank,
              .recovery⟩ : BankTrialLocalState q) =
          bankTrialDurationRecoveryReadRank
            (⟨B, .recovery⟩ : BankTrialLocalState q)
        rw [bankTrialLocalNextRecoveryBank]
        exact bankTrialDurationRecoveryReadRankDigitFrame
          B (GrantBankReference.bankLocalReferenceStepClamped
            ring root B e) hframe stage hstage
      rcases hscalar with ⟨hl, hmode, hlease⟩ |
          ⟨hl, hmode, hlease⟩
      · have hnewmode :
            bankTrialLiveWaveRootMode
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q) e).bank =
              .RWAIT := by
          rw [bankTrialLocalNextRecoveryBank]
          exact hmode
        have hnewlease :
            bankTrialDurationRecoveryReadLease
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q) e) =
            bankTrialDurationRecoveryReadLease
              (⟨B, .recovery⟩ : BankTrialLocalState q) - 1 := by
          unfold bankTrialDurationRecoveryReadLease
          rw [bankTrialLocalNextRecoveryBank]
          exact hlease
        have hgt :
            ¬ bankTrialDurationRecoveryReadLease
              (⟨B, .recovery⟩ : BankTrialLocalState q) ≤ 1 := by
          change ¬ (B.fields ⟨0, by omega⟩).2.2.2 ≤ 1
          omega
        have hclockStep :
            bankTrialDurationRecoveryClockNext
              (compileAdvice q).b root
              (Counter.site ring root (n - 1))
              (bankTrialDurationRecoveryNominated ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q))
              e (.waiting
                (bankTrialDurationRecoveryReadRank
                  (⟨B, .recovery⟩ : BankTrialLocalState q))
                (bankTrialDurationRecoveryReadLease
                  (⟨B, .recovery⟩ : BankTrialLocalState q))) =
            .waiting
              (bankTrialDurationRecoveryReadRank
                (⟨B, .recovery⟩ : BankTrialLocalState q))
              (bankTrialDurationRecoveryReadLease
                (⟨B, .recovery⟩ : BankTrialLocalState q) - 1) := by
          simp only [bankTrialDurationRecoveryClockNext,
            if_neg hfirstGuard, if_neg hnotchosen,
            if_pos hrootor, if_neg hgt]
        refine ⟨Or.inr hfrontNext, ?_⟩
        calc
          bankTrialDurationRecoveryClockOf
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q) e) =
            .waiting
              (bankTrialDurationRecoveryReadRank
                (⟨B, .recovery⟩ : BankTrialLocalState q))
              (bankTrialDurationRecoveryReadLease
                (⟨B, .recovery⟩ : BankTrialLocalState q) - 1) := by
                  rw [bankTrialDurationRecoveryClockWaitOfFront
                    _ hfrontNext hnewmode, hrank, hnewlease]
          _ = bankTrialDurationRecoveryClockNext
              (compileAdvice q).b root
              (Counter.site ring root (n - 1))
              (bankTrialDurationRecoveryNominated ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q))
              e (bankTrialDurationRecoveryClockOf
                (⟨B, .recovery⟩ : BankTrialLocalState q)) := by
                  rw [bankTrialDurationRecoveryClockWaitOfFront
                    _ hf hm, hclockStep]
      · have hnewmode :
            bankTrialLiveWaveRootMode
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q) e).bank =
              .RESET := by
          rw [bankTrialLocalNextRecoveryBank]
          exact hmode
        have hle :
            bankTrialDurationRecoveryReadLease
              (⟨B, .recovery⟩ : BankTrialLocalState q) ≤ 1 := hl
        have hclockStep :
            bankTrialDurationRecoveryClockNext
              (compileAdvice q).b root
              (Counter.site ring root (n - 1))
              (bankTrialDurationRecoveryNominated ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q))
              e (.waiting
                (bankTrialDurationRecoveryReadRank
                  (⟨B, .recovery⟩ : BankTrialLocalState q))
                (bankTrialDurationRecoveryReadLease
                  (⟨B, .recovery⟩ : BankTrialLocalState q))) =
              .reset := by
          simp only [bankTrialDurationRecoveryClockNext,
            if_neg hfirstGuard, if_neg hnotchosen,
            if_pos hrootor, if_pos hle]
        refine ⟨Or.inr hfrontNext, ?_⟩
        calc
          bankTrialDurationRecoveryClockOf
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q) e) =
              .reset := bankTrialDurationRecoveryClockResetOfFront
                _ hfrontNext hnewmode
          _ = bankTrialDurationRecoveryClockNext
              (compileAdvice q).b root
              (Counter.site ring root (n - 1))
              (bankTrialDurationRecoveryNominated ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q))
              e (bankTrialDurationRecoveryClockOf
                (⟨B, .recovery⟩ : BankTrialLocalState q)) := by
                  rw [bankTrialDurationRecoveryClockWaitOfFront
                    _ hf hm, hclockStep]

/-- RESET incoming-root does not change its zero root lease.
The raw responder empties its token only; the physical clamp
keeps zero exactly. -/
private theorem bankTrialDurationRecoveryIncomingResetRaw (q : Nat)
    (x : BankCell) (hm : x.mode = .RESET) (hl : x.lease = 0) :
    (GrantBankReference.bankLocalReferenceClampedQuad q
      (GrantBankReference.incomingRootBankMap x)).1 = .RESET ∧
    (GrantBankReference.bankLocalReferenceClampedQuad q
      (GrantBankReference.incomingRootBankMap x)).2.2.2 = 0 := by
  simp [GrantBankReference.bankLocalReferenceClampedQuad,
    GrantBankReference.bankAgentLeaseQuad, copyBank,
    GrantBankReference.incomingRootBankMap, hm, hl, isWaitMode]

/-- Class (1), RESET away from the root: exact root mode and
zero lease, even for the incoming-root orientation. -/
theorem bankTrialDurationRecoveryResetAwayFields {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RESET)
    (hl : (B.fields ⟨0, by omega⟩).2.2.2 = 0)
    (hne : e ≠ root) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨0, by omega⟩).1 = .RESET ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨0, by omega⟩).2.2.2 = 0 := by
  by_cases hin : ring.rightNeighbor e = root
  · have hfields := bankTrialDurationIncomingFieldsRow
      ring root e hw hin B hf
    have hraw := bankTrialDurationRecoveryIncomingResetRaw q
      (GrantBankReference.bankLocalReferenceCell B
        ⟨0, by omega⟩) hm hl
    constructor
    · rw [hfields]
      simpa only [Fin.val_mk, ↓reduceIte] using hraw.1
    · rw [hfields]
      simpa only [Fin.val_mk, ↓reduceIte] using hraw.2
  · have hframe := bankTrialLocalRootNonincidentFrame
      ring root e B hf hne hin
    rw [hframe]
    exact ⟨hm, hl⟩

/-- Class (1), every nonroot scheduler letter (including the
incoming root) preserves RESET front and the RESET clock. -/
theorem bankTrialDurationRecoveryResetAwayRow {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RESET)
    (hne : e ≠ root) :
    (bankTrialLocalTerminal (bankTrialLocalNext ring root z e) ∨
      BankTrialDurationRecoveryFront q
        (bankTrialLocalNext ring root z e)) ∧
    bankTrialDurationRecoveryClockOf
        (bankTrialLocalNext ring root z e) =
      bankTrialDurationRecoveryClockNext
        (compileAdvice q).b root
        (Counter.site ring root (n - 1))
        (bankTrialDurationRecoveryNominated ring root z)
        e (bankTrialDurationRecoveryClockOf z) := by
  cases z with
  | mk B phase =>
      cases hf.1
      rcases hf.2.2.2 with ⟨hroot, hlease⟩ | hwait
      · have hfields := bankTrialDurationRecoveryResetAwayFields
          ring root e hw B hf.2.2.1 hm hlease hne
        have hfalseStep := bankTrialDurationRecoveryFrontNoWin
          ring root e (⟨B, .recovery⟩ : BankTrialLocalState q) hf
        have hcap := bankTrialLocalLeaseCapNext ring root e
          (⟨B, .recovery⟩ : BankTrialLocalState q) hf.2.1
        have hphase := bankTrialDurationRecoveryNextPhaseAtBand
          ring root e B hfalseStep (Or.inl hfields.1)
        have hfalse :
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q) e).bank.success =
              false := by
          rw [bankTrialLocalNextRecoveryBank]
          exact hfalseStep
        have hmode :
            bankTrialLiveWaveRootMode
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q) e).bank =
              .RESET := by
          rw [bankTrialLocalNextRecoveryBank]
          exact hfields.1
        have hzero :
            ((bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q) e).bank.fields
              ⟨0, by omega⟩).2.2.2 = 0 := by
          rw [bankTrialLocalNextRecoveryBank]
          exact hfields.2
        have hfrontNext : BankTrialDurationRecoveryFront q
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q) e) :=
          ⟨hphase, hcap, hfalse, Or.inl ⟨hmode, hzero⟩⟩
        refine ⟨Or.inr hfrontNext, ?_⟩
        calc
          bankTrialDurationRecoveryClockOf
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q) e) =
              .reset := bankTrialDurationRecoveryClockResetOfFront
                _ hfrontNext hmode
          _ = bankTrialDurationRecoveryClockNext
              (compileAdvice q).b root
              (Counter.site ring root (n - 1))
              (bankTrialDurationRecoveryNominated ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q))
              e (bankTrialDurationRecoveryClockOf
                (⟨B, .recovery⟩ : BankTrialLocalState q)) := by
                  rw [bankTrialDurationRecoveryClockResetOfFront
                    _ hf hm]
                  simp [bankTrialDurationRecoveryClockNext, hne]
      · cases (hm.symm.trans hwait.1)

/-- A fully unsupported scheduler letter is a proven row once
the three abstract distinguished-port inequalities are known. -/
theorem bankTrialDurationRecoveryOutsideClockRow {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hout : ¬ Counter.Support q ring root e)
    (hnotIncoming : e ≠ Counter.site ring root (n - 1))
    (hnotChosen :
      e ≠ bankTrialDurationRecoveryNominated ring root z) :
    (bankTrialLocalTerminal (bankTrialLocalNext ring root z e) ∨
      BankTrialDurationRecoveryFront q
        (bankTrialLocalNext ring root z e)) ∧
    bankTrialDurationRecoveryClockOf
        (bankTrialLocalNext ring root z e) =
      bankTrialDurationRecoveryClockNext
        (compileAdvice q).b root
        (Counter.site ring root (n - 1))
        (bankTrialDurationRecoveryNominated ring root z)
        e (bankTrialDurationRecoveryClockOf z) := by
  have hbase := bankTrialDurationRecoveryOutsideFrontRow
    ring root e z hf hout
  have hnotroot : e ≠ root := by
    intro he
    apply hout
    exact Or.inr ⟨0, Nat.zero_le _, by simpa only [Counter.site] using he⟩
  refine ⟨hbase.1, ?_⟩
  calc
    bankTrialDurationRecoveryClockOf
      (bankTrialLocalNext ring root z e) =
        bankTrialDurationRecoveryClockOf z := hbase.2
    _ = bankTrialDurationRecoveryClockNext
      (compileAdvice q).b root
      (Counter.site ring root (n - 1))
      (bankTrialDurationRecoveryNominated ring root z)
      e (bankTrialDurationRecoveryClockOf z) :=
        (bankTrialDurationRecoveryClockNextAway
          (compileAdvice q).b root
          (Counter.site ring root (n - 1))
          (bankTrialDurationRecoveryNominated ring root z)
          e hnotroot hnotIncoming hnotChosen
          (bankTrialDurationRecoveryClockOf z)).symm


theorem bankTrialDurationRecoveryNominatedInteriorOfStage {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RWAIT)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (stage : Counter.ResetClockStage)
    (hvalid : Counter.resetClockValid (compileAdvice q).b stage)
    (hstage :
      match stage with
      | .outward k => BankTrialLocalFrontOut q
          (bankTrialLocalNext ring root z
            (Counter.site ring root j.val)).bank k
      | .returning k => BankTrialLocalFrontBack q
          (bankTrialLocalNext ring root z
            (Counter.site ring root j.val)).bank k
      | .finished => False)
    (hrank :
      bankTrialDurationRecoveryReadRank
        (bankTrialLocalNext ring root z
          (Counter.site ring root j.val)) =
        bankTrialDurationRecoveryReadRank z - 1)
    (hchosen :
      bankTrialDurationRecoveryNominated ring root z =
        Counter.site ring root j.val) :
    (bankTrialLocalTerminal
        (bankTrialLocalNext ring root z
          (Counter.site ring root j.val)) ∨
      BankTrialDurationRecoveryFront q
        (bankTrialLocalNext ring root z
          (Counter.site ring root j.val))) ∧
    bankTrialDurationRecoveryClockOf
        (bankTrialLocalNext ring root z
          (Counter.site ring root j.val)) =
      bankTrialDurationRecoveryClockNext
        (compileAdvice q).b root
        (Counter.site ring root (n - 1))
        (bankTrialDurationRecoveryNominated ring root z)
        (Counter.site ring root j.val)
        (bankTrialDurationRecoveryClockOf z) := by
  cases z with
  | mk B phase =>
      cases hf.1
      have hrootField :
          (GrantBankReference.bankLocalReferenceStepClamped ring root
            B (Counter.site ring root j.val)).fields ⟨0, by omega⟩ =
          B.fields ⟨0, by omega⟩ := by
        exact bankTrialWindowInteriorFrame (q := q) ring root hw
          B hf.2.2.1 j hj ⟨0, by omega⟩
          (Nat.ne_of_lt hj) (Nat.succ_ne_zero j.val).symm
      have hfalseStep := bankTrialDurationRecoveryFrontNoWin
        ring root (Counter.site ring root j.val)
        (⟨B, .recovery⟩ : BankTrialLocalState q) hf
      have hmodeStep :
          ((GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j.val)).fields
            ⟨0, by omega⟩).1 = .RWAIT := by
        rw [hrootField]
        exact hm
      have hphase := bankTrialDurationRecoveryNextPhaseAtBand (q := q)
        ring root (Counter.site ring root j.val) B hfalseStep
        (Or.inr hmodeStep)
      have hcap := bankTrialLocalLeaseCapNext ring root
        (Counter.site ring root j.val)
        (⟨B, .recovery⟩ : BankTrialLocalState q) hf.2.1
      have hfalse :
          (bankTrialLocalNext ring root
            (⟨B, .recovery⟩ : BankTrialLocalState q)
            (Counter.site ring root j.val)).bank.success = false := by
        rw [bankTrialLocalNextRecoveryBank]
        exact hfalseStep
      have hnewmode :
          bankTrialLiveWaveRootMode
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q)
              (Counter.site ring root j.val)).bank = .RWAIT := by
        rw [bankTrialLocalNextRecoveryBank]
        exact hmodeStep
      have hlease :
          bankTrialDurationRecoveryReadLease
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q)
              (Counter.site ring root j.val)) =
          bankTrialDurationRecoveryReadLease
            (⟨B, .recovery⟩ : BankTrialLocalState q) := by
        unfold bankTrialDurationRecoveryReadLease
        rw [bankTrialLocalNextRecoveryBank, hrootField]
      have hpositive :
          1 ≤ bankTrialDurationRecoveryReadLease
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q)
              (Counter.site ring root j.val)) := by
        rw [hlease]
        exact bankTrialDurationRecoveryWaitLeasePositive
          (⟨B, .recovery⟩ : BankTrialLocalState q) hf hm
      have hfrontNext :
          BankTrialDurationRecoveryFront q
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q)
              (Counter.site ring root j.val)) := by
        refine ⟨hphase, hcap, hfalse, ?_⟩
        right
        refine ⟨?_, ?_, stage, ?_, ?_⟩
        · exact hnewmode
        · exact hpositive
        · exact hvalid
        · cases stage with
          | outward k =>
              exact hstage
          | returning k =>
              exact hstage
          | finished =>
              exact False.elim hstage
      have hnotroot : Counter.site ring root j.val ≠ root :=
        bankTrialWindowInteriorNotRoot (q := q) ring root hw j hj
      have hfirstGuard :
          ¬ (bankTrialDurationRecoveryReadRank
              (⟨B, .recovery⟩ : BankTrialLocalState q) = 1 ∧
            Counter.site ring root j.val = root) := by
        intro h
        exact hnotroot h.2
      have hclockStep :
          bankTrialDurationRecoveryClockNext
            (compileAdvice q).b root
            (Counter.site ring root (n - 1))
            (bankTrialDurationRecoveryNominated ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q))
            (Counter.site ring root j.val)
            (.waiting
              (bankTrialDurationRecoveryReadRank
                (⟨B, .recovery⟩ : BankTrialLocalState q))
              (bankTrialDurationRecoveryReadLease
                (⟨B, .recovery⟩ : BankTrialLocalState q))) =
          .waiting
            (bankTrialDurationRecoveryReadRank
              (⟨B, .recovery⟩ : BankTrialLocalState q) - 1)
            (bankTrialDurationRecoveryReadLease
              (⟨B, .recovery⟩ : BankTrialLocalState q)) := by
        have hh : Counter.site ring root j.val =
            bankTrialDurationRecoveryNominated ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q) :=
          hchosen.symm
        simp only [bankTrialDurationRecoveryClockNext,
          if_neg hfirstGuard, if_pos hh]
      refine ⟨Or.inr hfrontNext, ?_⟩
      calc
        bankTrialDurationRecoveryClockOf
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q)
              (Counter.site ring root j.val)) =
          .waiting
            (bankTrialDurationRecoveryReadRank
              (⟨B, .recovery⟩ : BankTrialLocalState q) - 1)
            (bankTrialDurationRecoveryReadLease
              (⟨B, .recovery⟩ : BankTrialLocalState q)) := by
                rw [bankTrialDurationRecoveryClockWaitOfFront
                  _ hfrontNext hnewmode, hrank, hlease]
        _ = bankTrialDurationRecoveryClockNext
            (compileAdvice q).b root
            (Counter.site ring root (n - 1))
            (bankTrialDurationRecoveryNominated ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q))
            (Counter.site ring root j.val)
            (bankTrialDurationRecoveryClockOf
              (⟨B, .recovery⟩ : BankTrialLocalState q)) := by
                rw [bankTrialDurationRecoveryClockWaitOfFront
                  _ hf hm, hclockStep]

/-- Class (3), every genuine non-top nominated F_j service,
1 ≤ j < b, creates F_(j+1) and decreases the exact read-off rank. -/
theorem bankTrialDurationRecoveryNominatedOutwardRow {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RWAIT)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hout : BankTrialLocalFrontOut q z.bank j.val) :
    (bankTrialLocalTerminal
        (bankTrialLocalNext ring root z
          (Counter.site ring root j.val)) ∨
      BankTrialDurationRecoveryFront q
        (bankTrialLocalNext ring root z
          (Counter.site ring root j.val))) ∧
    bankTrialDurationRecoveryClockOf
        (bankTrialLocalNext ring root z
          (Counter.site ring root j.val)) =
      bankTrialDurationRecoveryClockNext
        (compileAdvice q).b root
        (Counter.site ring root (n - 1))
        (bankTrialDurationRecoveryNominated ring root z)
        (Counter.site ring root j.val)
        (bankTrialDurationRecoveryClockOf z) := by
  have hn : 2 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    omega
  cases z with
  | mk B phase =>
      cases hf.1
      have hpair := bankTrialLocalOutwardAdvancePair
        ring root (Counter.site ring root j.val) hn B
        hf.2.2.1 j.val hout j.isLt rfl
      have hfront :
          BankTrialLocalFrontOut q
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B (Counter.site ring root j.val))
            (j.val + 1) := by
        refine ⟨(by omega), (by omega), hpair.2.1, hpair.2.2, ?_⟩
        intro i hi hij hib
        by_cases hsame : i = j.val
        · subst i
          exact hpair.1
        · exact bankTrialLocalOutwardPrefixSafe
            ring root (Counter.site ring root j.val) hn
            B hf.2.2.1 hm j.val i hout hi
            (by omega) hib (Or.inl j.isLt)
      have hnextFront :
          BankTrialLocalFrontOut q
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q)
              (Counter.site ring root j.val)).bank
            (j.val + 1) := by
        rw [bankTrialLocalNextRecoveryBank]
        exact hfront
      have hvalid :
          Counter.resetClockValid (compileAdvice q).b
            (.outward (j.val + 1)) := by
        change 1 ≤ j.val + 1 ∧ j.val + 1 ≤ (compileAdvice q).b
        omega
      have hrank :
          bankTrialDurationRecoveryReadRank
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q)
              (Counter.site ring root j.val)) =
          bankTrialDurationRecoveryReadRank
            (⟨B, .recovery⟩ : BankTrialLocalState q) - 1 := by
        rw [bankTrialDurationRecoveryReadRankOut
            _ (j.val + 1) hnextFront,
          bankTrialDurationRecoveryReadRankOut
            _ j.val hout]
        change 2 * (compileAdvice q).b - (j.val + 1) =
          (2 * (compileAdvice q).b - j.val) - 1
        omega
      have hchosen :
          bankTrialDurationRecoveryNominated ring root
            (⟨B, .recovery⟩ : BankTrialLocalState q) =
          Counter.site ring root j.val := by
        unfold bankTrialDurationRecoveryNominated
        rw [bankTrialDurationRecoveryReadStageOut
          (⟨B, .recovery⟩ : BankTrialLocalState q) j.val hout]
        simp [Counter.resetClockNominated, j.isLt]
      exact bankTrialDurationRecoveryNominatedInteriorOfStage
        ring root hw
        (⟨B, .recovery⟩ : BankTrialLocalState q)
        hf hm j hj (.outward (j.val + 1))
        hvalid hnextFront hrank hchosen


/-- A certified return front has no extra RL token: if a
distinct location is RL, it must be the G-front location. -/
private theorem bankTrialDurationRecoveryBackTokenLocation {q : Nat}
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (j k : Nat) (hjb : j ≤ (compileAdvice q).b)
    (hjpos : 1 ≤ j)
    (hjtok :
      (B.fields ⟨j, Nat.lt_succ_of_le hjb⟩).2.2.1 = .RL)
    (hk : BankTrialLocalFrontBack q B k) :
    k = j := by
  obtain ⟨_, _, _, _, hother⟩ := hk
  by_cases heq : j = k
  · exact heq.symm
  · have he := (hother j hjpos hjb heq).2
    rw [hjtok] at he
    cases he

/-- Class (3), every nominated G_j return edge (j>1) produces
the full G_(j-1) array, preserving lease and losing one rank. -/
theorem bankTrialDurationRecoveryNominatedReturningRow {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RWAIT)
    (j : Nat) (hj : 1 < j)
    (hback : BankTrialLocalFrontBack q z.bank j) :
    (bankTrialLocalTerminal
        (bankTrialLocalNext ring root z
          (Counter.site ring root (j - 1))) ∨
      BankTrialDurationRecoveryFront q
        (bankTrialLocalNext ring root z
          (Counter.site ring root (j - 1)))) ∧
    bankTrialDurationRecoveryClockOf
        (bankTrialLocalNext ring root z
          (Counter.site ring root (j - 1))) =
      bankTrialDurationRecoveryClockNext
        (compileAdvice q).b root
        (Counter.site ring root (n - 1))
        (bankTrialDurationRecoveryNominated ring root z)
        (Counter.site ring root (j - 1))
        (bankTrialDurationRecoveryClockOf z) := by
  have hn : 2 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    omega
  cases z with
  | mk B phase =>
      cases hf.1
      have hbound : j ≤ (compileAdvice q).b := hback.choose
      have hpair := bankTrialLocalReturnRetreatPair
        ring root (Counter.site ring root (j - 1))
        hn B hf.2.2.1 j hback hj rfl
      obtain ⟨k, hk⟩ :=
        bankTrialLocalReturnArrayStep
          ring root (Counter.site ring root (j - 1))
          hn B hf.2.2.1 hm j hback hj
      have hkEq : k = j - 1 := by
        apply bankTrialDurationRecoveryBackTokenLocation
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root (j - 1)))
          (j - 1) k (by omega) (by omega)
        · exact hpair.1.2
        · exact hk
      have hfront :
          BankTrialLocalFrontBack q
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B (Counter.site ring root (j - 1)))
            (j - 1) := by
        rw [hkEq] at hk
        exact hk
      have hnextFront :
          BankTrialLocalFrontBack q
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q)
              (Counter.site ring root (j - 1))).bank
            (j - 1) := by
        rw [bankTrialLocalNextRecoveryBank]
        exact hfront
      have hvalid :
          Counter.resetClockValid (compileAdvice q).b
            (.returning (j - 1)) := by
        change 1 ≤ j - 1 ∧ j - 1 ≤ (compileAdvice q).b
        omega
      have hrank :
          bankTrialDurationRecoveryReadRank
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q)
              (Counter.site ring root (j - 1))) =
          bankTrialDurationRecoveryReadRank
            (⟨B, .recovery⟩ : BankTrialLocalState q) - 1 := by
        rw [bankTrialDurationRecoveryReadRankBack
            _ (j - 1) hnextFront,
          bankTrialDurationRecoveryReadRankBack _ j hback]
        rfl
      have hchosen :
          bankTrialDurationRecoveryNominated ring root
            (⟨B, .recovery⟩ : BankTrialLocalState q) =
          Counter.site ring root (j - 1) := by
        unfold bankTrialDurationRecoveryNominated
        rw [bankTrialDurationRecoveryReadStageBack
          (⟨B, .recovery⟩ : BankTrialLocalState q) j hback]
        simp [Counter.resetClockNominated, hj]
      exact bankTrialDurationRecoveryNominatedInteriorOfStage
        ring root hw
        (⟨B, .recovery⟩ : BankTrialLocalState q)
        hf hm
        ⟨j - 1, (show j - 1 < (compileAdvice q).b by omega)⟩
        (show 0 < j - 1 by omega)
        (.returning (j - 1))
        hvalid hnextFront hrank hchosen

theorem bankTrialDurationRecoveryWaitingFrameRow {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RWAIT)
    (hrootFrame :
      (bankTrialLocalNext ring root z e).bank.fields
        ⟨0, by omega⟩ = z.bank.fields ⟨0, by omega⟩)
    (stage : Counter.ResetClockStage)
    (hvalid : Counter.resetClockValid (compileAdvice q).b stage)
    (hold :
      match stage with
      | .outward k => BankTrialLocalFrontOut q z.bank k
      | .returning k => BankTrialLocalFrontBack q z.bank k
      | .finished => False)
    (hnew :
      match stage with
      | .outward k => BankTrialLocalFrontOut q
          (bankTrialLocalNext ring root z e).bank k
      | .returning k => BankTrialLocalFrontBack q
          (bankTrialLocalNext ring root z e).bank k
      | .finished => False)
    (hnotroot : e ≠ root)
    (hnotincoming : e ≠ Counter.site ring root (n - 1))
    (hnotchosen :
      e ≠ bankTrialDurationRecoveryNominated ring root z) :
    (bankTrialLocalTerminal (bankTrialLocalNext ring root z e) ∨
      BankTrialDurationRecoveryFront q
        (bankTrialLocalNext ring root z e)) ∧
    bankTrialDurationRecoveryClockOf
        (bankTrialLocalNext ring root z e) =
      bankTrialDurationRecoveryClockNext
        (compileAdvice q).b root
        (Counter.site ring root (n - 1))
        (bankTrialDurationRecoveryNominated ring root z)
        e (bankTrialDurationRecoveryClockOf z) := by
  cases z with
  | mk B phase =>
      cases hf.1
      have hfalseStep := bankTrialDurationRecoveryFrontNoWin
        ring root e (⟨B, .recovery⟩ : BankTrialLocalState q) hf
      have hnewMode :
          bankTrialLiveWaveRootMode
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q) e).bank =
            .RWAIT := by
        change
          ((bankTrialLocalNext ring root
            (⟨B, .recovery⟩ : BankTrialLocalState q) e).bank.fields
              ⟨0, by omega⟩).1 = .RWAIT
        rw [hrootFrame]
        exact hm
      have hstepMode :
          ((GrantBankReference.bankLocalReferenceStepClamped
            ring root B e).fields ⟨0, by omega⟩).1 = .RWAIT := by
        rw [← bankTrialLocalNextRecoveryBank]
        exact hnewMode
      have hphase := bankTrialDurationRecoveryNextPhaseAtBand (q := q)
        ring root e B hfalseStep (Or.inr hstepMode)
      have hcap := bankTrialLocalLeaseCapNext ring root e
        (⟨B, .recovery⟩ : BankTrialLocalState q) hf.2.1
      have hfalse :
          (bankTrialLocalNext ring root
            (⟨B, .recovery⟩ : BankTrialLocalState q) e).bank.success =
              false := by
        rw [bankTrialLocalNextRecoveryBank]
        exact hfalseStep
      have hlease :
          bankTrialDurationRecoveryReadLease
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q) e) =
          bankTrialDurationRecoveryReadLease
            (⟨B, .recovery⟩ : BankTrialLocalState q) := by
        unfold bankTrialDurationRecoveryReadLease
        rw [hrootFrame]
      have hpositive :
          1 ≤ bankTrialDurationRecoveryReadLease
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q) e) := by
        rw [hlease]
        exact bankTrialDurationRecoveryWaitLeasePositive
          (⟨B, .recovery⟩ : BankTrialLocalState q) hf hm
      have hfrontNext :
          BankTrialDurationRecoveryFront q
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q) e) := by
        refine ⟨hphase, hcap, hfalse, ?_⟩
        right
        refine ⟨?_, ?_, stage, ?_, ?_⟩
        · exact hnewMode
        · exact hpositive
        · exact hvalid
        · cases stage with
          | outward k =>
              exact hnew
          | returning k =>
              exact hnew
          | finished =>
              exact False.elim hnew
      have hrank :
          bankTrialDurationRecoveryReadRank
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q) e) =
          bankTrialDurationRecoveryReadRank
            (⟨B, .recovery⟩ : BankTrialLocalState q) := by
        cases stage with
        | outward k =>
            rw [bankTrialDurationRecoveryReadRankOut _ k hnew,
              bankTrialDurationRecoveryReadRankOut _ k hold]
        | returning k =>
            rw [bankTrialDurationRecoveryReadRankBack _ k hnew,
              bankTrialDurationRecoveryReadRankBack _ k hold]
        | finished =>
            exact False.elim hold
      refine ⟨Or.inr hfrontNext, ?_⟩
      calc
        bankTrialDurationRecoveryClockOf
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q) e) =
          bankTrialDurationRecoveryClockOf
            (⟨B, .recovery⟩ : BankTrialLocalState q) := by
              rw [bankTrialDurationRecoveryClockWaitOfFront
                _ hfrontNext hnewMode,
                bankTrialDurationRecoveryClockWaitOfFront _ hf hm,
                hrank, hlease]
        _ = bankTrialDurationRecoveryClockNext
            (compileAdvice q).b root
            (Counter.site ring root (n - 1))
            (bankTrialDurationRecoveryNominated ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q))
            e (bankTrialDurationRecoveryClockOf
              (⟨B, .recovery⟩ : BankTrialLocalState q)) :=
          (bankTrialDurationRecoveryClockNextAway
            (compileAdvice q).b root
            (Counter.site ring root (n - 1))
            (bankTrialDurationRecoveryNominated ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q))
            e hnotroot hnotincoming hnotchosen
            (bankTrialDurationRecoveryClockOf
              (⟨B, .recovery⟩ : BankTrialLocalState q))).symm

/-- The top unary edge neither starts at root nor enters root
under the nonalias window hypothesis. -/
private theorem bankTrialDurationRecoveryTopNotRootIncident {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q) :
    Counter.site ring root (compileAdvice q).b ≠ root ∧
      Counter.site ring root (compileAdvice q).b ≠
        Counter.site ring root (n - 1) := by
  have hb : 1 < (compileAdvice q).b :=
    bankTrialDurationRecoveryWidthLarge q
  have hleft :
      Counter.site ring root (compileAdvice q).b ≠ root := by
    intro he
    have hh := bankTrialWindowSitesDistinct ring root hw
      (compileAdvice q).b 0 (by omega) (by omega)
      (show Counter.site ring root (compileAdvice q).b =
        Counter.site ring root 0 from he)
    omega
  have hright :
      ring.rightNeighbor
        (Counter.site ring root (compileAdvice q).b) ≠ root := by
    intro he
    have hh := bankTrialWindowSitesDistinct ring root hw
      ((compileAdvice q).b + 1) 0 (by omega) (by omega)
      (show Counter.site ring root ((compileAdvice q).b + 1) =
        Counter.site ring root 0 from he)
    omega
  refine ⟨hleft, ?_⟩
  intro he
  apply hright
  rw [he]
  exact bankTrialDurationRecoveryLastIncoming ring root

/-- The top unary service is distinct from every RWAIT F/G
nominated edge. In F_b the designated edge is b-1. -/
private theorem bankTrialDurationRecoveryTopNotChosen {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RWAIT) :
    Counter.site ring root (compileAdvice q).b ≠
      bankTrialDurationRecoveryNominated ring root z := by
  rcases hf.2.2.2 with hr | ⟨_, _, stage, hvalid, hstage⟩
  · cases (hm.symm.trans hr.1)
  cases stage with
  | outward j =>
      obtain ⟨hpos, hbound⟩ := hvalid
      unfold bankTrialDurationRecoveryNominated
      rw [bankTrialDurationRecoveryReadStageOut z j hstage]
      by_cases hj : j < (compileAdvice q).b
      · simp only [Counter.resetClockNominated, if_pos hj]
        intro he
        have hh := bankTrialWindowSitesDistinct ring root hw
          (compileAdvice q).b j (by omega) (by omega) he
        omega
      · simp only [Counter.resetClockNominated, if_neg hj]
        intro he
        have hh := bankTrialWindowSitesDistinct ring root hw
          (compileAdvice q).b ((compileAdvice q).b - 1)
          (by omega) (by omega) he
        have hb := bankTrialDurationRecoveryWidthLarge q
        omega
  | returning j =>
      obtain ⟨hpos, hbound⟩ := hvalid
      unfold bankTrialDurationRecoveryNominated
      rw [bankTrialDurationRecoveryReadStageBack z j hstage]
      by_cases hj : 1 < j
      · simp only [Counter.resetClockNominated, if_pos hj]
        intro he
        have hh := bankTrialWindowSitesDistinct ring root hw
          (compileAdvice q).b (j - 1) (by omega) (by omega) he
        omega
      · simp only [Counter.resetClockNominated, if_neg hj]
        exact (bankTrialDurationRecoveryTopNotRootIncident
          ring root hw).1
  | finished =>
      exact False.elim hstage

/-- The unary top edge preserves any F_j front, although its
unrestricted suffix may contain IR, RR, RL or live worker tokens. -/
private theorem bankTrialDurationRecoveryTopOutFront {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (j : Nat) (hout : BankTrialLocalFrontOut q B j) :
    BankTrialLocalFrontOut q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root (compileAdvice q).b))
      j := by
  have hn : 2 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    omega
  have houtSaved := hout
  obtain ⟨hjb, hjpos, _, _, _⟩ := houtSaved
  have hnotForward : j < (compileAdvice q).b →
      Counter.site ring root (compileAdvice q).b ≠
        Counter.site ring root j := by
    intro hj he
    have hh := bankTrialWindowSitesDistinct ring root hw
      (compileAdvice q).b j (by omega) (by omega) he
    omega
  have hnotTurn : j = (compileAdvice q).b →
      Counter.site ring root (compileAdvice q).b ≠
        Counter.site ring root (j - 1) := by
    intro hj he
    have hh := bankTrialWindowSitesDistinct ring root hw
      (compileAdvice q).b (j - 1) (by omega) (by omega) he
    omega
  have hfirst := bankTrialLocalOutwardFrontSafe
    ring root (Counter.site ring root (compileAdvice q).b)
    hn B hf hm j hout hnotForward hnotTurn
  refine ⟨hjb, hjpos, hfirst.1, hfirst.2, ?_⟩
  intro i hi hij hib
  have hsafe : j < (compileAdvice q).b ∨
      Counter.site ring root (compileAdvice q).b ≠
        Counter.site ring root (j - 1) := by
    by_cases hlt : j < (compileAdvice q).b
    · exact Or.inl hlt
    · have htop : j = (compileAdvice q).b := by omega
      exact Or.inr (hnotTurn htop)
  exact bankTrialLocalOutwardPrefixSafe ring root
    (Counter.site ring root (compileAdvice q).b)
    hn B hf hm j i hout hi hij hib hsafe

/-- The unary top edge preserves each returning G_j front.
The G_1 case is handled by its own non-root digit-frame rows. -/
private theorem bankTrialDurationRecoveryTopBackFront {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (j : Nat) (hback : BankTrialLocalFrontBack q B j) :
    BankTrialLocalFrontBack q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root (compileAdvice q).b))
      j := by
  have hn : 2 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    omega
  have hnotroot := (bankTrialDurationRecoveryTopNotRootIncident
    ring root hw).1
  by_cases hj : j = 1
  · subst j
    have hfirst := bankTrialLocalGOneDigitOneOff
      ring root (Counter.site ring root (compileAdvice q).b)
      hn B hf hback hnotroot
    have hbound : 1 ≤ (compileAdvice q).b :=
      Nat.le_of_lt (bankTrialDurationRecoveryWidthLarge q)
    refine ⟨hbound, Nat.le_refl _, hfirst.1, hfirst.2, ?_⟩
    intro i hi hib hneq
    exact bankTrialLocalGOneAllOtherDigits ring root
      (Counter.site ring root (compileAdvice q).b)
      hn B hf hback i (by omega) hib
  · have hjbound : j ≤ (compileAdvice q).b := hback.choose
    have hjpos : 1 ≤ j := hback.choose_spec.1
    have hjmore : 1 < j := by omega
    have hnotchosen :
        Counter.site ring root (compileAdvice q).b ≠
          Counter.site ring root (j - 1) := by
      intro he
      have hh := bankTrialWindowSitesDistinct ring root hw
        (compileAdvice q).b (j - 1)
        (by omega) (by omega) he
      omega
    have hfrontData := bankTrialLocalReturnFrontSafe
      ring root (Counter.site ring root (compileAdvice q).b)
      hn B hf j hback hnotchosen
    obtain ⟨k, hk⟩ := bankTrialLocalReturnArrayStep
      ring root (Counter.site ring root (compileAdvice q).b)
      hn B hf hm j hback hjmore
    have hkEq : k = j := by
      apply bankTrialDurationRecoveryBackTokenLocation
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root (compileAdvice q).b))
        j k hjbound hjpos
      · exact hfrontData.2
      · exact hk
    rw [hkEq] at hk
    exact hk

theorem bankTrialDurationRecoveryTopUnaryRow {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RWAIT) :
    (bankTrialLocalTerminal
        (bankTrialLocalNext ring root z
          (Counter.site ring root (compileAdvice q).b)) ∨
      BankTrialDurationRecoveryFront q
        (bankTrialLocalNext ring root z
          (Counter.site ring root (compileAdvice q).b))) ∧
    bankTrialDurationRecoveryClockOf
        (bankTrialLocalNext ring root z
          (Counter.site ring root (compileAdvice q).b)) =
      bankTrialDurationRecoveryClockNext
        (compileAdvice q).b root
        (Counter.site ring root (n - 1))
        (bankTrialDurationRecoveryNominated ring root z)
        (Counter.site ring root (compileAdvice q).b)
        (bankTrialDurationRecoveryClockOf z) := by
  have hports := bankTrialDurationRecoveryTopNotRootIncident
    ring root hw
  have hnotchosen := bankTrialDurationRecoveryTopNotChosen
    ring root hw z hf hm
  cases z with
  | mk B phase =>
      cases hf.1
      have hfields := bankTrialDurationTopFieldsRow ring root hw
        B hf.2.2.1
      have hrootFrame :
          (bankTrialLocalNext ring root
            (⟨B, .recovery⟩ : BankTrialLocalState q)
            (Counter.site ring root (compileAdvice q).b)).bank.fields
              ⟨0, by omega⟩ = B.fields ⟨0, by omega⟩ := by
        rw [bankTrialLocalNextRecoveryBank, hfields]
        have hne : (0 : Nat) ≠ (compileAdvice q).b := by
          have hb := bankTrialDurationRecoveryWidthLarge q
          omega
        simp only [Fin.val_mk, if_neg hne]
      rcases hf.2.2.2 with hr | ⟨_, _, stage, hvalid, hstage⟩
      · cases (hm.symm.trans hr.1)
      have hstageNew :
          match stage with
          | .outward k => BankTrialLocalFrontOut q
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q)
                (Counter.site ring root (compileAdvice q).b)).bank k
          | .returning k => BankTrialLocalFrontBack q
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q)
                (Counter.site ring root (compileAdvice q).b)).bank k
          | .finished => False := by
        rw [bankTrialLocalNextRecoveryBank]
        cases stage with
        | outward k =>
            exact bankTrialDurationRecoveryTopOutFront
              ring root hw B hf.2.2.1 hm k hstage
        | returning k =>
            exact bankTrialDurationRecoveryTopBackFront
              ring root hw B hf.2.2.1 hm k hstage
        | finished =>
            exact False.elim hstage
      have hchosenDifferent :
          Counter.site ring root (compileAdvice q).b ≠
            bankTrialDurationRecoveryNominated ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q) := by
        exact bankTrialDurationRecoveryTopNotChosen (q := q) ring root hw
          (⟨B, .recovery⟩ : BankTrialLocalState q) hf hm
      refine bankTrialDurationRecoveryWaitingFrameRow (q := q)
        ring root (Counter.site ring root (compileAdvice q).b)
        (⟨B, .recovery⟩ : BankTrialLocalState q)
        ?_ ?_ ?_ stage ?_ ?_ ?_ ?_ ?_ ?_
      · exact hf
      · exact hm
      · exact hrootFrame
      · exact hvalid
      · cases stage with
        | outward k =>
            exact hstage
        | returning k =>
            exact hstage
        | finished =>
            exact False.elim hstage
      · cases stage with
        | outward k => exact hstageNew
        | returning k => exact hstageNew
        | finished => exact hstageNew
      · exact hports.1
      · exact hports.2
      · exact hchosenDifferent

/-- Distinctness of the root from any positive digit edge,
derived from the same b+2 nonalias window. -/
private theorem bankTrialDurationRecoveryPositiveSiteNotRoot {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (j : Nat) (hj : 1 ≤ j) (hjb : j ≤ (compileAdvice q).b) :
    Counter.site ring root j ≠ root := by
  intro he
  have hh := bankTrialWindowSitesDistinct ring root hw
    j 0 (by omega) (by omega)
    (show Counter.site ring root j = Counter.site ring root 0 from he)
  omega

/-- The root-outgoing edge cannot consume a non-final F/G
front. The G_1 return is separately terminal and excluded. -/
private theorem bankTrialDurationRecoveryRootNotChosen {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RWAIT)
    (hrank :
      bankTrialDurationRecoveryReadRank z ≠ 1) :
    root ≠ bankTrialDurationRecoveryNominated ring root z := by
  rcases hf.2.2.2 with hr | ⟨_, _, stage, hvalid, hstage⟩
  · cases (hm.symm.trans hr.1)
  cases stage with
  | outward j =>
      obtain ⟨hpos, hbound⟩ := hvalid
      unfold bankTrialDurationRecoveryNominated
      rw [bankTrialDurationRecoveryReadStageOut z j hstage]
      by_cases hj : j < (compileAdvice q).b
      · simp only [Counter.resetClockNominated, if_pos hj]
        exact (bankTrialDurationRecoveryPositiveSiteNotRoot
          ring root hw j hpos hbound).symm
      · simp only [Counter.resetClockNominated, if_neg hj]
        have hb := bankTrialDurationRecoveryWidthLarge q
        exact (bankTrialDurationRecoveryPositiveSiteNotRoot
          ring root hw ((compileAdvice q).b - 1)
          (by omega) (by omega)).symm
  | returning j =>
      obtain ⟨hpos, hbound⟩ := hvalid
      have hnotone : j ≠ 1 := by
        intro he
        subst j
        apply hrank
        rw [bankTrialDurationRecoveryReadRankBack z 1 hstage]
        rfl
      have hmore : 1 < j := by omega
      unfold bankTrialDurationRecoveryNominated
      rw [bankTrialDurationRecoveryReadStageBack z j hstage]
      simp only [Counter.resetClockNominated, if_pos hmore]
      exact (bankTrialDurationRecoveryPositiveSiteNotRoot
        ring root hw (j - 1) (by omega) (by omega)).symm
  | finished =>
      exact False.elim hstage

/-- The root-outgoing service preserves F_j for every j,
because the nominated F-edge is not the root. This also holds
when F_j has arbitrary suffix fields. -/
private theorem bankTrialDurationRecoveryRootOutFront {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (j : Nat) (hout : BankTrialLocalFrontOut q B j) :
    BankTrialLocalFrontOut q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root) j := by
  have hn : 2 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    omega
  have houtSaved := hout
  obtain ⟨hjb, hjpos, _, _, _⟩ := houtSaved
  have hnotForward : j < (compileAdvice q).b →
      root ≠ Counter.site ring root j := by
    intro hj
    exact (bankTrialDurationRecoveryPositiveSiteNotRoot
      ring root hw j hjpos hjb).symm
  have hnotTurn : j = (compileAdvice q).b →
      root ≠ Counter.site ring root (j - 1) := by
    intro htop
    have hb := bankTrialDurationRecoveryWidthLarge q
    exact (bankTrialDurationRecoveryPositiveSiteNotRoot
      ring root hw (j - 1) (by omega) (by omega)).symm
  have hfront := bankTrialLocalOutwardFrontSafe
    ring root root hn B hf hm j hout hnotForward hnotTurn
  refine ⟨hjb, hjpos, hfront.1, hfront.2, ?_⟩
  intro i hi hij hib
  have hsafe : j < (compileAdvice q).b ∨
      root ≠ Counter.site ring root (j - 1) := by
    by_cases hlt : j < (compileAdvice q).b
    · exact Or.inl hlt
    · have heq : j = (compileAdvice q).b := by omega
      exact Or.inr (hnotTurn heq)
  exact bankTrialLocalOutwardPrefixSafe ring root root
    hn B hf hm j i hout hi hij hib hsafe

/-- Root-outgoing preserves G_j for j>1. The separate G_1
root service is the terminal LOST transition. -/
private theorem bankTrialDurationRecoveryRootBackFront {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (j : Nat) (hj : 1 < j)
    (hback : BankTrialLocalFrontBack q B j) :
    BankTrialLocalFrontBack q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root) j := by
  have hn : 2 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    omega
  have hjbound : j ≤ (compileAdvice q).b := hback.choose
  have hnotchosen : root ≠ Counter.site ring root (j - 1) :=
    (bankTrialDurationRecoveryPositiveSiteNotRoot
      ring root hw (j - 1) (by omega) (by omega)).symm
  have hdata := bankTrialLocalReturnFrontSafe
    ring root root hn B hf j hback hnotchosen
  obtain ⟨k, hk⟩ := bankTrialLocalReturnArrayStep
    ring root root hn B hf hm j hback hj
  have hkeq : k = j := by
    apply bankTrialDurationRecoveryBackTokenLocation
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root)
      j k hjbound (by omega) hdata.2 hk
  rw [hkeq] at hk
  exact hk

/-- Root-outgoing RWAIT non-final stages preserve their exact
front stage: the only productive root service is G_1. -/
private theorem bankTrialDurationRecoveryRootStageSafe {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (stage : Counter.ResetClockStage)
    (hvalid : Counter.resetClockValid (compileAdvice q).b stage)
    (hold :
      match stage with
      | .outward j => BankTrialLocalFrontOut q B j
      | .returning j => BankTrialLocalFrontBack q B j
      | .finished => False)
    (hrank :
      Counter.resetClockRank (compileAdvice q).b stage ≠ 1) :
    (match stage with
      | .outward j => BankTrialLocalFrontOut q
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B root) j
      | .returning j => BankTrialLocalFrontBack q
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B root) j
      | .finished => False) := by
  cases stage with
  | outward j =>
      exact bankTrialDurationRecoveryRootOutFront
        ring root hw B hf hm j hold
  | returning j =>
      have hj : 1 < j := by
        have hv : 1 ≤ j := hvalid.1
        change j ≠ 1 at hrank
        omega
      exact bankTrialDurationRecoveryRootBackFront
        ring root hw B hf hm j hj hold
  | finished =>
      exact False.elim hold


theorem bankTrialDurationRecoveryRootWatchdogRow {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RWAIT)
    (hnonfinal : bankTrialDurationRecoveryReadRank z ≠ 1) :
    (bankTrialLocalTerminal (bankTrialLocalNext ring root z root) ∨
      BankTrialDurationRecoveryFront q
        (bankTrialLocalNext ring root z root)) ∧
    bankTrialDurationRecoveryClockOf
        (bankTrialLocalNext ring root z root) =
      bankTrialDurationRecoveryClockNext
        (compileAdvice q).b root
        (Counter.site ring root (n - 1))
        (bankTrialDurationRecoveryNominated ring root z)
        root (bankTrialDurationRecoveryClockOf z) := by
  have hnotchosen := bankTrialDurationRecoveryRootNotChosen (q := q)
    ring root hw z hf hm hnonfinal
  have hfirstGuard :
      ¬ (bankTrialDurationRecoveryReadRank z = 1 ∧ root = root) := by
    intro h
    exact hnonfinal h.1
  have hrootor :
      root = root ∨ root = Counter.site ring root (n - 1) :=
    Or.inl rfl
  cases z with
  | mk B phase =>
      cases hf.1
      rcases hf.2.2.2 with hr | ⟨_, _, stage, hvalid, hstage⟩
      · cases (hm.symm.trans hr.1)
      have hstageRank :
          Counter.resetClockRank (compileAdvice q).b stage ≠ 1 := by
        cases stage with
        | outward j =>
            rw [bankTrialDurationRecoveryReadRankOut
              (⟨B, .recovery⟩ : BankTrialLocalState q) j hstage]
              at hnonfinal
            exact hnonfinal
        | returning j =>
            rw [bankTrialDurationRecoveryReadRankBack
              (⟨B, .recovery⟩ : BankTrialLocalState q) j hstage]
              at hnonfinal
            exact hnonfinal
        | finished =>
            exact False.elim hstage
      have hfirstIndex : 1 ≤ (compileAdvice q).b :=
        Nat.le_of_lt (bankTrialDurationRecoveryWidthLarge q)
      have hfirst :
          (B.fields ⟨1, Nat.lt_succ_of_le hfirstIndex⟩).2.2.1 = .E ∨
          (B.fields ⟨1, Nat.lt_succ_of_le hfirstIndex⟩).2.2.1 = .RR := by
        cases stage with
        | outward j =>
            exact bankTrialLocalFrontOutFirstToken B j hstage
        | returning j =>
            have hj : 1 < j := by
              have hv := hvalid.1
              change j ≠ 1 at hstageRank
              omega
            exact Or.inl
              (bankTrialLocalFrontBackFirstEmpty B j hstage hj)
        | finished =>
            exact False.elim hstage
      have hnextStage :
          match stage with
          | .outward j => BankTrialLocalFrontOut q
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q) root).bank j
          | .returning j => BankTrialLocalFrontBack q
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q) root).bank j
          | .finished => False := by
        rw [bankTrialLocalNextRecoveryBank]
        cases stage with
        | outward k =>
            exact bankTrialDurationRecoveryRootStageSafe (q := q)
              ring root hw B hf.2.2.1 hm (.outward k)
              hvalid hstage hstageRank
        | returning k =>
            exact bankTrialDurationRecoveryRootStageSafe (q := q)
              ring root hw B hf.2.2.1 hm (.returning k)
              hvalid hstage hstageRank
        | finished =>
            exact False.elim hstage
      have hfirstRaw :
          (B.fields
            ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 = .E ∨
          (B.fields
            ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 = .RR := by
        exact hfirst
      have hmodeRaw := bankTrialLocalRootOutgoingWaitMode (q := q)
        ring root B hf.2.2.1 hm hfirstRaw
      have hleaseRaw := bankTrialLocalRootOutgoingWaitLease (q := q)
        ring root B hf.2.2.1 hf.2.1 hm hfirstRaw
      have hfalseStep := bankTrialDurationRecoveryFrontNoWin
        ring root root
        (⟨B, .recovery⟩ : BankTrialLocalState q) hf
      have hcap := bankTrialLocalLeaseCapNext ring root root
        (⟨B, .recovery⟩ : BankTrialLocalState q) hf.2.1
      have hfalse :
          (bankTrialLocalNext ring root
            (⟨B, .recovery⟩ : BankTrialLocalState q) root).bank.success =
            false := by
        rw [bankTrialLocalNextRecoveryBank]
        exact hfalseStep
      have hrankFrame :
          bankTrialDurationRecoveryReadRank
            (bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q) root) =
          bankTrialDurationRecoveryReadRank
            (⟨B, .recovery⟩ : BankTrialLocalState q) := by
        cases stage with
        | outward j =>
            rw [bankTrialDurationRecoveryReadRankOut _ j hnextStage,
              bankTrialDurationRecoveryReadRankOut _ j hstage]
        | returning j =>
            rw [bankTrialDurationRecoveryReadRankBack _ j hnextStage,
              bankTrialDurationRecoveryReadRankBack _ j hstage]
        | finished =>
            exact False.elim hstage
      by_cases hl : 1 <
          bankTrialDurationRecoveryReadLease
            (⟨B, .recovery⟩ : BankTrialLocalState q)
      · have hmodeStep :
            ((GrantBankReference.bankLocalReferenceStepClamped
              ring root B root).fields ⟨0, by omega⟩).1 = .RWAIT := by
          rw [hmodeRaw]
          change Counter.resetClockWaitMode
            (bankTrialDurationRecoveryReadLease
              (⟨B, .recovery⟩ : BankTrialLocalState q)) = .RWAIT
          simp [Counter.resetClockWaitMode, hl]
        have hleaseStep :
            ((GrantBankReference.bankLocalReferenceStepClamped
              ring root B root).fields ⟨0, by omega⟩).2.2.2 =
            bankTrialDurationRecoveryReadLease
              (⟨B, .recovery⟩ : BankTrialLocalState q) - 1 := by
          rw [hleaseRaw]
          change Counter.resetClockWaitLease
            (bankTrialDurationRecoveryReadLease
              (⟨B, .recovery⟩ : BankTrialLocalState q)) =
            bankTrialDurationRecoveryReadLease
              (⟨B, .recovery⟩ : BankTrialLocalState q) - 1
          simp [Counter.resetClockWaitLease, hl]
        have hphase := bankTrialDurationRecoveryNextPhaseAtBand (q := q)
          ring root root B hfalseStep (Or.inr hmodeStep)
        have hnewmode :
            bankTrialLiveWaveRootMode
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q) root).bank =
              .RWAIT := by
          rw [bankTrialLocalNextRecoveryBank]
          exact hmodeStep
        have hleaseNext :
            bankTrialDurationRecoveryReadLease
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q) root) =
            bankTrialDurationRecoveryReadLease
              (⟨B, .recovery⟩ : BankTrialLocalState q) - 1 := by
          unfold bankTrialDurationRecoveryReadLease
          rw [bankTrialLocalNextRecoveryBank]
          exact hleaseStep
        have hpositive :
            1 ≤ bankTrialDurationRecoveryReadLease
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q) root) := by
          rw [hleaseNext]
          omega
        have hfrontNext :
            BankTrialDurationRecoveryFront q
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q) root) := by
          refine ⟨hphase, hcap, hfalse, ?_⟩
          right
          refine ⟨?_, ?_, stage, ?_, ?_⟩
          · exact hnewmode
          · exact hpositive
          · exact hvalid
          · cases stage with
            | outward k =>
                exact hnextStage
            | returning k =>
                exact hnextStage
            | finished =>
                exact False.elim hnextStage
        have hgt :
            ¬ bankTrialDurationRecoveryReadLease
              (⟨B, .recovery⟩ : BankTrialLocalState q) ≤ 1 := by
          omega
        have hclockStep :
            bankTrialDurationRecoveryClockNext
              (compileAdvice q).b root
              (Counter.site ring root (n - 1))
              (bankTrialDurationRecoveryNominated ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q))
              root (.waiting
                (bankTrialDurationRecoveryReadRank
                  (⟨B, .recovery⟩ : BankTrialLocalState q))
                (bankTrialDurationRecoveryReadLease
                  (⟨B, .recovery⟩ : BankTrialLocalState q))) =
            .waiting
              (bankTrialDurationRecoveryReadRank
                (⟨B, .recovery⟩ : BankTrialLocalState q))
              (bankTrialDurationRecoveryReadLease
                (⟨B, .recovery⟩ : BankTrialLocalState q) - 1) := by
          simp [bankTrialDurationRecoveryClockNext,
            hnonfinal, hnotchosen, hgt]
        refine ⟨Or.inr hfrontNext, ?_⟩
        calc
          bankTrialDurationRecoveryClockOf
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q) root) =
            .waiting
              (bankTrialDurationRecoveryReadRank
                (⟨B, .recovery⟩ : BankTrialLocalState q))
              (bankTrialDurationRecoveryReadLease
                (⟨B, .recovery⟩ : BankTrialLocalState q) - 1) := by
                  rw [bankTrialDurationRecoveryClockWaitOfFront
                    _ hfrontNext hnewmode, hrankFrame, hleaseNext]
          _ = bankTrialDurationRecoveryClockNext
              (compileAdvice q).b root
              (Counter.site ring root (n - 1))
              (bankTrialDurationRecoveryNominated ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q))
              root (bankTrialDurationRecoveryClockOf
                (⟨B, .recovery⟩ : BankTrialLocalState q)) := by
                  rw [bankTrialDurationRecoveryClockWaitOfFront
                    _ hf hm, hclockStep]
      · have hle :
            bankTrialDurationRecoveryReadLease
              (⟨B, .recovery⟩ : BankTrialLocalState q) ≤ 1 := by
          omega
        have hmodeStep :
            ((GrantBankReference.bankLocalReferenceStepClamped
              ring root B root).fields ⟨0, by omega⟩).1 = .RESET := by
          rw [hmodeRaw]
          change Counter.resetClockWaitMode
            (bankTrialDurationRecoveryReadLease
              (⟨B, .recovery⟩ : BankTrialLocalState q)) = .RESET
          simp [Counter.resetClockWaitMode, hl]
        have hleaseStep :
            ((GrantBankReference.bankLocalReferenceStepClamped
              ring root B root).fields ⟨0, by omega⟩).2.2.2 = 0 := by
          rw [hleaseRaw]
          change Counter.resetClockWaitLease
            (bankTrialDurationRecoveryReadLease
              (⟨B, .recovery⟩ : BankTrialLocalState q)) = 0
          simp [Counter.resetClockWaitLease, hl]
        have hphase := bankTrialDurationRecoveryNextPhaseAtBand (q := q)
          ring root root B hfalseStep (Or.inl hmodeStep)
        have hnewmode :
            bankTrialLiveWaveRootMode
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q) root).bank =
              .RESET := by
          rw [bankTrialLocalNextRecoveryBank]
          exact hmodeStep
        have hleaseNext :
            ((bankTrialLocalNext ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q) root).bank.fields
              ⟨0, by omega⟩).2.2.2 = 0 := by
          rw [bankTrialLocalNextRecoveryBank]
          exact hleaseStep
        have hfrontNext :
            BankTrialDurationRecoveryFront q
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q) root) :=
          ⟨hphase, hcap, hfalse,
            Or.inl ⟨hnewmode, hleaseNext⟩⟩
        have hclockStep :
            bankTrialDurationRecoveryClockNext
              (compileAdvice q).b root
              (Counter.site ring root (n - 1))
              (bankTrialDurationRecoveryNominated ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q))
              root (.waiting
                (bankTrialDurationRecoveryReadRank
                  (⟨B, .recovery⟩ : BankTrialLocalState q))
                (bankTrialDurationRecoveryReadLease
                  (⟨B, .recovery⟩ : BankTrialLocalState q))) =
              .reset := by
          simp [bankTrialDurationRecoveryClockNext,
            hnonfinal, hnotchosen, hle]
        refine ⟨Or.inr hfrontNext, ?_⟩
        calc
          bankTrialDurationRecoveryClockOf
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q) root) =
            .reset := bankTrialDurationRecoveryClockResetOfFront
              _ hfrontNext hnewmode
          _ = bankTrialDurationRecoveryClockNext
              (compileAdvice q).b root
              (Counter.site ring root (n - 1))
              (bankTrialDurationRecoveryNominated ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q))
              root (bankTrialDurationRecoveryClockOf
                (⟨B, .recovery⟩ : BankTrialLocalState q)) := by
                  rw [bankTrialDurationRecoveryClockWaitOfFront
                    _ hf hm, hclockStep]

/-- Every non-nominated, non-root RWAIT service preserves the
authenticated F/G stage, regardless of suffix and irrespective
of whether the service is itself a protected interior edge. -/
private theorem bankTrialDurationRecoveryNonNominatedStageSafe {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .RWAIT)
    (stage : Counter.ResetClockStage)
    (hvalid : Counter.resetClockValid (compileAdvice q).b stage)
    (hold :
      match stage with
      | .outward j => BankTrialLocalFrontOut q B j
      | .returning j => BankTrialLocalFrontBack q B j
      | .finished => False)
    (hnotroot : e ≠ root)
    (hnotchosen :
      e ≠ bankTrialDurationRecoveryNominated ring root
        (⟨B, .recovery⟩ : BankTrialLocalState q)) :
    match stage with
    | .outward j => BankTrialLocalFrontOut q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) j
    | .returning j => BankTrialLocalFrontBack q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) j
    | .finished => False := by
  have hn : 2 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    omega
  cases stage with
  | outward j =>
      have holdSaved := hold
      obtain ⟨hjb, hjpos, _, _, _⟩ := holdSaved
      have hread := bankTrialDurationRecoveryReadStageOut
        (⟨B, .recovery⟩ : BankTrialLocalState q) j hold
      have hnotforward : j < (compileAdvice q).b →
          e ≠ Counter.site ring root j := by
        intro hj he
        apply hnotchosen
        unfold bankTrialDurationRecoveryNominated
        rw [hread]
        simpa only [Counter.resetClockNominated, if_pos hj]
          using he
      have hnotturn : j = (compileAdvice q).b →
          e ≠ Counter.site ring root (j - 1) := by
        intro hj he
        apply hnotchosen
        unfold bankTrialDurationRecoveryNominated
        rw [hread]
        have hnot : ¬ j < (compileAdvice q).b := by omega
        have hsite :
            e = Counter.site ring root ((compileAdvice q).b - 1) := by
          simpa only [hj] using he
        simpa only [Counter.resetClockNominated, if_neg hnot]
          using hsite
      have hfront := bankTrialLocalOutwardFrontSafe
        ring root e hn B hf hm j hold hnotforward hnotturn
      refine ⟨hjb, hjpos, hfront.1, hfront.2, ?_⟩
      intro i hi hij hib
      have hsafe : j < (compileAdvice q).b ∨
          e ≠ Counter.site ring root (j - 1) := by
        by_cases hjlt : j < (compileAdvice q).b
        · exact Or.inl hjlt
        · have htop : j = (compileAdvice q).b := by omega
          exact Or.inr (hnotturn htop)
      exact bankTrialLocalOutwardPrefixSafe
        ring root e hn B hf hm j i hold hi hij hib hsafe
  | returning j =>
      have hread := bankTrialDurationRecoveryReadStageBack
        (⟨B, .recovery⟩ : BankTrialLocalState q) j hold
      by_cases hj : j = 1
      · subst j
        have hfirst := bankTrialLocalGOneDigitOneOff
          ring root e hn B hf hold hnotroot
        have hbound : 1 ≤ (compileAdvice q).b :=
          Nat.le_of_lt (bankTrialDurationRecoveryWidthLarge q)
        refine ⟨hbound, Nat.le_refl _, hfirst.1, hfirst.2, ?_⟩
        intro i hi hib hneq
        exact bankTrialLocalGOneAllOtherDigits
          ring root e hn B hf hold i (by omega) hib
      · have hjmore : 1 < j := by
          have hpos := hvalid.1
          omega
        have hnotret :
            e ≠ Counter.site ring root (j - 1) := by
          intro he
          apply hnotchosen
          unfold bankTrialDurationRecoveryNominated
          rw [hread]
          simpa only [Counter.resetClockNominated, if_pos hjmore]
            using he
        have hfront := bankTrialLocalReturnFrontSafe
          ring root e hn B hf j hold hnotret
        obtain ⟨k, hk⟩ := bankTrialLocalReturnArrayStep
          ring root e hn B hf hm j hold hjmore
        have hbound : j ≤ (compileAdvice q).b := hold.choose
        have hkEq : k = j := by
          apply bankTrialDurationRecoveryBackTokenLocation
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B e)
            j k hbound (by omega) hfront.2 hk
        rw [hkEq] at hk
        exact hk
  | finished =>
      exact False.elim hold

theorem bankTrialDurationRecoveryInteriorStutterRow {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RWAIT)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hnotchosen :
      Counter.site ring root j.val ≠
        bankTrialDurationRecoveryNominated ring root z) :
    (bankTrialLocalTerminal
        (bankTrialLocalNext ring root z
          (Counter.site ring root j.val)) ∨
      BankTrialDurationRecoveryFront q
        (bankTrialLocalNext ring root z
          (Counter.site ring root j.val))) ∧
    bankTrialDurationRecoveryClockOf
        (bankTrialLocalNext ring root z
          (Counter.site ring root j.val)) =
      bankTrialDurationRecoveryClockNext
        (compileAdvice q).b root
        (Counter.site ring root (n - 1))
        (bankTrialDurationRecoveryNominated ring root z)
        (Counter.site ring root j.val)
        (bankTrialDurationRecoveryClockOf z) := by
  have hnotroot : Counter.site ring root j.val ≠ root :=
    bankTrialWindowInteriorNotRoot (q := q) ring root hw j hj
  have hnotarrive :=
    bankTrialDurationRecoveryDigitNotIncoming
      ring root hw j.val j.isLt
  have hnotincoming :
      Counter.site ring root j.val ≠
        Counter.site ring root (n - 1) := by
    intro he
    apply hnotarrive
    rw [he]
    exact bankTrialDurationRecoveryLastIncoming ring root
  cases z with
  | mk B phase =>
      cases hf.1
      have hrootFrame :
          (bankTrialLocalNext ring root
            (⟨B, .recovery⟩ : BankTrialLocalState q)
            (Counter.site ring root j.val)).bank.fields
              ⟨0, by omega⟩ = B.fields ⟨0, by omega⟩ := by
        rw [bankTrialLocalNextRecoveryBank]
        exact bankTrialLocalRootNonincidentFrame
          ring root (Counter.site ring root j.val)
          B hf.2.2.1 hnotroot hnotarrive
      rcases hf.2.2.2 with hr | ⟨_, _, stage, hvalid, hstage⟩
      · cases (hm.symm.trans hr.1)
      have hchosenDifferent :
          Counter.site ring root j.val ≠
            bankTrialDurationRecoveryNominated ring root
              (⟨B, .recovery⟩ : BankTrialLocalState q) := by
        exact hnotchosen
      have hstageNew :
          match stage with
          | .outward k => BankTrialLocalFrontOut q
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q)
                (Counter.site ring root j.val)).bank k
          | .returning k => BankTrialLocalFrontBack q
              (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q)
                (Counter.site ring root j.val)).bank k
          | .finished => False := by
        rw [bankTrialLocalNextRecoveryBank]
        cases stage with
        | outward k =>
            exact bankTrialDurationRecoveryNonNominatedStageSafe (q := q)
              ring root (Counter.site ring root j.val)
              hw B hf.2.2.1 hm (.outward k)
              hvalid hstage hnotroot hchosenDifferent
        | returning k =>
            exact bankTrialDurationRecoveryNonNominatedStageSafe (q := q)
              ring root (Counter.site ring root j.val)
              hw B hf.2.2.1 hm (.returning k)
              hvalid hstage hnotroot hchosenDifferent
        | finished =>
            exact False.elim hstage
      refine bankTrialDurationRecoveryWaitingFrameRow (q := q)
        ring root (Counter.site ring root j.val)
        (⟨B, .recovery⟩ : BankTrialLocalState q)
        ?_ ?_ ?_ stage ?_ ?_ ?_ ?_ ?_ ?_
      · exact hf
      · exact hm
      · exact hrootFrame
      · exact hvalid
      · cases stage with
        | outward k =>
            exact hstage
        | returning k =>
            exact hstage
        | finished =>
            exact False.elim hstage
      · cases stage with
        | outward k => exact hstageNew
        | returning k => exact hstageNew
        | finished => exact hstageNew
      · exact hnotroot
      · exact hnotincoming
      · exact hchosenDifferent

/-- All RWAIT nominated scheduler letters: F_j advances,
F_b turns at b-1, G_j retreats, and G_1 returns to LOST. -/
theorem bankTrialDurationRecoveryAnyNominatedRow {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z)
    (hm : bankTrialLiveWaveRootMode z.bank = .RWAIT)
    (he : e = bankTrialDurationRecoveryNominated ring root z) :
    (bankTrialLocalTerminal (bankTrialLocalNext ring root z e) ∨
      BankTrialDurationRecoveryFront q
        (bankTrialLocalNext ring root z e)) ∧
    bankTrialDurationRecoveryClockOf
        (bankTrialLocalNext ring root z e) =
      bankTrialDurationRecoveryClockNext
        (compileAdvice q).b root
        (Counter.site ring root (n - 1))
        (bankTrialDurationRecoveryNominated ring root z)
        e (bankTrialDurationRecoveryClockOf z) := by
  rcases hf.2.2.2 with hr | ⟨_, _, stage, hvalid, hstage⟩
  · cases (hm.symm.trans hr.1)
  cases stage with
  | outward j =>
      obtain ⟨hjpos, hjbound⟩ := hvalid
      have hread := bankTrialDurationRecoveryReadStageOut
        z j hstage
      by_cases hjlt : j < (compileAdvice q).b
      · have heq : e = Counter.site ring root j := by
          rw [he]
          unfold bankTrialDurationRecoveryNominated
          rw [hread]
          simp [Counter.resetClockNominated, hjlt]
        rw [heq]
        exact bankTrialDurationRecoveryNominatedOutwardRow
          ring root hw z hf hm ⟨j, hjlt⟩ hjpos hstage
      · have hjtop : j = (compileAdvice q).b := by omega
        have heq :
            e = Counter.site ring root ((compileAdvice q).b - 1) := by
          rw [he]
          unfold bankTrialDurationRecoveryNominated
          rw [hread]
          simp [Counter.resetClockNominated, hjtop]
        rw [heq]
        exact bankTrialDurationRecoveryTopTurnRow
          ring root hw z hf hm (by rw [← hjtop]; exact hstage)
  | returning j =>
      obtain ⟨hjpos, hjbound⟩ := hvalid
      have hread := bankTrialDurationRecoveryReadStageBack
        z j hstage
      by_cases hjone : j = 1
      · subst j
        have heq : e = root := by
          rw [he]
          unfold bankTrialDurationRecoveryNominated
          rw [hread]
          simp [Counter.resetClockNominated]
        rw [heq]
        have hn : 2 ≤ n := by
          unfold BankTrialLiveWindowNonalias at hw
          omega
        exact bankTrialDurationRecoveryFinalReturnRow
          ring root hn z hf hm hstage
      · have hjmore : 1 < j := by omega
        have heq : e = Counter.site ring root (j - 1) := by
          rw [he]
          unfold bankTrialDurationRecoveryNominated
          rw [hread]
          simp [Counter.resetClockNominated, hjmore]
        rw [heq]
        exact bankTrialDurationRecoveryNominatedReturningRow
          ring root hw z hf hm j hjmore hstage
  | finished =>
      exact False.elim hstage

/-- Assembly of every literal local RECOVERY row on the original
Fin n scheduler alphabet, under useSmall=false and the nonalias
protected-window constraint. The proof separates the root,
incoming-root, nominated, top unary, other interior, and outside
support edge classes. -/
theorem bankTrialDurationRecoveryAllRowsNonalias {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q) :
    BankTrialDurationRecoveryAllRows (q := q) ring root := by
  classical
  intro z e hf
  rcases hf.2.2.2 with hreset |
      ⟨hm, hpositive, stage, hvalid, hstage⟩
  · by_cases he : e = root
    · subst e
      exact bankTrialDurationRecoveryResetOutgoingRow
        ring root hw z hf hreset.1
    · exact bankTrialDurationRecoveryResetAwayRow
        ring root e hw z hf hreset.1 he
  · by_cases heRoot : e = root
    · subst e
      by_cases hfinal : bankTrialDurationRecoveryReadRank z = 1
      · cases stage with
        | outward j =>
            have hread := bankTrialDurationRecoveryReadRankOut
              z j hstage
            rw [hread] at hfinal
            change 2 * (compileAdvice q).b - j = 1 at hfinal
            have hb := bankTrialDurationRecoveryWidthLarge q
            have hbound : j ≤ (compileAdvice q).b := hvalid.2
            omega
        | returning j =>
            have hread := bankTrialDurationRecoveryReadRankBack
              z j hstage
            rw [hread] at hfinal
            change j = 1 at hfinal
            subst j
            have hn : 2 ≤ n := by
              unfold BankTrialLiveWindowNonalias at hw
              omega
            exact bankTrialDurationRecoveryFinalReturnRow
              ring root hn z hf hm hstage
        | finished =>
            exact False.elim hstage
      · exact bankTrialDurationRecoveryRootWatchdogRow
          ring root hw z hf hm hfinal
    · by_cases hin : ring.rightNeighbor e = root
      · exact bankTrialDurationRecoveryIncomingObserverRow
          ring root e hw hin z hf hm
      · by_cases hchosen :
          e = bankTrialDurationRecoveryNominated ring root z
        · exact bankTrialDurationRecoveryAnyNominatedRow
            ring root e hw z hf hm hchosen
        · by_cases htop :
            e = Counter.site ring root (compileAdvice q).b
          · rw [htop]
            exact bankTrialDurationRecoveryTopUnaryRow
              ring root hw z hf hm
          · by_cases hsupport : Counter.Support q ring root e
            · rcases hsupport with hrootIncoming |
                ⟨j, hjbound, hjedge⟩
              · exact False.elim (hin hrootIncoming)
              · have hjpos : 0 < j := by
                  by_cases hzero : j = 0
                  · subst j
                    have hr : e = root := by
                      simpa only [Counter.site] using hjedge
                    exact False.elim (heRoot hr)
                  · omega
                have hjlt : j < (compileAdvice q).b := by
                  by_cases hjtop : j = (compileAdvice q).b
                  · subst j
                    exact False.elim (htop hjedge)
                  · omega
                have hnotselected :
                    Counter.site ring root j ≠
                      bankTrialDurationRecoveryNominated
                        ring root z := by
                  intro hh
                  exact hchosen (hjedge.trans hh)
                rw [hjedge]
                exact bankTrialDurationRecoveryInteriorStutterRow
                  ring root hw z hf hm ⟨j, hjlt⟩ hjpos
                  hnotselected
            · have hnotincoming :
                  e ≠ Counter.site ring root (n - 1) := by
                intro hh
                apply hin
                rw [hh]
                exact bankTrialDurationRecoveryLastIncoming
                  ring root
              exact bankTrialDurationRecoveryOutsideClockRow
                ring root e z hf hsupport hnotincoming hchosen

end L3

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-!
The imported bankTrialDurationClockBellman pays n per step,
whereas BankTrialDurationRecoveryOccupationCertificate
requires 2*n. Doubling that imported potential would exceed
the available 8*b*n reserve at RESET. This new potential
pays 2*n directly while using exactly 8*b*n at RESET.

The complete headline is NOT proved here. Two independent
bridges still need kernel proofs: the reachable first-entry
zero-lease/front certificate and the physical Fin n sum
of the distinguished root/incoming/nominated clock edges.
No assumption or axiom is introduced.
-/

def bankTrialDurationRecoveryTwinScalar
    (b rank lease : Nat) : Nat :=
  4 * rank + (13 * (b + 2) - lease)

def bankTrialDurationRecoveryTwinPotential (b n : Nat) :
    BankTrialDurationRecoveryClock → Nat
  | .reset => n * (8 * b)
  | .waiting rank lease =>
      n * bankTrialDurationRecoveryTwinScalar b rank lease
  | .done => 0

def bankTrialDurationRecoveryTwinLeaseNext
    (rank lease : Nat) : BankTrialDurationRecoveryClock :=
  if lease = 1 then .reset else .waiting rank (lease - 1)

def bankTrialDurationRecoveryTwinRowSum (b n : Nat) :
    BankTrialDurationRecoveryClock → Nat
  | .reset =>
      (n - 1) * bankTrialDurationRecoveryTwinPotential b n .reset +
      bankTrialDurationRecoveryTwinPotential b n
        (.waiting (2 * b - 1) (13 * (b + 2)))
  | .waiting rank lease =>
      if rank = 1 then
        (n - 2) * bankTrialDurationRecoveryTwinPotential b n
          (.waiting rank lease) +
        bankTrialDurationRecoveryTwinPotential b n .done +
        bankTrialDurationRecoveryTwinPotential b n
          (bankTrialDurationRecoveryTwinLeaseNext rank lease)
      else
        (n - 3) * bankTrialDurationRecoveryTwinPotential b n
          (.waiting rank lease) +
        bankTrialDurationRecoveryTwinPotential b n
          (.waiting (rank - 1) lease) +
        2 * bankTrialDurationRecoveryTwinPotential b n
          (bankTrialDurationRecoveryTwinLeaseNext rank lease)
  | .done => 0

private theorem bankTrialDurationRecoveryTwinScaleOne
    (n A B : Nat) (hn : 1 ≤ n) (h : 2 + B ≤ A) :
    2 * n + ((n - 1) * (n * A) + n * B) ≤
      n * (n * A) := by
  have hb : (n - 1) * A + (2 + B) ≤ n * A := by
    calc
      (n - 1) * A + (2 + B) ≤
          (n - 1) * A + A := Nat.add_le_add_left h _
      _ = n * A := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one,
            Nat.sub_add_cancel hn]
  calc
    2 * n + ((n - 1) * (n * A) + n * B) =
        n * ((n - 1) * A + (2 + B)) := by
          simp only [Nat.mul_add, Nat.mul_assoc]
          ac_rfl
    _ ≤ n * (n * A) := Nat.mul_le_mul_left n hb

private theorem bankTrialDurationRecoveryTwinScaleTwo
    (n A B : Nat) (hn : 2 ≤ n) (h : 2 + B ≤ 2 * A) :
    2 * n + ((n - 2) * (n * A) + n * B) ≤
      n * (n * A) := by
  have hb : (n - 2) * A + (2 + B) ≤ n * A := by
    calc
      (n - 2) * A + (2 + B) ≤
          (n - 2) * A + 2 * A := Nat.add_le_add_left h _
      _ = n * A := by
          rw [← Nat.add_mul, Nat.sub_add_cancel hn]
  calc
    2 * n + ((n - 2) * (n * A) + n * B) =
        n * ((n - 2) * A + (2 + B)) := by
          simp only [Nat.mul_add, Nat.mul_assoc]
          ac_rfl
    _ ≤ n * (n * A) := Nat.mul_le_mul_left n hb

private theorem bankTrialDurationRecoveryTwinScaleThree
    (n A B C : Nat) (hn : 3 ≤ n)
    (h : 2 + B + 2 * C ≤ 3 * A) :
    2 * n +
      ((n - 3) * (n * A) + n * B + 2 * (n * C)) ≤
      n * (n * A) := by
  have hb : (n - 3) * A + (2 + B + 2 * C) ≤ n * A := by
    calc
      (n - 3) * A + (2 + B + 2 * C) ≤
          (n - 3) * A + 3 * A := Nat.add_le_add_left h _
      _ = n * A := by
          rw [← Nat.add_mul, Nat.sub_add_cancel hn]
  calc
    2 * n +
        ((n - 3) * (n * A) + n * B + 2 * (n * C)) =
        n * ((n - 3) * A + (2 + B + 2 * C)) := by
          simp only [Nat.mul_add, Nat.mul_assoc]
          ac_rfl
    _ ≤ n * (n * A) := Nat.mul_le_mul_left n hb

private theorem bankTrialDurationRecoveryTwinResetScalar
    (b : Nat) (hb : 2 ≤ b) :
    2 + bankTrialDurationRecoveryTwinScalar b
      (2 * b - 1) (13 * (b + 2)) ≤ 8 * b := by
  unfold bankTrialDurationRecoveryTwinScalar
  omega

private theorem bankTrialDurationRecoveryTwinInteriorScalar
    (b rank lease : Nat)
    (hr : 2 ≤ rank) (hl : 2 ≤ lease) :
    2 + bankTrialDurationRecoveryTwinScalar b (rank - 1) lease +
        2 * bankTrialDurationRecoveryTwinScalar b rank
          (lease - 1) ≤
      3 * bankTrialDurationRecoveryTwinScalar b rank lease := by
  unfold bankTrialDurationRecoveryTwinScalar
  omega

private theorem bankTrialDurationRecoveryTwinTimeoutScalar
    (b rank : Nat) (hr : 2 ≤ rank) :
    2 + bankTrialDurationRecoveryTwinScalar b (rank - 1) 1 +
      2 * (8 * b) ≤
      3 * bankTrialDurationRecoveryTwinScalar b rank 1 := by
  unfold bankTrialDurationRecoveryTwinScalar
  omega

private theorem bankTrialDurationRecoveryTwinReturnScalar
    (b lease : Nat) (hl : 2 ≤ lease) :
    2 + bankTrialDurationRecoveryTwinScalar b 1 (lease - 1) ≤
      2 * bankTrialDurationRecoveryTwinScalar b 1 lease := by
  unfold bankTrialDurationRecoveryTwinScalar
  omega

private theorem bankTrialDurationRecoveryTwinReturnTimeoutScalar
    (b : Nat) :
    2 + 8 * b ≤
      2 * bankTrialDurationRecoveryTwinScalar b 1 1 := by
  unfold bankTrialDurationRecoveryTwinScalar
  omega

/-- Exact abstract reset/front Bellman inequality with TWO
units of occupation cost on the original n-edge clock. -/
theorem bankTrialDurationRecoveryTwinBellman
    (b n : Nat) (hb : 2 ≤ b) (hn : 3 ≤ n)
    (s : BankTrialDurationRecoveryClock)
    (hs : s = .reset ∨
      ∃ rank lease : Nat,
        s = .waiting rank lease ∧
        1 ≤ rank ∧ 1 ≤ lease) :
    2 * n + bankTrialDurationRecoveryTwinRowSum b n s ≤
      n * bankTrialDurationRecoveryTwinPotential b n s := by
  rcases hs with hreset | ⟨rank, lease, heq, hr, hl⟩
  · subst s
    have h := bankTrialDurationRecoveryTwinScaleOne n
      (8 * b)
      (bankTrialDurationRecoveryTwinScalar b
        (2 * b - 1) (13 * (b + 2)))
      (by omega) (bankTrialDurationRecoveryTwinResetScalar b hb)
    simpa only [bankTrialDurationRecoveryTwinRowSum,
      bankTrialDurationRecoveryTwinPotential] using h
  · subst s
    by_cases hone : rank = 1
    · subst rank
      by_cases hlease : lease = 1
      · subst lease
        have h := bankTrialDurationRecoveryTwinScaleTwo n
          (bankTrialDurationRecoveryTwinScalar b 1 1)
          (8 * b) (by omega)
          (bankTrialDurationRecoveryTwinReturnTimeoutScalar b)
        simpa only [bankTrialDurationRecoveryTwinRowSum,
          if_pos rfl, bankTrialDurationRecoveryTwinLeaseNext,
          ↓reduceIte, bankTrialDurationRecoveryTwinPotential,
          Nat.add_zero] using h
      · have hmore : 2 ≤ lease := by omega
        have h := bankTrialDurationRecoveryTwinScaleTwo n
          (bankTrialDurationRecoveryTwinScalar b 1 lease)
          (bankTrialDurationRecoveryTwinScalar b 1 (lease - 1))
          (by omega)
          (bankTrialDurationRecoveryTwinReturnScalar b lease hmore)
        simpa only [bankTrialDurationRecoveryTwinRowSum,
          if_pos rfl, bankTrialDurationRecoveryTwinLeaseNext,
          if_neg hlease, bankTrialDurationRecoveryTwinPotential,
          ↓reduceIte, Nat.add_zero] using h
    · have hrmore : 2 ≤ rank := by omega
      by_cases hlease : lease = 1
      · subst lease
        have h := bankTrialDurationRecoveryTwinScaleThree n
          (bankTrialDurationRecoveryTwinScalar b rank 1)
          (bankTrialDurationRecoveryTwinScalar b (rank - 1) 1)
          (8 * b) hn
          (bankTrialDurationRecoveryTwinTimeoutScalar b rank hrmore)
        simpa only [bankTrialDurationRecoveryTwinRowSum,
          if_neg hone, bankTrialDurationRecoveryTwinLeaseNext,
          if_pos rfl, bankTrialDurationRecoveryTwinPotential,
          ↓reduceIte] using h
      · have hmore : 2 ≤ lease := by omega
        have h := bankTrialDurationRecoveryTwinScaleThree n
          (bankTrialDurationRecoveryTwinScalar b rank lease)
          (bankTrialDurationRecoveryTwinScalar b (rank - 1) lease)
          (bankTrialDurationRecoveryTwinScalar b rank (lease - 1))
          hn
          (bankTrialDurationRecoveryTwinInteriorScalar
            b rank lease hrmore hmore)
        simpa only [bankTrialDurationRecoveryTwinRowSum,
          if_neg hone, bankTrialDurationRecoveryTwinLeaseNext,
          if_neg hlease, bankTrialDurationRecoveryTwinPotential]
          using h

/-- Every authenticated recovery front has a clock value
covered by the two-cost Bellman inequality. -/
theorem bankTrialDurationRecoveryTwinClockAdmissible {q : Nat}
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z) :
    bankTrialDurationRecoveryClockOf z = .reset ∨
      ∃ rank lease : Nat,
        bankTrialDurationRecoveryClockOf z =
          .waiting rank lease ∧
        1 ≤ rank ∧ 1 ≤ lease := by
  rcases hf.2.2.2 with hr | hw
  · exact Or.inl
      (bankTrialDurationRecoveryClockResetOfFront z hf hr.1)
  · rcases hw with ⟨hm, hpositive, stage, hvalid, hstage⟩
    refine Or.inr
      ⟨bankTrialDurationRecoveryReadRank z,
       bankTrialDurationRecoveryReadLease z,
       bankTrialDurationRecoveryClockWaitOfFront z hf hm, ?_,
       hpositive⟩
    cases stage with
    | outward j =>
        rw [bankTrialDurationRecoveryReadRankOut z j hstage]
        change 1 ≤ 2 * (compileAdvice q).b - j
        have hb := bankTrialDurationRecoveryWidthLarge q
        have hj : j ≤ (compileAdvice q).b := hvalid.2
        omega
    | returning j =>
        rw [bankTrialDurationRecoveryReadRankBack z j hstage]
        change 1 ≤ j
        exact hvalid.1
    | finished =>
        exact False.elim hstage

theorem bankTrialDurationRecoveryTwinFrontBellman {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z) :
    2 * n +
      bankTrialDurationRecoveryTwinRowSum (compileAdvice q).b n
        (bankTrialDurationRecoveryClockOf z) ≤
      n * bankTrialDurationRecoveryTwinPotential
        (compileAdvice q).b n
        (bankTrialDurationRecoveryClockOf z) := by
  have hn : 3 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    have hb := bankTrialDurationRecoveryWidthLarge q
    omega
  have hb : 2 ≤ (compileAdvice q).b :=
    bankTrialDurationRecoveryWidthLarge q
  exact bankTrialDurationRecoveryTwinBellman
    (compileAdvice q).b n hb hn
    (bankTrialDurationRecoveryClockOf z)
    (bankTrialDurationRecoveryTwinClockAdmissible z hf)

/-- A front is closed under all words by the
AllRows theorem and terminal absorption. -/
theorem bankTrialDurationRecoveryFrontRunNonalias {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (w : List (Fin n)) (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z) :
    bankTrialLocalTerminal (bankTrialLocalRun ring root w z) ∨
      BankTrialDurationRecoveryFront q
        (bankTrialLocalRun ring root w z) := by
  have hrows := bankTrialDurationRecoveryAllRowsNonalias
    ring root hsmall hw
  induction w generalizing z with
  | nil =>
      exact Or.inr hf
  | cons e es ih =>
      have hnext := (hrows z e hf).1
      rcases hnext with ht | hfnext
      · exact Or.inl
          (bankTrialLocalRunTerminal ring root es
            (bankTrialLocalNext ring root z e) ht)
      · exact ih (bankTrialLocalNext ring root z e) hfnext

/-- Candidate full-observer potential. Its CLEAN start is bounded
without any reachable-state or first-entry assumptions. -/
noncomputable def bankTrialDurationRecoveryTwinOccupation {q : Nat}
    (n : Nat) (z : BankTrialLocalState q) : Nat :=
  if bankTrialLocalTerminal z then 0
  else if z.phase = .recovery then
    bankTrialDurationRecoveryTwinPotential
      (compileAdvice q).b n
      (bankTrialDurationRecoveryClockOf z)
  else 8 * (compileAdvice q).b * n

theorem bankTrialDurationRecoveryTwinOccupationSeed {n q : Nat}
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    bankTrialDurationRecoveryTwinOccupation n
      (bankTrialLocalStart S) =
        8 * (compileAdvice q).b * n := by
  have hn : ¬ bankTrialLocalTerminal (bankTrialLocalStart S) := by
    intro ht
    rcases ht with hw | hl
    · cases hw
    · cases hl
  have hr : (bankTrialLocalStart S).phase ≠ .recovery := by
    intro h
    cases h
  simp only [bankTrialDurationRecoveryTwinOccupation,
    if_neg hn, if_neg hr]

theorem bankTrialDurationRecoveryTwinOccupationFront {n q : Nat}
    (z : BankTrialLocalState q)
    (hf : BankTrialDurationRecoveryFront q z) :
    bankTrialDurationRecoveryTwinOccupation n z =
      bankTrialDurationRecoveryTwinPotential
        (compileAdvice q).b n
        (bankTrialDurationRecoveryClockOf z) := by
  have hn := bankTrialDurationRecoveryFrontNotTerminal z hf
  simp only [bankTrialDurationRecoveryTwinOccupation,
    if_neg hn, if_pos hf.1]

/-- The two remaining explicit bridge predicates are *Props*,
not theorems and not axioms. Neither has been discharged here. -/
def BankTrialDurationRecoveryFirstEntryFront {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
        (compileAdvice q).b),
    BankTrialLocalClean q S →
    ∀ (z : BankTrialLocalState q),
      BankTrialDurationReachable ring root S z →
      ∀ (e : Fin n),
        (∃ begun : Bool, z.phase = .live begun) →
        (bankTrialLocalNext ring root z e).phase = .recovery →
        BankTrialDurationRecoveryFront q
          (bankTrialLocalNext ring root z e)

def BankTrialDurationRecoveryTwinPortSum {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (z : BankTrialLocalState q),
    BankTrialDurationRecoveryFront q z →
    (List.ofFn (fun e : Fin n =>
      bankTrialDurationRecoveryTwinPotential (compileAdvice q).b n
        (bankTrialDurationRecoveryClockNext
          (compileAdvice q).b root
          (Counter.site ring root (n - 1))
          (bankTrialDurationRecoveryNominated ring root z)
          e (bankTrialDurationRecoveryClockOf z)))).sum ≤
      bankTrialDurationRecoveryTwinRowSum
        (compileAdvice q).b n
        (bankTrialDurationRecoveryClockOf z)

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!The missing FirstEntryFront conjunct is precisely zero root lease.
The following port-sum derivation uses original Fin n letters.
The first-entry zero-lease BANK-reference row remains unproved.
-/

private theorem bankTrialRecoveryOneReplacement :
    ∀ (m : Nat) (a : Fin m) (f : Fin m → Nat) (v : Nat),
      (List.ofFn (fun i : Fin m =>
        if i = a then v else f i)).sum + f a =
      (List.ofFn f).sum + v := by
  intro m
  induction m with
  | zero =>
      intro a
      exact Fin.elim0 a
  | succ m ih =>
      intro a f v
      cases a using Fin.cases with
      | zero =>
          have htail :
              (fun i : Fin m =>
                if i.succ = (0 : Fin (m + 1)) then v
                else f i.succ) =
              (fun i : Fin m => f i.succ) := by
            funext i
            exact if_neg (Fin.succ_ne_zero i)
          simp only [List.ofFn_succ, List.sum_cons,
            ↓reduceIte, htail]
          omega
      | succ a =>
          have hz : (0 : Fin (m + 1)) ≠ a.succ :=
            Ne.symm (Fin.succ_ne_zero a)
          have htail :
              (fun i : Fin m =>
                if i.succ = a.succ then v else f i.succ) =
              (fun i : Fin m =>
                if i = a then v else f i.succ) := by
            funext i
            by_cases hi : i = a
            · subst i
              simp
            · have hn : i.succ ≠ a.succ := by
                intro he
                exact hi (Fin.succ_inj.mp he)
              simp only [if_neg hn, if_neg hi]
          have hrec := ih a (fun i : Fin m => f i.succ) v
          simp only [List.ofFn_succ, List.sum_cons,
            if_neg hz, htail]
          omega

private theorem bankTrialRecoverySumSingle
    (n : Nat) (a : Fin n) (v d : Nat) :
    (List.ofFn (fun e : Fin n =>
      if e = a then v else d)).sum =
      (n - 1) * d + v := by
  have h := bankTrialRecoveryOneReplacement n a
    (fun _ : Fin n => d) v
  change
    (List.ofFn (fun e : Fin n =>
      if e = a then v else d)).sum + d =
      (List.ofFn (fun _ : Fin n => d)).sum + v at h
  rw [FiniteUniformStoppingTree.ofFn_sum_const] at h
  have hn : 1 ≤ n := by
    have ha := a.isLt
    omega
  have hmul : (n - 1) * d + d = n * d := by
    calc
      (n - 1) * d + d = ((n - 1) + 1) * d := by
        rw [Nat.add_mul, Nat.one_mul]
      _ = n * d := by rw [Nat.sub_add_cancel hn]
  omega

private theorem bankTrialRecoverySumDouble
    (n : Nat) (a b : Fin n) (v w d : Nat)
    (hne : a ≠ b) (hn : 2 ≤ n) :
    (List.ofFn (fun e : Fin n =>
      if e = a then v else if e = b then w else d)).sum =
      (n - 2) * d + v + w := by
  have hb := bankTrialRecoveryOneReplacement n b
    (fun _ : Fin n => d) w
  change
    (List.ofFn (fun e : Fin n =>
      if e = b then w else d)).sum + d =
      (List.ofFn (fun _ : Fin n => d)).sum + w at hb
  rw [FiniteUniformStoppingTree.ofFn_sum_const] at hb
  have ha := bankTrialRecoveryOneReplacement n a
    (fun e : Fin n => if e = b then w else d) v
  have hneq : (if a = b then w else d) = d :=
    if_neg hne
  rw [hneq] at ha
  have hmul : (n - 2) * d + 2 * d = n * d := by
    calc
      (n - 2) * d + 2 * d = ((n - 2) + 2) * d := by
        rw [Nat.add_mul]
      _ = n * d := by rw [Nat.sub_add_cancel hn]
  omega

private theorem bankTrialRecoverySumTriple
    (n : Nat) (a b c : Fin n) (v w x d : Nat)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hn : 3 ≤ n) :
    (List.ofFn (fun e : Fin n =>
      if e = a then v
      else if e = b then w
      else if e = c then x else d)).sum =
      (n - 3) * d + v + w + x := by
  have hc := bankTrialRecoveryOneReplacement n c
    (fun _ : Fin n => d) x
  change
    (List.ofFn (fun e : Fin n =>
      if e = c then x else d)).sum + d =
      (List.ofFn (fun _ : Fin n => d)).sum + x at hc
  rw [FiniteUniformStoppingTree.ofFn_sum_const] at hc
  have hb := bankTrialRecoveryOneReplacement n b
    (fun e : Fin n => if e = c then x else d) w
  have hbcval : (if b = c then x else d) = d :=
    if_neg hbc
  rw [hbcval] at hb
  have ha := bankTrialRecoveryOneReplacement n a
    (fun e : Fin n =>
      if e = b then w else if e = c then x else d) v
  have haval :
      (if a = b then w else if a = c then x else d) = d := by
    simp only [if_neg hab, if_neg hac]
  rw [haval] at ha
  have hmul : (n - 3) * d + 3 * d = n * d := by
    calc
      (n - 3) * d + 3 * d = ((n - 3) + 3) * d := by
        rw [Nat.add_mul]
      _ = n * d := by rw [Nat.sub_add_cancel hn]
  omega

def bankTrialRecoveryTwinTape {n : Nat}
    (b : Nat) (root incoming chosen : Fin n)
    (s : BankTrialDurationRecoveryClock) (e : Fin n) : Nat :=
  bankTrialDurationRecoveryTwinPotential b n
    (bankTrialDurationRecoveryClockNext
      b root incoming chosen e s)

private theorem bankTrialRecoveryTwinResetPorts
    {n : Nat} (b : Nat)
    (root incoming chosen : Fin n) :
    (List.ofFn
      (bankTrialRecoveryTwinTape b root incoming chosen .reset)).sum =
      bankTrialDurationRecoveryTwinRowSum b n .reset := by
  have heq (e : Fin n) :
      bankTrialRecoveryTwinTape b root incoming chosen .reset e =
        if e = root then
          bankTrialDurationRecoveryTwinPotential b n
            (.waiting (2 * b - 1) (13 * (b + 2)))
        else bankTrialDurationRecoveryTwinPotential b n .reset := by
    by_cases hr : e = root
    · simp [bankTrialRecoveryTwinTape,
        bankTrialDurationRecoveryClockNext, hr]
    · simp [bankTrialRecoveryTwinTape,
        bankTrialDurationRecoveryClockNext, hr]
  calc
    (List.ofFn
      (bankTrialRecoveryTwinTape b root incoming chosen .reset)).sum =
      (List.ofFn (fun e : Fin n =>
        if e = root then
          bankTrialDurationRecoveryTwinPotential b n
            (.waiting (2 * b - 1) (13 * (b + 2)))
        else bankTrialDurationRecoveryTwinPotential b n .reset)).sum :=
          FiniteUniformStoppingTree.ofFn_sum_eq _ _ heq
    _ = (n - 1) *
          bankTrialDurationRecoveryTwinPotential b n .reset +
          bankTrialDurationRecoveryTwinPotential b n
            (.waiting (2 * b - 1) (13 * (b + 2))) :=
          bankTrialRecoverySumSingle n root _ _
    _ = bankTrialDurationRecoveryTwinRowSum b n .reset := rfl

private theorem bankTrialRecoveryTwinFinalPorts
    {n : Nat} (b : Nat) (root incoming : Fin n)
    (hne : root ≠ incoming) (lease : Nat) (hl : 1 ≤ lease) :
    (List.ofFn
      (bankTrialRecoveryTwinTape b root incoming root
        (.waiting 1 lease))).sum =
      bankTrialDurationRecoveryTwinRowSum b n
        (.waiting 1 lease) := by
  have hlease :
      (if lease ≤ 1 then
        (BankTrialDurationRecoveryClock.reset)
       else .waiting 1 (lease - 1)) =
      bankTrialDurationRecoveryTwinLeaseNext 1 lease := by
    by_cases h : lease = 1
    · subst lease
      rfl
    · have hn : ¬ lease ≤ 1 := by omega
      simp only [bankTrialDurationRecoveryTwinLeaseNext,
        if_neg h, if_neg hn]
  have heq (e : Fin n) :
      bankTrialRecoveryTwinTape b root incoming root
          (.waiting 1 lease) e =
        if e = root then
          bankTrialDurationRecoveryTwinPotential b n .done
        else if e = incoming then
          bankTrialDurationRecoveryTwinPotential b n
            (bankTrialDurationRecoveryTwinLeaseNext 1 lease)
        else bankTrialDurationRecoveryTwinPotential b n
          (.waiting 1 lease) := by
    by_cases hr : e = root
    · subst e
      simp [bankTrialRecoveryTwinTape,
        bankTrialDurationRecoveryClockNext]
    · by_cases hi : e = incoming
      · subst e
        have hri : incoming ≠ root := Ne.symm hne
        simp [bankTrialRecoveryTwinTape,
          bankTrialDurationRecoveryClockNext,
          hri, hlease]
      · simp [bankTrialRecoveryTwinTape,
          bankTrialDurationRecoveryClockNext,
          hr, hi]
  have hn : 2 ≤ n := by
    have ha := root.isLt
    have hb := incoming.isLt
    have hd : root.val ≠ incoming.val := by
      intro he
      exact hne (Fin.ext he)
    omega
  calc
    (List.ofFn (bankTrialRecoveryTwinTape b root incoming root
        (.waiting 1 lease))).sum =
      (List.ofFn (fun e : Fin n =>
        if e = root then
          bankTrialDurationRecoveryTwinPotential b n .done
        else if e = incoming then
          bankTrialDurationRecoveryTwinPotential b n
            (bankTrialDurationRecoveryTwinLeaseNext 1 lease)
        else bankTrialDurationRecoveryTwinPotential b n
          (.waiting 1 lease))).sum :=
          FiniteUniformStoppingTree.ofFn_sum_eq _ _ heq
    _ = (n - 2) *
          bankTrialDurationRecoveryTwinPotential b n
            (.waiting 1 lease) +
          bankTrialDurationRecoveryTwinPotential b n .done +
          bankTrialDurationRecoveryTwinPotential b n
            (bankTrialDurationRecoveryTwinLeaseNext 1 lease) :=
          bankTrialRecoverySumDouble n root incoming _ _ _
            hne hn
    _ = bankTrialDurationRecoveryTwinRowSum b n
          (.waiting 1 lease) := by
            simp only [bankTrialDurationRecoveryTwinRowSum,
              ↓reduceIte]

private theorem bankTrialRecoveryTwinNonfinalPorts
    {n : Nat} (b : Nat) (root incoming chosen : Fin n)
    (hn : 3 ≤ n) (hrc : root ≠ chosen)
    (hri : root ≠ incoming) (hci : chosen ≠ incoming)
    (rank lease : Nat) (hr : rank ≠ 1) (hl : 1 ≤ lease) :
    (List.ofFn
      (bankTrialRecoveryTwinTape b root incoming chosen
        (.waiting rank lease))).sum =
      bankTrialDurationRecoveryTwinRowSum b n
        (.waiting rank lease) := by
  have hlease :
      (if lease ≤ 1 then
        (BankTrialDurationRecoveryClock.reset)
       else .waiting rank (lease - 1)) =
      bankTrialDurationRecoveryTwinLeaseNext rank lease := by
    by_cases h : lease = 1
    · subst lease
      rfl
    · have hnot : ¬ lease ≤ 1 := by omega
      simp only [bankTrialDurationRecoveryTwinLeaseNext,
        if_neg h, if_neg hnot]
  have heq (e : Fin n) :
      bankTrialRecoveryTwinTape b root incoming chosen
          (.waiting rank lease) e =
        if e = chosen then
          bankTrialDurationRecoveryTwinPotential b n
            (.waiting (rank - 1) lease)
        else if e = root then
          bankTrialDurationRecoveryTwinPotential b n
            (bankTrialDurationRecoveryTwinLeaseNext rank lease)
        else if e = incoming then
          bankTrialDurationRecoveryTwinPotential b n
            (bankTrialDurationRecoveryTwinLeaseNext rank lease)
        else bankTrialDurationRecoveryTwinPotential b n
          (.waiting rank lease) := by
    by_cases hc : e = chosen
    · subst e
      have hcr : chosen ≠ root := Ne.symm hrc
      simp [bankTrialRecoveryTwinTape,
        bankTrialDurationRecoveryClockNext, hr, hcr]
    · by_cases hroot : e = root
      · subst e
        have hrc' : root ≠ chosen := hrc
        simp [bankTrialRecoveryTwinTape,
          bankTrialDurationRecoveryClockNext,
          hr, hrc', hlease]
      · by_cases hi : e = incoming
        · subst e
          have hic : incoming ≠ chosen := Ne.symm hci
          have hir : incoming ≠ root := Ne.symm hri
          simp [bankTrialRecoveryTwinTape,
            bankTrialDurationRecoveryClockNext,
            hr, hic, hir, hlease]
        · simp [bankTrialRecoveryTwinTape,
            bankTrialDurationRecoveryClockNext,
            hr, hc, hroot, hi]
  calc
    (List.ofFn (bankTrialRecoveryTwinTape b root incoming chosen
        (.waiting rank lease))).sum =
      (List.ofFn (fun e : Fin n =>
        if e = chosen then
          bankTrialDurationRecoveryTwinPotential b n
            (.waiting (rank - 1) lease)
        else if e = root then
          bankTrialDurationRecoveryTwinPotential b n
            (bankTrialDurationRecoveryTwinLeaseNext rank lease)
        else if e = incoming then
          bankTrialDurationRecoveryTwinPotential b n
            (bankTrialDurationRecoveryTwinLeaseNext rank lease)
        else bankTrialDurationRecoveryTwinPotential b n
          (.waiting rank lease))).sum :=
          FiniteUniformStoppingTree.ofFn_sum_eq _ _ heq
    _ = (n - 3) *
          bankTrialDurationRecoveryTwinPotential b n
            (.waiting rank lease) +
          bankTrialDurationRecoveryTwinPotential b n
            (.waiting (rank - 1) lease) +
          bankTrialDurationRecoveryTwinPotential b n
            (bankTrialDurationRecoveryTwinLeaseNext rank lease) +
          bankTrialDurationRecoveryTwinPotential b n
            (bankTrialDurationRecoveryTwinLeaseNext rank lease) :=
          bankTrialRecoverySumTriple n chosen root incoming _ _ _ _
            (Ne.symm hrc) hci hri hn
    _ = bankTrialDurationRecoveryTwinRowSum b n
          (.waiting rank lease) := by
            simp only [bankTrialDurationRecoveryTwinRowSum,
              if_neg hr]
            omega

/-- The three physical ports have exactly the counted row sum.
At the final rank the chosen edge coincides with root, and the
correct formula has only two exceptional letters. -/
theorem bankTrialDurationRecoveryTwinPortSumHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q) :
    BankTrialDurationRecoveryTwinPortSum (q := q) ring root := by
  classical
  intro z hf
  have hn : 3 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    have hb := bankTrialDurationRecoveryWidthLarge q
    omega
  have hrootIncoming :
      root ≠ Counter.site ring root (n - 1) := by
    intro he
    have hh := bankTrialDurationRecoveryLastIncoming ring root
    rw [← he] at hh
    exact (Counter.resetRootPortDistinct ring root (by omega)) hh
  change (List.ofFn
    (bankTrialRecoveryTwinTape (compileAdvice q).b root
      (Counter.site ring root (n - 1))
      (bankTrialDurationRecoveryNominated ring root z)
      (bankTrialDurationRecoveryClockOf z))).sum ≤
    bankTrialDurationRecoveryTwinRowSum
      (compileAdvice q).b n
      (bankTrialDurationRecoveryClockOf z)
  rcases hf.2.2.2 with hreset |
      ⟨hm, hpositive, stage, hvalid, hstage⟩
  · have hclock :=
      bankTrialDurationRecoveryClockResetOfFront z hf hreset.1
    rw [hclock]
    exact Nat.le_of_eq (bankTrialRecoveryTwinResetPorts
      (compileAdvice q).b root
      (Counter.site ring root (n - 1))
      (bankTrialDurationRecoveryNominated ring root z))
  · have hclock :=
      bankTrialDurationRecoveryClockWaitOfFront z hf hm
    rw [hclock]
    by_cases hfinal : bankTrialDurationRecoveryReadRank z = 1
    · have hchosen :
          bankTrialDurationRecoveryNominated ring root z = root := by
        cases stage with
        | outward j =>
            have hjbound : j ≤ (compileAdvice q).b := hvalid.2
            have hb := bankTrialDurationRecoveryWidthLarge q
            rw [bankTrialDurationRecoveryReadRankOut
              z j hstage] at hfinal
            change 2 * (compileAdvice q).b - j = 1 at hfinal
            omega
        | returning j =>
            rw [bankTrialDurationRecoveryReadRankBack
              z j hstage] at hfinal
            change j = 1 at hfinal
            subst j
            unfold bankTrialDurationRecoveryNominated
            rw [bankTrialDurationRecoveryReadStageBack z 1 hstage]
            simp [Counter.resetClockNominated]
        | finished =>
            exact False.elim hstage
      rw [hchosen, hfinal]
      exact Nat.le_of_eq
        (bankTrialRecoveryTwinFinalPorts (compileAdvice q).b
          root (Counter.site ring root (n - 1))
          hrootIncoming (bankTrialDurationRecoveryReadLease z)
          hpositive)
    · have hrootChosen :
          root ≠ bankTrialDurationRecoveryNominated ring root z :=
        bankTrialDurationRecoveryRootNotChosen
          ring root hw z hf hm hfinal
      have hchosenIncoming :
          bankTrialDurationRecoveryNominated ring root z ≠
            Counter.site ring root (n - 1) := by
        intro he
        have hh := bankTrialDurationRecoveryNominatedNotIncoming
          ring root hw z hf hm
        apply hh
        rw [he]
        exact bankTrialDurationRecoveryLastIncoming ring root
      exact Nat.le_of_eq
        (bankTrialRecoveryTwinNonfinalPorts
          (compileAdvice q).b root
          (Counter.site ring root (n - 1))
          (bankTrialDurationRecoveryNominated ring root z)
          hn hrootChosen hrootIncoming hchosenIncoming
          (bankTrialDurationRecoveryReadRank z)
          (bankTrialDurationRecoveryReadLease z)
          hfinal hpositive)

/-- CLEAN-word locking excludes an already-RESET LIVE root. -/
theorem bankTrialDurationRecoveryEntryOldNotReset {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalClean q S)
    (z : BankTrialLocalState q)
    (hz : BankTrialDurationReachable ring root S z)
    (begun : Bool) (hlive : z.phase = .live begun) :
    bankTrialLiveWaveRootMode z.bank ≠ .RESET := by
  obtain ⟨w, hword⟩ := hz
  have hlock := bankTrialWindowLockedCleanWords
    ring root hw S hc w
  rw [hword] at hlock
  exact hlock.2 begun hlive

/-- Sole missing conjunct after the first-entry RecoveryCert:
the postservice RESET root must have lease zero.
The exact local BANK-reference row has not been proved. -/
def BankTrialDurationRecoveryFirstEntryLeaseZero {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
        (compileAdvice q).b),
    BankTrialLocalClean q S →
    ∀ (z : BankTrialLocalState q),
      BankTrialDurationReachable ring root S z →
      ∀ (e : Fin n),
        (∃ begun : Bool, z.phase = .live begun) →
        (bankTrialLocalNext ring root z e).phase = .recovery →
        ((bankTrialLocalNext ring root z e).bank.fields
          ⟨0, by omega⟩).2.2.2 = 0

theorem bankTrialDurationRecoveryFirstEntryFrontOfLeaseZero
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hzero : BankTrialDurationRecoveryFirstEntryLeaseZero
      (q := q) ring root) :
    BankTrialDurationRecoveryFirstEntryFront (q := q)
      ring root := by
  intro S hclean z hz e hlive hrec
  rcases hlive with ⟨begun, hphase⟩
  cases z with
  | mk B phase =>
      cases hphase
      obtain ⟨w, hword⟩ := hz
      have hc := bankTrialLocalCleanRunRecoveryEntry
        ring root S hclean w B begun hword e hrec
      have hm : bankTrialLiveWaveRootMode
          (bankTrialLocalNext ring root
            (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank =
          .RESET := by
        change
          ((bankTrialLocalNext ring root
            (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank.fields
            ⟨0, by omega⟩).1 = .RESET
        rw [bankTrialLocalNextLiveBank]
        exact bankTrialLocalLiveRecoveryRoot
          ring root e B begun hrec
      exact bankTrialDurationRecoveryResetFrontOfCert
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) e)
        hrec hc hm
        (hzero S hclean
          (⟨B, .live begun⟩ : BankTrialLocalState q)
          ⟨w, hword⟩ e ⟨begun, rfl⟩ hrec)

end L3

namespace L3

open Classical
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-!
For the two remaining G12d stages.
Genuine CLEAN-reachable LIVE roots cannot be in OLD RESET mode.
The only new-RESET root rows are source, incoming and frame.
Then AllRows and TwinPortSum yield the occupation
certificate, paying two clock units per RECOVERY service.
-/

/-- Every NEW RESET output of the old root-source BANK row has
zero lease, including the CWAIT CL1 return and watchdog expiry.
The excluded OLD RESET mode is exactly the CLEAN-word lock. -/
private theorem bankTrialRecoveryRootSourceNewResetZero
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false)
    (hold : x.mode ≠ .RESET)
    (hnew : (bankPair x y 1 b theta).1.mode = .RESET) :
    (bankPair x y 1 b theta).1.lease = 0 := by
  cases hm : x.mode <;>
    cases ht : y.tok <;>
    cases hb : y.bit <;>
    by_cases hl : 1 < x.lease <;>
    simp [bankPair, hx, hy, hg, hm, ht, hb, hl,
      isWaitMode, isRetTok] at hold hnew ⊢ <;>
    (first | contradiction | rfl | omega |
      ((repeat' split) <;> simp_all))

/-- ARMED incoming clears to RESET/zero; waiting incoming
either stays waiting or expires to RESET/zero. -/
private theorem bankTrialRecoveryIncomingNewResetZero
    (x : BankCell) (hold : x.mode ≠ .RESET)
    (hnew : (GrantBankReference.incomingRootBankMap x).mode =
      .RESET) :
    (GrantBankReference.incomingRootBankMap x).lease = 0 := by
  cases hm : x.mode <;>
    by_cases hl : 1 < x.lease <;>
    simp [GrantBankReference.incomingRootBankMap, hm,
      isWaitMode, hl] at hold hnew ⊢ <;>
    (first | contradiction | rfl | omega)

/-- A literal zero survives copyBank's finite lease clamp. -/
private theorem bankTrialRecoveryClampedZero
    (q : Nat) (x : BankCell) (hz : x.lease = 0) :
    (GrantBankReference.bankLocalReferenceClampedQuad q x).2.2.2 =
      0 := by
  have hc : x.lease ≤ (compileAdvice q).bankLeaseCap := by
    rw [hz]
    exact Nat.zero_le _
  rw [bankTrialLocalClampedLease q x hc]
  exact hz

/-- Three exact physical cases for the protected root field:
source at root, responder to incoming root, or original frame. -/
private theorem bankTrialRecoveryRootStepNewResetZero
    {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hfalse : B.success = false)
    (hold : bankTrialLiveWaveRootMode B ≠ .RESET)
    (hnew :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨0, by omega⟩).1 = .RESET) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨0, by omega⟩).2.2.2 = 0 := by
  classical
  have hb : 1 < (compileAdvice q).b :=
    bankTrialDurationRecoveryWidthLarge q
  by_cases he : e = root
  · subst e
    have hs : Counter.Support q ring root root :=
      Or.inr ⟨0, Nat.zero_le _, rfl⟩
    have hfield :
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root).fields ⟨0, by omega⟩ =
        GrantBankReference.bankLocalReferenceClampedQuad q
          ((GrantBankReference.bankLocalReferenceInternalPair q B
            ⟨0, show 0 < (compileAdvice q).b by omega⟩).1) := by
      rw [bankTrialLocalStepField ring root root B hs hfalse]
      exact bankTrialLocalFieldRootOutgoing ring root B
    have hrawMode :
        (GrantBankReference.bankLocalReferenceInternalPair q B
          ⟨0, show 0 < (compileAdvice q).b by omega⟩).1.mode =
            .RESET := by
      rw [hfield] at hnew
      exact hnew
    have hsource :
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by omega⟩).mode ≠ .RESET := hold
    have hrawLease :
        (GrantBankReference.bankLocalReferenceInternalPair q B
          ⟨0, show 0 < (compileAdvice q).b by omega⟩).1.lease =
          0 := by
      exact bankTrialRecoveryRootSourceNewResetZero
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by omega⟩)
        (GrantBankReference.bankLocalReferenceCell B
          ⟨1, show 1 < (compileAdvice q).b + 1 by omega⟩)
        (compileAdvice q).b (compileAdvice q).theta
        rfl rfl rfl hsource hrawMode
    rw [hfield]
    exact bankTrialRecoveryClampedZero q _ hrawLease
  · by_cases hin : ring.rightNeighbor e = root
    · have hs : Counter.Support q ring root e :=
        Or.inl hin
      have hx :
          ¬ (0 < (compileAdvice q).b ∧
            e = Counter.site ring root 0) := by
        intro h
        apply he
        simpa [Counter.site] using h.2
      have hy :
          ¬ (0 < (0 : Nat) ∧
            e = Counter.site ring root (0 - 1)) := by
        intro h
        omega
      have ht :
          ¬ ((0 : Nat) = (compileAdvice q).b ∧
            e = Counter.site ring root (compileAdvice q).b) := by
        intro h
        have hb := bankTrialDurationRecoveryWidthLarge q
        omega
      have hfield :
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B e).fields ⟨0, by omega⟩ =
          GrantBankReference.bankLocalReferenceClampedQuad q
            (GrantBankReference.incomingRootBankMap
              (GrantBankReference.bankLocalReferenceCell B
                ⟨0, by omega⟩)) := by
        rw [bankTrialLocalStepField ring root e B hs hfalse]
        exact bankTrialLocalSelectedIncoming ring root e B
          ⟨0, by omega⟩ hx hy ht ⟨rfl, hin⟩
      have hrawMode :
          (GrantBankReference.incomingRootBankMap
            (GrantBankReference.bankLocalReferenceCell B
              ⟨0, by omega⟩)).mode = .RESET := by
        rw [hfield] at hnew
        exact hnew
      have hsource :
          (GrantBankReference.bankLocalReferenceCell B
            ⟨0, by omega⟩).mode ≠ .RESET := hold
      have hrawLease :
          (GrantBankReference.incomingRootBankMap
            (GrantBankReference.bankLocalReferenceCell B
              ⟨0, by omega⟩)).lease = 0 :=
        bankTrialRecoveryIncomingNewResetZero
          (GrantBankReference.bankLocalReferenceCell B
            ⟨0, by omega⟩) hsource hrawMode
      rw [hfield]
      exact bankTrialRecoveryClampedZero q _ hrawLease
    · have hframe := bankTrialLocalRootNonincidentFrame
        ring root e B hfalse he hin
      rw [hframe] at hnew
      exact False.elim (hold hnew)

/-- The last missing first-entry field is zero root lease.
Both OLD-LIVE premises are proved on every CLEAN scheduler word. -/
theorem bankTrialDurationRecoveryFirstEntryLeaseZeroHolds
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q) :
    BankTrialDurationRecoveryFirstEntryLeaseZero
      (q := q) ring root := by
  intro S hclean z hz e hlive hrec
  rcases hlive with ⟨begun, hphase⟩
  cases z with
  | mk B phase =>
    cases hphase
    obtain ⟨w, hword⟩ := hz
    have hfalse : B.success = false :=
      bankTrialProbabilityCleanLiveUnlatched
        ring root S hclean w B begun hword
    have hold :
        bankTrialLiveWaveRootMode B ≠ .RESET :=
      bankTrialDurationRecoveryEntryOldNotReset
        ring root hw S hclean
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        ⟨w, hword⟩ begun rfl
    have hnew :
        ((GrantBankReference.bankLocalReferenceStepClamped
          ring root B e).fields ⟨0, by omega⟩).1 = .RESET :=
      bankTrialLocalLiveRecoveryRoot ring root e B begun hrec
    rw [bankTrialLocalNextLiveBank]
    exact bankTrialRecoveryRootStepNewResetZero
      ring root e B hfalse hold hnew

theorem bankTrialDurationRecoveryFirstEntryFrontHolds
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q) :
    BankTrialDurationRecoveryFirstEntryFront (q := q)
      ring root := by
  exact bankTrialDurationRecoveryFirstEntryFrontOfLeaseZero
    ring root
    (bankTrialDurationRecoveryFirstEntryLeaseZeroHolds
      ring root hsmall hw)

/-- A post-letter RECOVERY state is a FRONT, for any cut
already known to satisfy the reachable-front invariant. -/
private theorem bankTrialRecoverySafeNext {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hrows : BankTrialDurationRecoveryAllRows (q := q) ring root)
    (hentry : BankTrialDurationRecoveryFirstEntryFront
      (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalClean q S)
    (z : BankTrialLocalState q)
    (hz : BankTrialDurationReachable ring root S z)
    (hsafe : z.phase = .recovery →
      BankTrialDurationRecoveryFront q z) :
    (bankTrialLocalNext ring root z e).phase = .recovery →
      BankTrialDurationRecoveryFront q
        (bankTrialLocalNext ring root z e) := by
  intro hrec
  cases hp : z.phase with
  | live begun =>
    exact hentry S hc z hz e ⟨begun, hp⟩ hrec
  | recovery =>
    have hf := hsafe hp
    rcases (hrows z e hf).1 with ht | hfnext
    · rcases ht with hw | hl
      · rw [hrec] at hw
        cases hw
      · rw [hrec] at hl
        cases hl
    · exact hfnext
  | won =>
    have ht : bankTrialLocalTerminal z := Or.inl hp
    have heq := bankTrialLocalTerminalAbsorbs ring root e z ht
    rw [heq, hp] at hrec
    cases hrec
  | lost =>
    have ht : bankTrialLocalTerminal z := Or.inr hp
    have heq := bankTrialLocalTerminalAbsorbs ring root e z ht
    rw [heq, hp] at hrec
    cases hrec

private theorem bankTrialRecoverySafeRun {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hrows : BankTrialDurationRecoveryAllRows (q := q) ring root)
    (hentry : BankTrialDurationRecoveryFirstEntryFront
      (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalClean q S)
    (w : List (Fin n)) :
    ∀ (z : BankTrialLocalState q),
      BankTrialDurationReachable ring root S z →
      (z.phase = .recovery →
        BankTrialDurationRecoveryFront q z) →
      (bankTrialLocalRun ring root w z).phase = .recovery →
        BankTrialDurationRecoveryFront q
          (bankTrialLocalRun ring root w z) := by
  induction w with
  | nil =>
    intro z hz hs hrec
    exact hs hrec
  | cons e es ih =>
    intro z hz hs hrec
    exact ih (bankTrialLocalNext ring root z e)
      (bankTrialDurationReachableNext ring root S z hz e)
      (bankTrialRecoverySafeNext
        ring root e hrows hentry S hc z hz hs) hrec

theorem bankTrialDurationRecoveryReachableFrontHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLocalClean q S)
    (z : BankTrialLocalState q)
    (hz : BankTrialDurationReachable ring root S z)
    (hrec : z.phase = .recovery) :
    BankTrialDurationRecoveryFront q z := by
  obtain ⟨w, hword⟩ := hz
  have hstart :
      BankTrialDurationReachable ring root S
        (bankTrialLocalStart S) := ⟨[], rfl⟩
  have hs :
      (bankTrialLocalStart S).phase = .recovery →
        BankTrialDurationRecoveryFront q
          (bankTrialLocalStart S) := by
    intro h
    cases h
  have hrun := bankTrialRecoverySafeRun
    ring root
    (bankTrialDurationRecoveryAllRowsNonalias
      ring root hsmall hw)
    (bankTrialDurationRecoveryFirstEntryFrontHolds
      ring root hsmall hw)
    S hc w (bankTrialLocalStart S) hstart hs
  rw [hword] at hrun
  exact hrun hrec

private theorem bankTrialRecoveryTwinTerminalClock {n q : Nat}
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

/-- Full reachable occupation drift: no ghost scheduler, no
large-power goal, and the identical finite physical n-edge tape. -/
theorem bankTrialDurationRecoveryOccupationCertificateHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q) :
    BankTrialDurationRecoveryOccupationCertificate
      (q := q) ring root := by
  classical
  intro S hclean
  refine ⟨bankTrialDurationRecoveryTwinOccupation n, ?_, ?_⟩
  · exact Nat.le_of_eq
      (bankTrialDurationRecoveryTwinOccupationSeed S)
  · intro z hz hnot
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
          · exact bankTrialRecoveryTwinTerminalClock
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

/-- Unconditional G12d statement; only established inputs
from the existing branch are referenced. -/
theorem bankTrialDurationRecoveryBudgetHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q) :
    BankTrialDurationRecoveryBudget (q := q) ring root := by
  exact bankTrialDurationRecoveryBudgetOfOccupation
    ring root
    (bankTrialDurationRecoveryOccupationCertificateHolds
      ring root hsmall hw)

end L3

namespace L3

open K2ArbitraryElimination.FiniteAccounting

/-- C.6 on the exact local first-hit clock, unconditional in the
BANK band: the three named budgets are now theorems (race for
n >= 2, worker for 0 < K < 2^b, recovery), each under
useSmall = false and the live-window nonalias condition. -/
theorem bankTrialDurationC6Holds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) (T : Nat) :
    costNumerator (bankTrialLocalNext ring root)
      bankTrialLocalTerminal (bankTrialLocalStart S) T ≤
        n ^ T * ((8 * (compileAdvice q).b + 12) * n) :=
  bankTrialDurationC6OfBudgets ring root
    (bankTrialDurationRaceBudgetDistinctPorts ring hn root)
    (bankTrialDurationWorkerBudgetHolds ring root hsmall hw
      hpositive hK)
    (bankTrialDurationRecoveryBudgetHolds ring root hsmall hw)
    S hclean T

end L3

namespace L3

open Classical
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Event masking never increases the original stopped-cost mass. -/
theorem bankTrialDurationAllKHeadCostLeTotal {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) :
    bankTrialDurationAllKHeadCostMass ring root S T ≤
      costNumerator (bankTrialLocalNext ring root)
        bankTrialLocalTerminal (bankTrialLocalStart S) T := by
  classical
  unfold bankTrialDurationAllKHeadCostMass
  change Prob.scheduleSum n T (fun w =>
      if bankTrialProbabilityHeadEvent ring root w
          (compileAdvice q).K (bankTrialLocalStart S) then
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

/-- C.6 also bounds the masked all-K-head cost, but at the
unconditional n^T scale; this alone is not the C.8 estimate. -/
theorem bankTrialDurationAllKHeadCostC6Holds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (T : Nat) :
    bankTrialDurationAllKHeadCostMass ring root S T ≤
      n ^ T * ((8 * (compileAdvice q).b + 12) * n) := by
  exact Nat.le_trans
    (bankTrialDurationAllKHeadCostLeTotal ring root S T)
    (bankTrialDurationC6Holds ring root hn hsmall hw
      hpositive hK S hclean T)

/-- The missing conditional worker-charge estimate is about
the K-head subdistribution, not the unconditional C.6 mass. -/
def BankTrialDurationAllKHeadChargeEstimate {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
        (compileAdvice q).b),
    BankTrialLocalClean q S →
    (compileAdvice q).useSmall = false →
    2 * (compileAdvice q).bankLeaseCap ≤ n →
    ∀ T : Nat,
      bankTrialDurationAllKHeadCostMass ring root S T ≤
        bankTrialProbabilityHeadMass ring root
          (bankTrialLocalStart S) (compileAdvice q).K T *
          ((2 * (2 * (compileAdvice q).b + 2) + 2) *
            ((compileAdvice q).K + 1) * n)

/-- The distinct missing survival comparison: an adapted
3/4 coupling must transfer K-head mass into WON plus ACTIVE. -/
def BankTrialDurationAllKHeadSurvivalEstimate {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
        (compileAdvice q).b),
    BankTrialLocalClean q S →
    (compileAdvice q).useSmall = false →
    2 * (compileAdvice q).bankLeaseCap ≤ n →
    ∀ T : Nat,
      3 * bankTrialProbabilityHeadMass ring root
        (bankTrialLocalStart S) (compileAdvice q).K T ≤
      4 * (bankTrialProbabilityWinMass ring root S T +
        bankTrialDurationActiveMass ring root S T)

/-- The exact Nat multiplication needed to combine the two
event-conditioned estimates; no independence is assumed. -/
private theorem bankTrialDurationHeadChargeSurvivalArithmetic
    (allCost headMass nonfailure worker : Nat)
    (hcost : allCost ≤ headMass * worker)
    (hsurvival : 3 * headMass ≤ 4 * nonfailure) :
    3 * allCost ≤ 4 * nonfailure * worker := by
  calc
    3 * allCost ≤ 3 * (headMass * worker) :=
      Nat.mul_le_mul_left 3 hcost
    _ = (3 * headMass) * worker := by
      simp only [Nat.mul_assoc]
    _ ≤ (4 * nonfailure) * worker :=
      Nat.mul_le_mul_right worker hsurvival
    _ = 4 * nonfailure * worker := rfl

/-- C.8 reduces to a labelled-head conditional charge and
a survival mass comparison. Neither follows from C.6 alone. -/
theorem bankTrialDurationAllKHeadWorkerPathCostOfEstimates
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hcharge : BankTrialDurationAllKHeadChargeEstimate
      (q := q) ring root)
    (hsurvival : BankTrialDurationAllKHeadSurvivalEstimate
      (q := q) ring root) :
    BankTrialDurationAllKHeadWorkerPathCost (q := q)
      ring root := by
  intro S hclean hsmall hlarge T _
  exact bankTrialDurationHeadChargeSurvivalArithmetic
    (bankTrialDurationAllKHeadCostMass ring root S T)
    (bankTrialProbabilityHeadMass ring root
      (bankTrialLocalStart S) (compileAdvice q).K T)
    (bankTrialProbabilityWinMass ring root S T +
      bankTrialDurationActiveMass ring root S T)
    ((2 * (2 * (compileAdvice q).b + 2) + 2) *
      ((compileAdvice q).K + 1) * n)
    (hcharge S hclean hsmall hlarge T)
    (hsurvival S hclean hsmall hlarge T)

/-- Assemble the C.6 budgets with the existing C.8
conditional theorem. The all-K-head path premise remains open. -/
theorem bankTrialDurationSuccessConditionalSpatialFromPathBudget
    {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hpaths : BankTrialDurationAllKHeadWorkerPathCost
      (q := q) ring root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (T : Nat) :
    bankTrialDurationSuccessCostMass ring root S T ≤
      (bankTrialProbabilityWinMass ring root S T +
        bankTrialDurationActiveMass ring root S T) *
        ((8 * (compileAdvice q).b + 12) *
          ((compileAdvice q).K + 1) * n) := by
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hn : 2 ≤ n := by
    have hcap : 0 < (compileAdvice q).bankLeaseCap := by
      change 0 < 13 * ((compileAdvice q).b + 2)
      omega
    omega
  exact bankTrialDurationSuccessConditionalOfBudgets
    ring root
    (bankTrialDurationRaceBudgetDistinctPorts ring hn root)
    (bankTrialDurationWorkerBudgetHolds ring root hsmall hw
      hpositive hK)
    (bankTrialDurationRecoveryBudgetHolds ring root hsmall hw)
    hpaths S hclean hsmall hlarge T

/-- Exact target Prop in the spatial band, CONDITIONAL on hpaths.
This is not an unconditional closure of G12e. -/
theorem bankTrialDurationSuccessConditionalHolds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hpaths : BankTrialDurationAllKHeadWorkerPathCost
      (q := q) ring root) :
    BankTrialDurationSuccessConditionalTarget (q := q)
      ring root := by
  intro S hclean T
  exact bankTrialDurationSuccessConditionalSpatialFromPathBudget
    ring root hsmall hlarge hpositive hK hpaths S hclean T

end L3

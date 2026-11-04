import Leader.PPL.Elim.Attempt

/-!
# LD(736): moderate one-attempt cost

This bounded round proves the generic finite-tree machinery that was missing
for `attemptCostNumerator`:

* an invariant-restricted Bellman bound;
* the sequential-composition rule: a cost supersolution plus a
  zero-cost continuation supersolution adds without paying the current
  interaction twice;
* the exact junk-start estimate;
* the paper-budget arithmetic.

The remaining physical obligation is isolated as one stage-level Prop,
`ModerateLiveStageSuperSolutionSpec`.  It asks only for the reachable
live-stage invariant and its assembled potential.  In the intended discharge
the potential is the sequential sum of

  3*n*a, n*(5*b-1), 5*n*a, n*(2*b-2),

using the proved CR / controlled-vulnerable rows and the sealed phase closure.
-/

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree

/-! ## Generic attempt-cost sequential composition -/

theorem attemptCostNumerator_success_eq_zero
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n) (T : Nat) :
    attemptCostNumerator K (.success) T = 0 := by
  cases T <;> rfl

theorem attemptCostNumerator_retry_eq_zero
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n) (s : S) (T : Nat) :
    attemptCostNumerator K (.retry s) T = 0 := by
  cases T <;> rfl

/-- Potential of an attempt node; both terminal kinds carry zero continuation
potential. -/
def attemptNodePotential
    {A S : Type} (P : A → Nat) :
    AttemptNode A S → Nat
  | .active a => P a
  | .success => 0
  | .retry _ => 0

/-- Bellman supersolution on an invariant set of active attempt states. -/
def AttemptCostSuperSolutionOn
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (good : A → Prop) (P : A → Nat) : Prop :=
  ∀ a, good a →
    n +
        (List.ofFn (fun e : Fin n =>
          attemptNodePotential P (K.step a e))).sum ≤
      n * P a

/-- A continuation potential is transported through the current stage without
charging another interaction.  This is the object needed for sequential
composition. -/
def AttemptContinuationSuperSolutionOn
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (good : A → Prop) (Q : A → Nat) : Prop :=
  ∀ a, good a →
    (List.ofFn (fun e : Fin n =>
      attemptNodePotential Q (K.step a e))).sum ≤
      n * Q a

theorem attemptNodePotential_add
    {A S : Type} (P Q : A → Nat)
    (x : AttemptNode A S) :
    attemptNodePotential (fun a => P a + Q a) x =
      attemptNodePotential P x + attemptNodePotential Q x := by
  cases x <;> rfl

/-- Sequential-composition lemma.

If `P` pays the interactions of the current stage and `Q` is a
zero-cost continuation supersolution transported through that stage, then
`P+Q` pays their sequential composition. -/
theorem attemptCostSuperSolutionOn_add_continuation
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (good : A → Prop) (P Q : A → Nat)
    (hP : AttemptCostSuperSolutionOn K good P)
    (hQ : AttemptContinuationSuperSolutionOn K good Q) :
    AttemptCostSuperSolutionOn K good (fun a => P a + Q a) := by
  intro a ha
  have hp := hP a ha
  have hq := hQ a ha
  have hsum :
      (List.ofFn (fun e : Fin n =>
        attemptNodePotential (fun z => P z + Q z) (K.step a e))).sum =
        (List.ofFn (fun e : Fin n =>
          attemptNodePotential P (K.step a e))).sum +
        (List.ofFn (fun e : Fin n =>
          attemptNodePotential Q (K.step a e))).sum := by
    rw [← ofFn_sum_add]
    apply ofFn_sum_eq
    intro e
    exact attemptNodePotential_add P Q (K.step a e)
  rw [hsum, Nat.mul_add]
  omega

/-- Finite-horizon attempt-cost bound from an invariant-restricted Bellman
supersolution.  The closure premise is exactly what permits excluding
unreachable junk such as the concrete monitor's `.stuck` state. -/
theorem attemptCostNumerator_le_of_super_on
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (good : A → Prop) (P : A → Nat)
    (hclosed :
      ∀ a e a', good a →
        K.step a e = .active a' → good a')
    (hsuper : AttemptCostSuperSolutionOn K good P) :
    ∀ a, good a → ∀ T,
      attemptCostNumerator K (.active a) T ≤
        n ^ T * P a := by
  intro a ha T
  induction T generalizing a with
  | zero =>
      simp [attemptCostNumerator]
  | succ T ih =>
      change
        n ^ (T + 1) +
            (List.ofFn (fun e : Fin n =>
              attemptCostNumerator K (K.step a e) T)).sum ≤
          n ^ (T + 1) * P a
      have hchild :
          ∀ e : Fin n,
            attemptCostNumerator K (K.step a e) T ≤
              n ^ T * attemptNodePotential P (K.step a e) := by
        intro e
        cases hstep : K.step a e with
        | active a' =>
            have ha' : good a' :=
              hclosed a e a' ha hstep
            have hi := ih a' ha'
            simpa [hstep, attemptNodePotential] using hi
        | success =>
            simp [hstep, attemptNodePotential,
              attemptCostNumerator_success_eq_zero]
        | retry s =>
            simp [hstep, attemptNodePotential,
              attemptCostNumerator_retry_eq_zero]
      have hsum :
          (List.ofFn (fun e : Fin n =>
            attemptCostNumerator K (K.step a e) T)).sum ≤
            n ^ T *
              (List.ofFn (fun e : Fin n =>
                attemptNodePotential P (K.step a e))).sum := by
        calc
          (List.ofFn (fun e : Fin n =>
              attemptCostNumerator K (K.step a e) T)).sum
              ≤
            (List.ofFn (fun e : Fin n =>
              n ^ T * attemptNodePotential P (K.step a e))).sum :=
                ofFn_sum_le _ _ hchild
          _ =
            n ^ T *
              (List.ofFn (fun e : Fin n =>
                attemptNodePotential P (K.step a e))).sum :=
                  ofFn_sum_mul_left (n ^ T) _
      calc
        n ^ (T + 1) +
              (List.ofFn (fun e : Fin n =>
                attemptCostNumerator K (K.step a e) T)).sum
            ≤
          n ^ (T + 1) +
            n ^ T *
              (List.ofFn (fun e : Fin n =>
                attemptNodePotential P (K.step a e))).sum :=
                  Nat.add_le_add_left hsum _
        _ =
          n ^ T *
            (n +
              (List.ofFn (fun e : Fin n =>
                attemptNodePotential P (K.step a e))).sum) := by
                  simp [Nat.pow_succ, Nat.mul_add,
                    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ ≤ n ^ T * (n * P a) :=
          Nat.mul_le_mul_left (n ^ T) (hsuper a ha)
        _ = n ^ (T + 1) * P a := by
          simp [Nat.pow_succ, Nat.mul_assoc,
            Nat.mul_left_comm, Nat.mul_comm]

/-- Direct finite-horizon form of the sequential-composition lemma. -/
theorem attemptCostNumerator_sequential_le
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (good : A → Prop) (P Q : A → Nat)
    (hclosed :
      ∀ a e a', good a →
        K.step a e = .active a' → good a')
    (hP : AttemptCostSuperSolutionOn K good P)
    (hQ : AttemptContinuationSuperSolutionOn K good Q)
    (a : A) (ha : good a) (T : Nat) :
    attemptCostNumerator K (.active a) T ≤
      n ^ T * (P a + Q a) := by
  exact
    attemptCostNumerator_le_of_super_on
      K good (fun z => P z + Q z)
      hclosed
      (attemptCostSuperSolutionOn_add_continuation
        K good P Q hP hQ)
      a ha T

/-! ## Moderate paper arithmetic and junk starts -/

/-- The four paper pieces before the deliberately loose headline constant. -/
def moderatePaperAttemptBudget (n a b : Nat) : Nat :=
  3 * n * a +
    n * (5 * b - 1) +
    5 * n * a +
    n * (2 * b - 2)

/-- In the concrete monitor the target preparation can be split as a
`3*n*b` CleanReady phase followed by one expected incoming-edge wait.
For `b ≥ 2` this fits inside the paper's `n*(5*b-1)` allowance. -/
theorem moderate_target_preparation_le_paper
    (n b : Nat) (hb : 2 ≤ b) :
    3 * n * b + n ≤ n * (5 * b - 1) := by
  have hlin : 3 * b + 1 ≤ 5 * b - 1 := by
    omega
  have hmul :=
    Nat.mul_le_mul_left n hlin
  calc
    3 * n * b + n =
        n * (3 * b) + n := by
          rw [show 3 * n * b = n * (3 * b) by ac_rfl]
    _ = n * (3 * b) + n * 1 := by
          simp
    _ = n * (3 * b + 1) := by
          rw [Nat.mul_add]
    _ ≤ n * (5 * b - 1) := hmul

/-- The exact paper sum is strictly stronger than the requested
`n*(8a+7b)` headline. -/
theorem moderatePaperAttemptBudget_le
    (n a b : Nat) :
    moderatePaperAttemptBudget n a b ≤
      n * (8 * a + 7 * b) := by
  have h5 :
      n * (5 * b - 1) ≤ 5 * (n * b) := by
    calc
      n * (5 * b - 1) ≤ n * (5 * b) :=
        Nat.mul_le_mul_left n (Nat.sub_le _ _)
      _ = 5 * (n * b) := by
        ac_rfl
  have h2 :
      n * (2 * b - 2) ≤ 2 * (n * b) := by
    calc
      n * (2 * b - 2) ≤ n * (2 * b) :=
        Nat.mul_le_mul_left n (Nat.sub_le _ _)
      _ = 2 * (n * b) := by
        ac_rfl
  have hmid :
      3 * (n * a) +
          n * (5 * b - 1) +
          5 * (n * a) +
          n * (2 * b - 2) ≤
        3 * (n * a) +
          5 * (n * b) +
          5 * (n * a) +
          2 * (n * b) := by
    omega
  calc
    moderatePaperAttemptBudget n a b =
        3 * (n * a) +
          n * (5 * b - 1) +
          5 * (n * a) +
          n * (2 * b - 2) := by
            simp [moderatePaperAttemptBudget, Nat.mul_assoc]
    _ ≤
        3 * (n * a) +
          5 * (n * b) +
          5 * (n * a) +
          2 * (n * b) := hmid
    _ = 8 * (n * a) + 7 * (n * b) := by
          omega
    _ = n * (8 * a) + n * (7 * b) := by
          rw [show 8 * (n * a) = n * (8 * a) by ac_rfl,
            show 7 * (n * b) = n * (7 * b) by ac_rfl]
    _ = n * (8 * a + 7 * b) := by
          rw [Nat.mul_add]

private theorem moderateCost_sum_ofFn_zero :
    ∀ m : Nat, (List.ofFn (fun _ : Fin m => (0 : Nat))).sum = 0
  | 0 => rfl
  | m + 1 => by
      rw [List.ofFn_succ, List.sum_cons, moderateCost_sum_ofFn_zero m]

/-- A bad input is started in `.junk`; it consumes exactly one scheduler
interaction and then succeeds.  This proves its contribution directly rather
than putting junk states into the live-stage invariant. -/
theorem moderateAttemptCost_junk_le
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (s : Config n)
    (hbad : ¬ AttemptGood ring F s) :
    ∀ T,
      attemptCostNumerator
          (moderateAttemptKernel ring F)
          (.active ((moderateAttemptKernel ring F).start s)) T ≤
        n ^ T * (n * (8 * F.a + 7 * F.b)) := by
  classical
  intro T
  have hstart :
      (moderateAttemptKernel ring F).start s =
        (.junk s : ModerateAttemptState ring F) := by
    simp [moderateAttemptKernel, moderateStart, hbad]
  cases T with
  | zero =>
      simp [attemptCostNumerator]
  | succ T =>
      rw [hstart]
      have hcost :
          attemptCostNumerator
              (moderateAttemptKernel ring F)
              (.active (.junk s)) (T + 1) =
            n ^ (T + 1) := by
        simp [attemptCostNumerator, moderateAttemptKernel,
          moderateStep, attemptCostNumerator_success_eq_zero,
          moderateCost_sum_ofFn_zero]
      rw [hcost]
      have hn : 0 < n := by
        have hlt := F.B.gap_lt_n
        rw [F.B_gap] at hlt
        omega
      have hweight :
          0 < 8 * F.a + 7 * F.b := by
        omega
      have hprod :
          0 < n * (8 * F.a + 7 * F.b) :=
        Nat.mul_pos hn hweight
      have hcoef :
          1 ≤ n * (8 * F.a + 7 * F.b) := by
        omega
      calc
        n ^ (T + 1) =
            n ^ (T + 1) * 1 := by simp
        _ ≤
            n ^ (T + 1) *
              (n * (8 * F.a + 7 * F.b)) :=
          Nat.mul_le_mul_left (n ^ (T + 1)) hcoef

/-! ## Single remaining live-stage fact -/

/-- The one remaining physical stage-level fact.

A discharge should take `good` to the reachable live-stage invariant:
it records the correct CR mode in the two CR stages, `PhaseHolds` for the
sealed phases, target unshieldedness in the vulnerable stage, and excludes
`.stuck`.  The potential `P` is the sequential stage potential assembled
with `attemptCostSuperSolutionOn_add_continuation`.

The four initial allowances are exactly

  * `3*n*a`          -- attacker CleanReady,
  * `n*(5*b-1)`     -- target CleanReady + first incoming dummy,
  * `5*n*a`         -- raw vulnerable trial dominated by the controlled Q row,
  * `n*(2*b-2)`     -- live/return recovery debt.

The cited proved assets (`cleanReady_cost_proved`,
`controlRowSpec_proved`, `qTrial_cost_five_na`, and sealed closure)
are precisely the stage producers needed to prove this Prop. -/
def ModerateLiveStageSuperSolutionSpec : Prop :=
  ∀ (hSealed : SealedStepSpec),
    ∀ {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0),
      2 ≤ F.b →
      ∃ good : ModerateAttemptState ring F → Prop,
        ∃ P : ModerateAttemptState ring F → Nat,
          (∀ s, AttemptGood ring F s →
            good ((moderateAttemptKernel ring F).start s)) ∧
          (∀ a e a',
            good a →
            (moderateAttemptKernel ring F).step a e = .active a' →
            good a') ∧
          AttemptCostSuperSolutionOn
            (moderateAttemptKernel ring F) good P ∧
          (∀ s, AttemptGood ring F s →
            P ((moderateAttemptKernel ring F).start s) ≤
              moderatePaperAttemptBudget n F.a F.b)

/-- Once the single live-stage supersolution above is supplied,
the repository's exact `ModerateAttemptCostSpec` follows for every start.
Bad starts are discharged by `moderateAttemptCost_junk_le`. -/
theorem moderateAttemptCostSpec_of_live_stage
    (hStage : ModerateLiveStageSuperSolutionSpec) :
    ModerateAttemptCostSpec := by
  unfold ModerateAttemptCostSpec
  intro hSealed n ring C0 F hb _hab s T
  by_cases hs : AttemptGood ring F s
  · rcases hStage hSealed ring F hb with
      ⟨good, P, hstart, hclosed, hsuper, hbudget⟩
    have hcost :=
      attemptCostNumerator_le_of_super_on
        (moderateAttemptKernel ring F) good P
        hclosed hsuper
        ((moderateAttemptKernel ring F).start s)
        (hstart s hs) T
    calc
      attemptCostNumerator
            (moderateAttemptKernel ring F)
            (.active ((moderateAttemptKernel ring F).start s)) T
          ≤
        n ^ T *
          P ((moderateAttemptKernel ring F).start s) :=
            hcost
      _ ≤
        n ^ T *
          moderatePaperAttemptBudget n F.a F.b :=
            Nat.mul_le_mul_left (n ^ T) (hbudget s hs)
      _ ≤
        n ^ T * (n * (8 * F.a + 7 * F.b)) :=
            Nat.mul_le_mul_left (n ^ T)
              (moderatePaperAttemptBudget_le n F.a F.b)
  · exact
      moderateAttemptCost_junk_le
        ring F hb s hs T

#print axioms PPL.Convergence.LDLocal.attemptCostNumerator_sequential_le
#print axioms PPL.Convergence.LDLocal.moderateAttemptCost_junk_le
#print axioms PPL.Convergence.LDLocal.moderateAttemptCostSpec_of_live_stage

end PPL.Convergence.LDLocal

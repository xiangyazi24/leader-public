import Leader.L3.ProbStages
import Leader.PPL.Elim.LocalDeletionCounting

namespace L3.Prob

set_option autoImplicit false
set_option Elab.async false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal
  (AttemptNode RetryKernel attemptCostNumerator retryCount
   repeatCostActive repeatCostNumerator)

/-!
Exact finite-word renewal and origin counting.
All times count raw scheduler letters. A retry reinitializes only
an attempt, without consuming another letter. No independence of
attempts, trial successes, or target times is assumed.
-/

abbrev scheduleSum (n T : Nat) (f : List (Fin n) → Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n T f

private theorem ss_zero {n : Nat} (f : List (Fin n) → Nat) :
    scheduleSum n 0 f = f [] := by
  simp [scheduleSum, FixedSpanRenewalPayload.wordSum, allSchedules]

private theorem ss_succ {n : Nat} (T : Nat)
    (f : List (Fin n) → Nat) :
    scheduleSum n (T + 1) f =
      (List.ofFn (fun e : Fin n =>
        scheduleSum n T (fun w => f (e :: w)))).sum :=
  FixedSpanRenewalPayload.wordSum_succ n T f

private theorem ss_const {n : Nat} (T c : Nat) :
    scheduleSum n T (fun _ => c) = n ^ T * c := by
  change FixedSpanRenewalPayload.wordSum n T (fun _ => c) = _
  rw [← FixedSpanRenewalPayload.rawWord_sum n T (fun _ => c)]
  exact ofFn_sum_const (n ^ T) c

private theorem ss_add {n : Nat} (T : Nat)
    (f g : List (Fin n) → Nat) :
    scheduleSum n T (fun w => f w + g w) =
      scheduleSum n T f + scheduleSum n T g := by
  change FixedSpanRenewalPayload.wordSum n T (fun w => f w + g w) =
    FixedSpanRenewalPayload.wordSum n T f +
      FixedSpanRenewalPayload.wordSum n T g
  rw [← FixedSpanRenewalPayload.rawWord_sum n T (fun w => f w + g w),
    ← FixedSpanRenewalPayload.rawWord_sum n T f,
    ← FixedSpanRenewalPayload.rawWord_sum n T g]
  exact ofFn_sum_add _ _

private theorem ss_mono {n : Nat} (T : Nat)
    (f g : List (Fin n) → Nat) (h : ∀ w, f w ≤ g w) :
    scheduleSum n T f ≤ scheduleSum n T g := by
  change FixedSpanRenewalPayload.wordSum n T f ≤
    FixedSpanRenewalPayload.wordSum n T g
  rw [← FixedSpanRenewalPayload.rawWord_sum n T f,
    ← FixedSpanRenewalPayload.rawWord_sum n T g]
  exact ofFn_sum_le _ _ (fun i => h _)

/-! ## Exact ceiling arithmetic -/

/-- Quotient plus one exactly when the remainder is nonzero. -/
def ceilNat (a d : Nat) : Nat :=
  a / d + if a % d = 0 then 0 else 1

private theorem le_mul_ceilNat (a d : Nat) (hd : 0 < d) :
    a ≤ d * ceilNat a d := by
  have he : d * (a / d) + a % d = a := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod a d
  have hr := Nat.mod_lt a hd
  by_cases hz : a % d = 0
  · simp only [ceilNat, if_pos hz, Nat.add_zero]
    omega
  · simp only [ceilNat, if_neg hz, Nat.mul_add, Nat.mul_one]
    omega

/-- The exact natural ceiling of B / (1 - num/den). -/
def renewalCeiling (B num den : Nat) : Nat :=
  ceilNat (B * den) (den - num)

/-- The rounded reserve pays one attempt and its failed continuation. -/
theorem renewalCeiling_budget (B num den : Nat) (h : num < den) :
    den * B + num * renewalCeiling B num den ≤
      den * renewalCeiling B num den := by
  have hd : 0 < den - num := by omega
  have hc : den * B ≤ (den - num) * renewalCeiling B num den := by
    simpa only [renewalCeiling, Nat.mul_comm] using
      le_mul_ceilNat (B * den) (den - num) hd
  have he : (den - num) + num = den :=
    Nat.sub_add_cancel (Nat.le_of_lt h)
  calc
    den * B + num * renewalCeiling B num den ≤
        (den - num) * renewalCeiling B num den +
          num * renewalCeiling B num den :=
      Nat.add_le_add_right hc _
    _ = ((den - num) + num) * renewalCeiling B num den := by
      rw [Nat.add_mul]
    _ = den * renewalCeiling B num den := by rw [he]

/-! ## Literal static-Fail specification: valid but degenerate -/

open Classical in
/-- First-hit indicator including time zero. Good wins ties. -/
noncomputable def failureFirstWord {S : Type} {n : Nat}
    (next : S → Fin n → S) (Good Fail : S → Prop) :
    S → List (Fin n) → Nat
  | x, [] => if Good x then 0 else if Fail x then 1 else 0
  | x, e :: w =>
      if Good x then 0 else if Fail x then 1
      else failureFirstWord next Good Fail (next x e) w

noncomputable def failureFirstCount {S : Type} {n : Nat}
    (next : S → Fin n → S) (Good Fail : S → Prop)
    (x : S) (T : Nat) : Nat :=
  scheduleSum n T (failureFirstWord next Good Fail x)

/-- The literal Part-A premises imply Fail is already contained in Good.
    This theorem records the exact requested implication, but is NOT the
    nontrivial retry theorem used below. -/
theorem static_renewal_le {S : Type} {n : Nat}
    (next : S → Fin n → S) (Good Fail R : S → Prop)
    (B num den : Nat) (hrho : num < den)
    (hcost : ∀ x, R x → ∀ T,
      costNumerator next (fun y => Good y ∨ Fail y) x T ≤ n ^ T * B)
    (hfail : ∀ x, R x → ∀ T,
      den * failureFirstCount next Good Fail x T ≤ num * n ^ T)
    (hrestart : ∀ x, Fail x → R x) :
    ∀ x, R x → ∀ T,
      costNumerator next Good x T ≤
        n ^ T * renewalCeiling B num den := by
  classical
  have hFG : ∀ x, Fail x → Good x := by
    intro x hf
    apply Classical.byContradiction
    intro hg
    have h0 := hfail x (hrestart x hf) 0
    have hbad : den ≤ num := by
      simpa [failureFirstCount, ss_zero, failureFirstWord, hg, hf] using h0
    omega
  have hb : B ≤ renewalCeiling B num den := by
    have hbudget := renewalCeiling_budget B num den hrho
    have hmul : den * B ≤ den * renewalCeiling B num den := by omega
    exact Nat.le_of_mul_le_mul_left hmul (by omega)
  intro x hx T
  calc
    costNumerator next Good x T ≤
        costNumerator next (fun y => Good y ∨ Fail y) x T :=
      costNumerator_target_mono next (fun y => Good y ∨ Fail y) Good
        (fun y hy => hy.elim (fun h => h) (hFG y)) x T
    _ ≤ n ^ T * B := hcost x hx T
    _ ≤ n ^ T * renewalCeiling B num den := Nat.mul_le_mul_left _ hb

/-! ## Nondegenerate attempts and exact failure-word counts -/

def attemptGood {A Seed : Type} : AttemptNode A Seed → Prop
  | .success => True
  | _ => False

def attemptFail {A Seed : Type} : AttemptNode A Seed → Prop
  | .retry _ => True
  | _ => False

/-- Both terminal tags are absorbing for a single attempt only. -/
def attemptStepper {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) :
    AttemptNode A Seed → Fin n → AttemptNode A Seed
  | .active a, e => K.step a e
  | .success, _ => .success
  | .retry s, _ => .retry s

/-- Single-attempt accounting is precisely the costNumerator. -/
theorem attempt_costNumerator_eq {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) :
    ∀ z T,
      costNumerator (attemptStepper K)
        (fun q => attemptGood q ∨ attemptFail q) z T =
        attemptCostNumerator K z T := by
  classical
  intro z T
  induction T generalizing z with
  | zero => rfl
  | succ T ih =>
      cases z with
      | success =>
          rw [costNumerator_terminal (attemptStepper K)
            (fun q => attemptGood q ∨ attemptFail q)
            .success (by exact Or.inl True.intro) (T + 1)]
          rfl
      | retry s =>
          rw [costNumerator_terminal (attemptStepper K)
            (fun q => attemptGood q ∨ attemptFail q)
            (.retry s) (by exact Or.inr True.intro) (T + 1)]
          rfl
      | active a =>
          have hn : ¬ (attemptGood (.active a : AttemptNode A Seed) ∨
              attemptFail (.active a : AttemptNode A Seed)) := by
            simp [attemptGood, attemptFail]
          rw [costNumerator_succ (attemptStepper K)
            (fun q => attemptGood q ∨ attemptFail q) (.active a) hn T]
          change n ^ (T + 1) +
              (List.ofFn (fun e : Fin n =>
                costNumerator (attemptStepper K)
                  (fun q => attemptGood q ∨ attemptFail q) (K.step a e) T)).sum =
            n ^ (T + 1) +
              (List.ofFn (fun e : Fin n =>
                attemptCostNumerator K (K.step a e) T)).sum
          exact congrArg (fun v : Nat => n ^ (T + 1) + v)
            (ofFn_sum_eq _ _ (fun e => ih (K.step a e)))

/-- Indicator that this attempt has ended in retry by the word's end.
    Once retry is reached, all unused suffix letters are padding. -/
def retryFirstWord {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) :
    AttemptNode A Seed → List (Fin n) → Nat
  | .success, _ => 0
  | .retry _, _ => 1
  | .active _, [] => 0
  | .active a, e :: w => retryFirstWord K (K.step a e) w

/-- retryCount is a genuine cylinder-event count, with denominator n^T. -/
theorem retryCount_eq_wordSum {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) :
    ∀ z T, retryCount K z T = scheduleSum n T (retryFirstWord K z) := by
  intro z T
  induction T generalizing z with
  | zero => cases z <;> simp [retryCount, ss_zero, retryFirstWord]
  | succ T ih =>
      cases z with
      | success =>
          have hf : retryFirstWord K (AttemptNode.success : AttemptNode A Seed)
              = fun _ => 0 := by
            funext w
            cases w <;> rfl
          rw [hf, ss_const]
          simp [retryCount]
      | retry s =>
          have hf : retryFirstWord K (AttemptNode.retry s : AttemptNode A Seed)
              = fun _ => 1 := by
            funext w
            cases w <;> rfl
          rw [hf, ss_const]
          simp [retryCount]
      | active a =>
          rw [retryCount, ss_succ]
          exact ofFn_sum_eq _ _ (fun e => by
            simpa only [retryFirstWord] using ih (K.step a e))

private theorem attemptCostNumerator_active_succ {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) (a : A) (T : Nat) :
    attemptCostNumerator K (AttemptNode.active a) (T + 1) =
      n ^ (T + 1) +
        (List.ofFn (fun e : Fin n =>
          attemptCostNumerator K (K.step a e) T)).sum := by
  simp only [attemptCostNumerator]

private theorem retryCount_active_succ {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) (a : A) (T : Nat) :
    retryCount K (AttemptNode.active a) (T + 1) =
      (List.ofFn (fun e : Fin n => retryCount K (K.step a e) T)).sum := by
  simp only [retryCount]

private def renewalContinuation {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) (z : AttemptNode A Seed) (T : Nat) : Nat :=
  match z with
  | .active a => repeatCostActive K a T
  | .success => 0
  | .retry s => repeatCostNumerator K s T

private theorem renewalContinuation_active {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) (a : A) (T : Nat) :
    renewalContinuation K (AttemptNode.active a) T =
      repeatCostActive K a T := rfl

private theorem renewalContinuation_retry {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) (s : Seed) (T : Nat) :
    renewalContinuation K (AttemptNode.retry s) T =
      repeatCostActive K (K.start s) T := rfl

private theorem repeatCostActive_succ_eq {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) (a : A) (T : Nat) :
    repeatCostActive K a (T + 1) =
      n ^ (T + 1) +
        (List.ofFn (fun e : Fin n =>
          renewalContinuation K (K.step a e) T)).sum := by
  simp only [repeatCostActive]
  exact congrArg (fun v : Nat => n ^ (T + 1) + v)
    (ofFn_sum_eq _ _ (fun e => by
      cases K.step a e <;> rfl))

private def renewalNodeValid {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) (z : AttemptNode A Seed) : Prop :=
  match z with
  | .retry s => K.valid s
  | _ => True

private theorem renewal_child_valid {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) (a : A) (e : Fin n) :
    renewalNodeValid K (K.step a e) := by
  cases h : K.step a e with
  | active a' => trivial
  | success => trivial
  | retry s => exact K.retry_valid a e s h

/-- Retain the exact failed payload and bound only its continuation. -/
private theorem renewal_reserve {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) (C T : Nat)
    (hbound : ∀ t ≤ T, ∀ s, K.valid s →
      repeatCostNumerator K s t ≤ n ^ t * C) :
    ∀ z, renewalNodeValid K z →
      renewalContinuation K z T ≤
        attemptCostNumerator K z T + C * retryCount K z T := by
  induction T with
  | zero =>
      intro z hz
      cases z <;>
        simp [renewalContinuation, repeatCostNumerator, repeatCostActive,
          attemptCostNumerator, retryCount]
  | succ T ih =>
      intro z hz
      cases z with
      | success => simp [renewalContinuation, attemptCostNumerator, retryCount]
      | retry s =>
          have hs := hbound (T + 1) (Nat.le_refl _) s hz
          simpa [renewalContinuation, attemptCostNumerator, retryCount,
            Nat.mul_comm] using hs
      | active a =>
          have hc (e : Fin n) :
              renewalContinuation K (K.step a e) T ≤
                attemptCostNumerator K (K.step a e) T +
                  C * retryCount K (K.step a e) T := by
            apply ih
            · intro t ht s hs
              exact hbound t (by omega) s hs
            · exact renewal_child_valid K a e
          rw [renewalContinuation_active, repeatCostActive_succ_eq,
            attemptCostNumerator_active_succ, retryCount_active_succ]
          have hs := ofFn_sum_le
            (fun e : Fin n => renewalContinuation K (K.step a e) T)
            (fun e : Fin n => attemptCostNumerator K (K.step a e) T +
              C * retryCount K (K.step a e) T) hc
          rw [ofFn_sum_add, ofFn_sum_mul_left] at hs
          omega

/-- Rational retry mass, with an arbitrary integer reserve satisfying
    den*B + num*C <= den*C. This is the finite-horizon renewal proof. -/
theorem retry_cost_le_of_budget {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) (B num den C : Nat)
    (hden : 0 < den) (hbudget : den * B + num * C ≤ den * C)
    (hcost : ∀ s, K.valid s → ∀ T,
      attemptCostNumerator K (.active (K.start s)) T ≤ n ^ T * B)
    (hfail : ∀ s, K.valid s → ∀ T,
      den * retryCount K (.active (K.start s)) T ≤ num * n ^ T) :
    ∀ s, K.valid s → ∀ T,
      repeatCostNumerator K s T ≤ n ^ T * C := by
  intro s hs T
  induction T using Nat.strongRecOn generalizing s with
  | ind T ih =>
      cases T with
      | zero => simp [repeatCostNumerator, repeatCostActive]
      | succ T =>
          have hbound : ∀ t ≤ T, ∀ s', K.valid s' →
              repeatCostNumerator K s' t ≤ n ^ t * C := by
            intro t ht s' hs'
            exact ih t (by omega) s' hs'
          have hc (e : Fin n) :
              renewalContinuation K (K.step (K.start s) e) T ≤
                attemptCostNumerator K (K.step (K.start s) e) T +
                  C * retryCount K (K.step (K.start s) e) T :=
            renewal_reserve K C T hbound _
              (renewal_child_valid K (K.start s) e)
          have hdecomp : repeatCostNumerator K s (T + 1) ≤
              attemptCostNumerator K (.active (K.start s)) (T + 1) +
                C * retryCount K (.active (K.start s)) (T + 1) := by
            have e1 : repeatCostNumerator K s (T + 1) =
                repeatCostActive K (K.start s) (T + 1) := rfl
            rw [e1, repeatCostActive_succ_eq,
              attemptCostNumerator_active_succ, retryCount_active_succ]
            have hsum := ofFn_sum_le
              (fun e : Fin n => renewalContinuation K (K.step (K.start s) e) T)
              (fun e : Fin n =>
                attemptCostNumerator K (K.step (K.start s) e) T +
                  C * retryCount K (K.step (K.start s) e) T) hc
            rw [ofFn_sum_add, ofFn_sum_mul_left] at hsum
            omega
          have htotal : repeatCostNumerator K s (T + 1) ≤
              n ^ (T + 1) * B +
                C * retryCount K (.active (K.start s)) (T + 1) :=
            Nat.le_trans hdecomp (Nat.add_le_add_right (hcost s hs (T + 1)) _)
          have hr := hfail s hs (T + 1)
          have hscaled : den * repeatCostNumerator K s (T + 1) ≤
              den * (n ^ (T + 1) * C) := by
            calc
              den * repeatCostNumerator K s (T + 1) ≤
                  den * (n ^ (T + 1) * B +
                    C * retryCount K (.active (K.start s)) (T + 1)) :=
                Nat.mul_le_mul_left den htotal
              _ = n ^ (T + 1) * (den * B) +
                  C * (den * retryCount K (.active (K.start s)) (T + 1)) := by
                rw [Nat.mul_add]
                congr 1 <;> ac_rfl
              _ ≤ n ^ (T + 1) * (den * B) + C * (num * n ^ (T + 1)) :=
                Nat.add_le_add_left (Nat.mul_le_mul_left C hr) _
              _ = n ^ (T + 1) * (den * B + num * C) := by
                rw [Nat.mul_add]
                congr 1 <;> ac_rfl
              _ ≤ n ^ (T + 1) * (den * C) :=
                Nat.mul_le_mul_left _ hbudget
              _ = den * (n ^ (T + 1) * C) := by ac_rfl
          exact Nat.le_of_mul_le_mul_left hscaled hden

/-- Exact ceiling, not the coarser q*B special case. -/
theorem retry_cost_le_ceiling {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) (B num den : Nat) (hrho : num < den)
    (hcost : ∀ s, K.valid s → ∀ T,
      attemptCostNumerator K (.active (K.start s)) T ≤ n ^ T * B)
    (hfail : ∀ s, K.valid s → ∀ T,
      den * retryCount K (.active (K.start s)) T ≤ num * n ^ T) :
    ∀ s, K.valid s → ∀ T,
      repeatCostNumerator K s T ≤ n ^ T * renewalCeiling B num den :=
  retry_cost_le_of_budget K B num den (renewalCeiling B num den)
    (by omega) (renewalCeiling_budget B num den hrho) hcost hfail

/-! ## Same-word transfer to an arbitrary physical stepper -/

/-- One SAME physical scheduler letter advances both systems. On retry,
    the new comparison starts at the actual reached physical state.
    Success must certify the real target, including any tie case. -/
def RetrySimulation {X A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) (next : X → Fin n → X)
    (Good : X → Prop) (Rel : X → A → Prop) : Prop :=
  ∀ x a, Rel x a → ¬ Good x → ∀ e,
    match K.step a e with
    | .success => Good (next x e)
    | .active a' => Rel (next x e) a'
    | .retry s' => Rel (next x e) (K.start s')

private theorem physical_cost_le_repeat {X A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) (next : X → Fin n → X)
    (Good : X → Prop) (Rel : X → A → Prop)
    (hsim : RetrySimulation K next Good Rel) :
    ∀ x a, Rel x a → ∀ T,
      costNumerator next Good x T ≤ repeatCostActive K a T := by
  classical
  intro x a hrel T
  induction T generalizing x a with
  | zero => simp [repeatCostActive]
  | succ T ih =>
      by_cases hx : Good x
      · rw [costNumerator_terminal next Good x hx (T + 1)]
        exact Nat.zero_le _
      · rw [costNumerator_succ next Good x hx T]
        have hc (e : Fin n) :
            costNumerator next Good (next x e) T ≤
              renewalContinuation K (K.step a e) T := by
          have hh := hsim x a hrel hx e
          cases he : K.step a e with
          | success =>
              have hg : Good (next x e) := by simpa only [he] using hh
              rw [costNumerator_terminal next Good (next x e) hg T]
              exact Nat.zero_le _
          | active a' =>
              have hr : Rel (next x e) a' := by simpa only [he] using hh
              exact ih (next x e) a' hr
          | retry s' =>
              have hr : Rel (next x e) (K.start s') := by
                simpa only [he] using hh
              exact ih (next x e) (K.start s') hr
        rw [repeatCostActive_succ_eq]
        exact Nat.add_le_add_left (ofFn_sum_le _ _ hc) _

/-- Usable Part A. Attempt costs are literally costNumerator, failure
    mass is the exact first-retry word count, and the conclusion is
    the Good-hitting cost of the arbitrary original physical stepper. -/
theorem costNumerator_renewal_le {X A Seed : Type} {n : Nat}
    (next : X → Fin n → X) (Good : X → Prop)
    (K : RetryKernel A Seed n) (Rel : X → A → Prop)
    (hsim : RetrySimulation K next Good Rel)
    (B num den : Nat) (hrho : num < den)
    (hcost : ∀ s, K.valid s → ∀ T,
      costNumerator (attemptStepper K)
        (fun q => attemptGood q ∨ attemptFail q)
        (.active (K.start s)) T ≤ n ^ T * B)
    (hfail : ∀ s, K.valid s → ∀ T,
      den * retryCount K (.active (K.start s)) T ≤ num * n ^ T)
    (x : X) (s : Seed) (hs : K.valid s) (hrel : Rel x (K.start s)) :
    ∀ T, costNumerator next Good x T ≤ n ^ T * renewalCeiling B num den := by
  have hc : ∀ s', K.valid s' → ∀ T,
      attemptCostNumerator K (.active (K.start s')) T ≤ n ^ T * B := by
    intro s' hs' T
    simpa only [attempt_costNumerator_eq] using hcost s' hs' T
  intro T
  calc
    costNumerator next Good x T ≤ repeatCostActive K (K.start s) T :=
      physical_cost_le_repeat K next Good Rel hsim x (K.start s) hrel T
    _ = repeatCostNumerator K s T := rfl
    _ ≤ n ^ T * renewalCeiling B num den :=
      retry_cost_le_ceiling K B num den hrho hc hfail s hs T

/-- The finite-horizon result is the exact expected first-hitting-time
    bound, including almost-sure entrance, in the existing API. -/
theorem expectedHittingTimeAtMost_renewal_le {X A Seed : Type} {n : Nat}
    (hn : 0 < n) (next : X → Fin n → X) (Good : X → Prop)
    (K : RetryKernel A Seed n) (Rel : X → A → Prop)
    (hsim : RetrySimulation K next Good Rel)
    (B num den : Nat) (hrho : num < den)
    (hcost : ∀ s, K.valid s → ∀ T,
      costNumerator (attemptStepper K)
        (fun q => attemptGood q ∨ attemptFail q)
        (.active (K.start s)) T ≤ n ^ T * B)
    (hfail : ∀ s, K.valid s → ∀ T,
      den * retryCount K (.active (K.start s)) T ≤ num * n ^ T)
    (x : X) (s : Seed) (hs : K.valid s) (hrel : Rel x (K.start s)) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      next Good x ((renewalCeiling B num den : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    next Good hn x (renewalCeiling B num den)).2
  exact costNumerator_renewal_le next Good K Rel hsim
    B num den hrho hcost hfail x s hs hrel

/-! ## Part B: stopped creation of origins, unrestricted success suffixes -/

def indicator (b : Bool) : Nat := if b then 1 else 0

/-- A concrete future-success event for a deterministic trial ghost.
    The origin edge is already consumed before this function is called. -/
def trialHits {G : Type} {n : Nat}
    (step : G → Fin n → G) (success : G → Bool) :
    G → List (Fin n) → Bool
  | g, [] => success g
  | g, e :: w => success g || trialHits step success (step g e) w

open Classical in
/-- Origins are created from the pre-state and the current selected edge.
    A list permits the recurring origin and an occasional extra origin
    on the same service. Creation stops at the first Stop state.
    Thus an edge entering Stop is included, as in O_j <= tau. -/
noncomputable def originsWord {S O : Type} {n : Nat}
    (next : S → Fin n → S) (Stop : S → Prop)
    (spawn : S → Fin n → List O) : S → List (Fin n) → Nat
  | _, [] => 0
  | x, e :: w =>
      if Stop x then 0
      else (spawn x e).length + originsWord next Stop spawn (next x e) w

open Classical in
/-- Number of successful origins. Each win o w is evaluated on the
    entire suffix AFTER that origin, not conditioned on a future Stop.
    Only creation of later origins is stopped. -/
noncomputable def successfulOriginsWord {S O : Type} {n : Nat}
    (next : S → Fin n → S) (Stop : S → Prop)
    (spawn : S → Fin n → List O) (win : O → List (Fin n) → Bool) :
    S → List (Fin n) → Nat
  | _, [] => 0
  | x, e :: w =>
      if Stop x then 0
      else ((spawn x e).map (fun o => indicator (win o w))).sum +
        successfulOriginsWord next Stop spawn win (next x e) w

/-- 0/1 indicator that at least one of the counted origins succeeds. -/
noncomputable def originEventWord {S O : Type} {n : Nat}
    (next : S → Fin n → S) (Stop : S → Prop)
    (spawn : S → Fin n → List O) (win : O → List (Fin n) → Bool)
    (x : S) (w : List (Fin n)) : Nat :=
  if successfulOriginsWord next Stop spawn win x w = 0 then 0 else 1

noncomputable def originsNumerator {S O : Type} {n : Nat}
    (next : S → Fin n → S) (Stop : S → Prop)
    (spawn : S → Fin n → List O) (x : S) (T : Nat) : Nat :=
  scheduleSum n T (originsWord next Stop spawn x)

noncomputable def originEventNumerator {S O : Type} {n : Nat}
    (next : S → Fin n → S) (Stop : S → Prop)
    (spawn : S → Fin n → List O) (win : O → List (Fin n) → Bool)
    (x : S) (T : Nat) : Nat :=
  scheduleSum n T (originEventWord next Stop spawn win x)

/-- Finite conditional success bound, separately at each actual origin.
    No condition involving the future target time occurs here. -/
def OriginRarity {S O : Type} {n : Nat}
    (Stop : S → Prop) (spawn : S → Fin n → List O)
    (win : O → List (Fin n) → Bool) (num den : Nat) : Prop :=
  ∀ x, ¬ Stop x → ∀ e o, o ∈ spawn x e → ∀ T,
    den * scheduleSum n T (fun w => indicator (win o w)) ≤ num * n ^ T

private theorem batch_rarity {O : Type} {n : Nat}
    (win : O → List (Fin n) → Bool) (num den T : Nat) :
    ∀ os : List O,
      (∀ o, o ∈ os →
        den * scheduleSum n T (fun w => indicator (win o w)) ≤ num * n ^ T) →
      den * scheduleSum n T
          (fun w => (os.map (fun o => indicator (win o w))).sum) ≤
        num * (n ^ T * os.length) := by
  intro os
  induction os with
  | nil =>
      intro h
      simp [ss_const]
  | cons o os ih =>
      intro h
      have hh := h o (by simp)
      have ht := ih (fun p hp => h p (by simp [hp]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ss_add, Nat.mul_add]
      calc
        den * scheduleSum n T (fun w => indicator (win o w)) +
            den * scheduleSum n T
              (fun w => (os.map (fun p => indicator (win p w))).sum) ≤
            num * n ^ T + num * (n ^ T * os.length) :=
          Nat.add_le_add hh ht
        _ = num * (n ^ T * (os.length + 1)) := by
          simp [Nat.mul_add, Nat.add_comm]

/-- Finite tower-property calculation, before the union bound. -/
private theorem successful_origins_scaled_le {S O : Type} {n : Nat}
    (next : S → Fin n → S) (Stop : S → Prop)
    (spawn : S → Fin n → List O) (win : O → List (Fin n) → Bool)
    (num den : Nat) (hrare : OriginRarity Stop spawn win num den) :
    ∀ x T,
      den * scheduleSum n T (successfulOriginsWord next Stop spawn win x) ≤
        num * originsNumerator next Stop spawn x T := by
  classical
  intro x T
  induction T generalizing x with
  | zero =>
      simp [ss_zero, successfulOriginsWord, originsNumerator, originsWord]
  | succ T ih =>
      have hrow (e : Fin n) :
          den * scheduleSum n T
              (fun w => successfulOriginsWord next Stop spawn win x (e :: w)) ≤
            num * scheduleSum n T
              (fun w => originsWord next Stop spawn x (e :: w)) := by
        by_cases hx : Stop x
        · simp [successfulOriginsWord, originsWord, hx, ss_const]
        · have hb := batch_rarity win num den T (spawn x e)
            (fun o ho => hrare x hx e o ho T)
          have ht := ih (next x e)
          simp only [successfulOriginsWord, originsWord, if_neg hx]
          rw [ss_add, ss_add, ss_const, Nat.mul_add, Nat.mul_add]
          exact Nat.add_le_add hb ht
      have hsum := ofFn_sum_le _ _ hrow
      rw [ofFn_sum_mul_left, ofFn_sum_mul_left] at hsum
      simpa only [originsNumerator, ss_succ] using hsum

/-- Part B: event count <= rarity times the exact stopped origin sum.
    Dividing both sides by den*n^T gives the Wald-type probability
    bound. It has NO additive or independence correction. -/
theorem origin_counting_le {S O : Type} {n : Nat}
    (next : S → Fin n → S) (Stop : S → Prop)
    (spawn : S → Fin n → List O) (win : O → List (Fin n) → Bool)
    (num den : Nat) (hrare : OriginRarity Stop spawn win num den)
    (x : S) (T : Nat) :
    den * originEventNumerator next Stop spawn win x T ≤
      num * originsNumerator next Stop spawn x T := by
  have hu : originEventNumerator next Stop spawn win x T ≤
      scheduleSum n T (successfulOriginsWord next Stop spawn win x) := by
    apply ss_mono
    intro w
    unfold originEventWord
    split <;> omega
  exact Nat.le_trans (Nat.mul_le_mul_left den hu)
    (successful_origins_scaled_le next Stop spawn win num den hrare x T)

/-- F.1's last charge. J is an actual pathwise allowance for extra
    origins, not a correction to the probability/union argument. -/
theorem origin_counting_cost_le {S O : Type} {n : Nat}
    (next : S → Fin n → S) (Stop : S → Prop)
    (spawn : S → Fin n → List O) (win : O → List (Fin n) → Bool)
    (num den J : Nat) (hrare : OriginRarity Stop spawn win num den)
    (x : S)
    (hcharge : ∀ w, originsWord next Stop spawn x w ≤
      costWord next Stop x w + J) (T : Nat) :
    den * originEventNumerator next Stop spawn win x T ≤
      num * (costNumerator next Stop x T + n ^ T * J) := by
  have hc : originsNumerator next Stop spawn x T ≤
      costNumerator next Stop x T + n ^ T * J := by
    calc
      originsNumerator next Stop spawn x T ≤
          scheduleSum n T (fun w => costWord next Stop x w + J) :=
        ss_mono T _ _ hcharge
      _ = costNumerator next Stop x T + n ^ T * J := by
        rw [ss_add, ss_const]
        rfl
  exact Nat.le_trans (origin_counting_le next Stop spawn win num den hrare x T)
    (Nat.mul_le_mul_left num hc)

/-- Uniform reference cost converts F.1 into a horizon-uniform
    divergence-probability numerator bound. -/
theorem origin_counting_budget_le {S O : Type} {n : Nat}
    (next : S → Fin n → S) (Stop : S → Prop)
    (spawn : S → Fin n → List O) (win : O → List (Fin n) → Bool)
    (num den J B : Nat) (hrare : OriginRarity Stop spawn win num den)
    (x : S)
    (hcharge : ∀ w, originsWord next Stop spawn x w ≤
      costWord next Stop x w + J)
    (hcost : ∀ T, costNumerator next Stop x T ≤ n ^ T * B) :
    ∀ T, den * originEventNumerator next Stop spawn win x T ≤
      num * (n ^ T * (B + J)) := by
  intro T
  calc
    den * originEventNumerator next Stop spawn win x T ≤
        num * (costNumerator next Stop x T + n ^ T * J) :=
      origin_counting_cost_le next Stop spawn win num den J hrare x hcharge T
    _ ≤ num * (n ^ T * B + n ^ T * J) :=
      Nat.mul_le_mul_left num (Nat.add_le_add_right (hcost T) _)
    _ = num * (n ^ T * (B + J)) := by rw [← Nat.mul_add]

/-- Ghost-sensitive origins, but a physical stopping target. The exact
    ghost projection theorem removes the ghost from the cost term. -/
theorem origin_counting_ghost_cost_le {S G O : Type} {n : Nat}
    (next : S → Fin n → S) (nextGhost : S × G → Fin n → S × G)
    (hproj : ∀ z e, (nextGhost z e).1 = next z.1 e)
    (Stop : S → Prop) (spawn : S × G → Fin n → List O)
    (win : O → List (Fin n) → Bool) (num den J : Nat)
    (hrare : OriginRarity (fun z : S × G => Stop z.1) spawn win num den)
    (z : S × G)
    (hcharge : ∀ w,
      originsWord nextGhost (fun q => Stop q.1) spawn z w ≤
        costWord nextGhost (fun q => Stop q.1) z w + J) (T : Nat) :
    den * originEventNumerator nextGhost (fun q => Stop q.1) spawn win z T ≤
      num * (costNumerator next Stop z.1 T + n ^ T * J) := by
  have h := origin_counting_cost_le nextGhost (fun q => Stop q.1)
    spawn win num den J hrare z hcharge T
  rw [costNumerator_ghost_eq next nextGhost hproj Stop z T] at h
  exact h

end L3.Prob

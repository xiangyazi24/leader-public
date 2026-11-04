import Leader.PPL.Elim.Attempt
import Leader.PPL.Elim.CleanReadyCost
import Leader.PPL.Elim.ControlRows
import Leader.Core.PredictableTwoTargetFiniteTree
import Leader.Core.PhaseComposition

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree

/-!
# Long-attempt cost

The concrete long monitor contains an intentionally unreachable `.stuck`
state.  Consequently a global Bellman supersolution over *all*
`LongAttemptState` values cannot exist: `.stuck` is an active self-loop on
every scheduler edge.  The generic lemmas below therefore formulate Bellman
and sequential-composition bounds on a closed reachable predicate.  This is
exactly what the long physical start needs, and it does not assign any cost
certificate to junk or malformed ghost states.
-/

@[simp] theorem attemptCostNumerator_success_Long
    {A S : Type} {n : Nat} (K : RetryKernel A S n) :
    ∀ T,
      attemptCostNumerator K (.success : AttemptNode A S) T = 0 := by
  intro T
  cases T <;> rfl

@[simp] theorem attemptCostNumerator_retry_Long
    {A S : Type} {n : Nat} (K : RetryKernel A S n)
    (s : S) :
    ∀ T,
      attemptCostNumerator K (.retry s : AttemptNode A S) T = 0 := by
  intro T
  cases T <;> rfl

/-- Potential of a child node: active children carry Φ, leaves carry 0. -/
def attemptNodePotLong {A S : Type} (Φ : A → Nat) : AttemptNode A S → Nat
  | .active a' => Φ a'
  | .success => 0
  | .retry _ => 0

private theorem longCost_sum_ofFn_zero :
    ∀ m : Nat, (List.ofFn (fun _ : Fin m => (0 : Nat))).sum = 0
  | 0 => rfl
  | m + 1 => by
      rw [List.ofFn_succ, List.sum_cons, longCost_sum_ofFn_zero m]

/--
Reachable Bellman bound for one attempt.

Unlike `NatBellmanSuperSolution`, the row inequality is required only on
`Good`, and active children of `Good` states must stay in `Good`.
Success and retry are both terminal for `attemptCostNumerator`.
-/
theorem attemptCostNumerator_reachableBellman_Long
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (Good : A → Prop)
    (Φ : A → Nat)
    (hclosed :
      ∀ a, Good a →
        ∀ e a', K.step a e = .active a' → Good a')
    (hrow :
      ∀ a, Good a →
        n +
            (List.ofFn (fun e : Fin n =>
              attemptNodePotLong Φ (K.step a e))).sum ≤
          n * Φ a)
    (a : A) (ha : Good a) :
    ∀ T,
      attemptCostNumerator K (.active a) T ≤
        n ^ T * Φ a := by
  intro T
  induction T generalizing a with
  | zero =>
      simp [attemptCostNumerator]
  | succ T ih =>
      let ψ : Fin n → Nat := fun e =>
        attemptNodePotLong Φ (K.step a e)
      have hchild :
          ∀ e : Fin n,
            attemptCostNumerator K (K.step a e) T ≤
              n ^ T * ψ e := by
        intro e
        cases hstep : K.step a e with
        | success =>
            simp [ψ, hstep, attemptNodePotLong]
        | retry s =>
            simp [ψ, hstep, attemptNodePotLong]
        | active a' =>
            have ha' : Good a' :=
              hclosed a ha e a' hstep
            simpa [ψ, hstep, attemptNodePotLong] using ih a' ha'
      have hsum :=
        ofFn_sum_le
          (fun e : Fin n =>
            attemptCostNumerator K (K.step a e) T)
          (fun e : Fin n => n ^ T * ψ e)
          hchild
      rw [ofFn_sum_mul_left] at hsum
      have hr :
          n + (List.ofFn ψ).sum ≤ n * Φ a := by
        simpa [ψ] using hrow a ha
      change
        n ^ (T + 1) +
            (List.ofFn (fun e : Fin n =>
              attemptCostNumerator K (K.step a e) T)).sum ≤
          n ^ (T + 1) * Φ a
      calc
        n ^ (T + 1) +
              (List.ofFn (fun e : Fin n =>
                attemptCostNumerator K (K.step a e) T)).sum
            ≤
          n ^ (T + 1) + n ^ T * (List.ofFn ψ).sum :=
            Nat.add_le_add_left hsum _
        _ = n ^ T * (n + (List.ofFn ψ).sum) := by
          rw [Nat.pow_succ, Nat.mul_add]
        _ ≤ n ^ T * (n * Φ a) :=
          Nat.mul_le_mul_left _ hr
        _ = n ^ (T + 1) * Φ a := by
          rw [Nat.pow_succ]
          ac_rfl

/--
Two-stage sequential composition for `attemptCostNumerator`, restricted to
a closed reachable subgraph.

Phase 1 pays its own masked Bellman potential plus a reserve `C₂`.
Any phase-1 -> phase-2 active crossing must satisfy `E₂`, where the phase-2
entry potential is at most that reserve.  Phase 2 cannot return to phase 1.
This is the reachable analogue of `PhaseComposition.phase_compose_bellman`;
it is usable for the concrete long monitor despite its unreachable
`.stuck` constructor.
-/
theorem attemptCostNumerator_sequentialComposition_Long
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (Good : A → Prop)
    (phase : A → PhaseComposition.TwoPhase)
    (Φ₁ Φ₂ : A → Nat)
    (C₂ : Nat)
    (E₂ : A → Prop)
    (hclosed :
      ∀ a, Good a →
        ∀ e a', K.step a e = .active a' → Good a')
    (hnoBack :
      ∀ a e a', Good a →
        phase a = .p2 →
        K.step a e = .active a' →
        phase a' = .p2)
    (h₁ :
      ∀ a, Good a → phase a = .p1 →
        n +
            (List.ofFn (fun e : Fin n =>
              match K.step a e with
              | .active a' =>
                  if phase a' = .p1 then Φ₁ a' else 0
              | .success => 0
              | .retry _ => 0)).sum ≤
          n * Φ₁ a)
    (h₂ :
      ∀ a, Good a → phase a = .p2 →
        n +
            (List.ofFn (fun e : Fin n =>
              match K.step a e with
              | .active a' => Φ₂ a'
              | .success => 0
              | .retry _ => 0)).sum ≤
          n * Φ₂ a)
    (henter :
      ∀ a e a', Good a →
        phase a = .p1 →
        K.step a e = .active a' →
        phase a' = .p2 →
        E₂ a')
    (hC₂ :
      ∀ a', Good a' → E₂ a' →
        Φ₂ a' ≤ C₂)
    (a : A) (ha : Good a) :
    ∀ T,
      attemptCostNumerator K (.active a) T ≤
        n ^ T *
          (if phase a = .p1 then Φ₁ a + C₂ else Φ₂ a) := by
  let Φ : A → Nat := fun x =>
    if phase x = .p1 then Φ₁ x + C₂ else Φ₂ x
  have hrowΦ :
      ∀ x, Good x →
        n +
            (List.ofFn (fun e : Fin n =>
              match K.step x e with
              | .active y => Φ y
              | .success => 0
              | .retry _ => 0)).sum ≤
          n * Φ x := by
    intro x hx
    cases hph : phase x with
    | p1 =>
        have hchild :
            ∀ e : Fin n,
              (match K.step x e with
               | .active y => Φ y
               | .success => 0
               | .retry _ => 0) ≤
                (match K.step x e with
                 | .active y =>
                     if phase y = .p1 then Φ₁ y else 0
                 | .success => 0
                 | .retry _ => 0) + C₂ := by
          intro e
          cases hstep : K.step x e with
          | success =>
              simp
          | retry s =>
              simp
          | active y =>
              have hy : Good y :=
                hclosed x hx e y hstep
              cases hyph : phase y with
              | p1 =>
                  simp [Φ, hstep, hyph]
              | p2 =>
                  have hE : E₂ y :=
                    henter x e y hx hph hstep hyph
                  have hbound : Φ₂ y ≤ C₂ :=
                    hC₂ y hy hE
                  simpa [Φ, hstep, hyph] using hbound
        have hsum :=
          ofFn_sum_le
            (fun e : Fin n =>
              match K.step x e with
              | .active y => Φ y
              | .success => 0
              | .retry _ => 0)
            (fun e : Fin n =>
              (match K.step x e with
               | .active y =>
                   if phase y = .p1 then Φ₁ y else 0
               | .success => 0
               | .retry _ => 0) + C₂)
            hchild
        calc
          n +
                (List.ofFn (fun e : Fin n =>
                  match K.step x e with
                  | .active y => Φ y
                  | .success => 0
                  | .retry _ => 0)).sum
              ≤
            n +
                (List.ofFn (fun e : Fin n =>
                  (match K.step x e with
                   | .active y =>
                       if phase y = .p1 then Φ₁ y else 0
                   | .success => 0
                   | .retry _ => 0) + C₂)).sum :=
              Nat.add_le_add_left hsum n
          _ =
            (n +
                (List.ofFn (fun e : Fin n =>
                  match K.step x e with
                  | .active y =>
                      if phase y = .p1 then Φ₁ y else 0
                  | .success => 0
                  | .retry _ => 0)).sum) +
              n * C₂ := by
                rw [ofFn_sum_add, ofFn_sum_const, ← Nat.add_assoc]
          _ ≤ n * Φ₁ x + n * C₂ :=
            Nat.add_le_add_right (h₁ x hx hph) (n * C₂)
          _ = n * (Φ₁ x + C₂) := by
            rw [Nat.mul_add]
          _ = n * Φ x := by
            simp [Φ, hph]
    | p2 =>
        have hchild :
            ∀ e : Fin n,
              (match K.step x e with
               | .active y => Φ y
               | .success => 0
               | .retry _ => 0) =
                (match K.step x e with
                 | .active y => Φ₂ y
                 | .success => 0
                 | .retry _ => 0) := by
          intro e
          cases hstep : K.step x e with
          | success =>
              simp
          | retry s =>
              simp
          | active y =>
              have hyph : phase y = .p2 :=
                hnoBack x e y hx hph hstep
              simp [Φ, hstep, hyph]
        have hsum :=
          ofFn_sum_eq
            (fun e : Fin n =>
              match K.step x e with
              | .active y => Φ y
              | .success => 0
              | .retry _ => 0)
            (fun e : Fin n =>
              match K.step x e with
              | .active y => Φ₂ y
              | .success => 0
              | .retry _ => 0)
            hchild
        calc
          n +
                (List.ofFn (fun e : Fin n =>
                  match K.step x e with
                  | .active y => Φ y
                  | .success => 0
                  | .retry _ => 0)).sum
              =
            n +
                (List.ofFn (fun e : Fin n =>
                  match K.step x e with
                  | .active y => Φ₂ y
                  | .success => 0
                  | .retry _ => 0)).sum :=
              congrArg (fun z => n + z) hsum
          _ ≤ n * Φ₂ x :=
            h₂ x hx hph
          _ = n * Φ x := by
            simp [Φ, hph]
  have h :=
    attemptCostNumerator_reachableBellman_Long
      K Good Φ hclosed hrowΦ a ha
  intro T
  simpa [Φ] using h T

/--
The eight paper charges, with the common scheduler factor `n` removed:

* target CR: `3b`;
* attacker CR: `3a`;
* clean-live launch: `2a`;
* retained-bullet advance: `a - 1 - 2b`;
* target race: `2b - 1`;
* incident orientation: `1`;
* retained trial: `2b`;
* recovery: `2b - 2`.
-/
def longAttemptPaperBudgetLong
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) : Nat :=
  3 * F.b +
    3 * F.a +
    2 * F.a +
    (F.a - 1 - 2 * F.b) +
    (2 * F.b - 1) +
    1 +
    2 * F.b +
    (2 * F.b - 2)

theorem longAttemptPaperBudget_le_Long
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (hab : 2 * F.b + 1 ≤ F.a) :
    longAttemptPaperBudgetLong F ≤
      7 * (F.a + F.b) := by
  unfold longAttemptPaperBudgetLong
  omega

theorem longAttemptPaperBudget_scaled_Long
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (hab : 2 * F.b + 1 ≤ F.a) :
    n * longAttemptPaperBudgetLong F ≤
      7 * n * (F.a + F.b) := by
  have h :=
    longAttemptPaperBudget_le_Long F hb hab
  calc
    n * longAttemptPaperBudgetLong F
        ≤ n * (7 * (F.a + F.b)) :=
      Nat.mul_le_mul_left n h
    _ = 7 * n * (F.a + F.b) := by
      ac_rfl

/--
Junk starts consume exactly the first interaction and then terminate.  This is
the branch of `LongAttemptCostSpec` that does not need any physical stage
invariant.
-/
theorem longAttempt_junk_cost_Long
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n)
    (hbad : ¬ AttemptGood ring F s) :
    ∀ T,
      attemptCostNumerator
          (longAttemptKernel ring F)
          (.active ((longAttemptKernel ring F).start s)) T ≤
        n ^ T := by
  classical
  have hstart :
      (longAttemptKernel ring F).start s =
        (.junk s : LongAttemptState ring F) := by
    simp [longAttemptKernel, longStart, hbad]
  have hstep :
      ∀ e : Fin n,
        (longAttemptKernel ring F).step
            (.junk s : LongAttemptState ring F) e =
          .success := by
    intro e
    simp [longAttemptKernel, longStep]
  intro T
  rw [hstart]
  cases T with
  | zero =>
      simp [attemptCostNumerator]
  | succ T =>
      simp [attemptCostNumerator, hstep, longCost_sum_ofFn_zero]

/--
Single remaining long-stage fact.

It asks for a closed set of legitimate active monitor states and one
scheduler-scaled Bellman potential on that set.  The entry budget is exactly
the eight-term paper budget above.  This is deliberately reachable-only:
asking for a global Bellman row would be false because the raw datatype also
contains the unreachable self-looping `.stuck` stage.

The intended proof is the stage wiring:
`crRankStep_proved` for the two CR stages, sealed-step ranks for clean-live
and recovery, predictable service ranks for advance/race/incident, and
`retainedTrial_cost_nr (controlRowSpec_proved ...)` for the retained trial.
`attemptCostNumerator_sequentialComposition_Long` is the generic
composition brick for joining those rows.
-/
def LongStageBellmanCostSpec : Prop :=
  ∀ (hSealed : SealedStepSpec),
    ∀ {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0),
      2 ≤ F.b →
      2 * F.b + 1 ≤ F.a →
      ∃ Good : LongAttemptState ring F → Prop,
      ∃ Φ : LongAttemptState ring F → Nat,
        (∀ s, AttemptGood ring F s →
          Good ((longAttemptKernel ring F).start s)) ∧
        (∀ a, Good a →
          ∀ e a',
            (longAttemptKernel ring F).step a e = .active a' →
            Good a') ∧
        (∀ a, Good a →
          n +
              (List.ofFn (fun e : Fin n =>
                attemptNodePotLong Φ
                  ((longAttemptKernel ring F).step a e))).sum ≤
            n * Φ a) ∧
        (∀ s, AttemptGood ring F s →
          Φ ((longAttemptKernel ring F).start s) ≤
            n * longAttemptPaperBudgetLong F)

/--
The requested `LongAttemptCostSpec` follows from the single stage-level
Bellman certificate.  The junk case is discharged independently.
-/
theorem longAttemptCostSpec_of_stageBellman_Long
    (hStage : LongStageBellmanCostSpec) :
    LongAttemptCostSpec := by
  unfold LongAttemptCostSpec
  intro hSealed n ring C0 F hb hab s T
  by_cases hgood : AttemptGood ring F s
  · obtain
      ⟨Good, Φ, hstartGood, hclosed, hrow, hentry⟩ :=
        hStage hSealed ring F hb hab
    have hg :
        Good ((longAttemptKernel ring F).start s) :=
      hstartGood s hgood
    have hcost :=
      attemptCostNumerator_reachableBellman_Long
        (longAttemptKernel ring F)
        Good Φ hclosed hrow
        ((longAttemptKernel ring F).start s) hg T
    have hentry' :
        Φ ((longAttemptKernel ring F).start s) ≤
          n * longAttemptPaperBudgetLong F :=
      hentry s hgood
    have hpaper :=
      longAttemptPaperBudget_scaled_Long F hb hab
    calc
      attemptCostNumerator
            (longAttemptKernel ring F)
            (.active ((longAttemptKernel ring F).start s)) T
          ≤ n ^ T *
              Φ ((longAttemptKernel ring F).start s) :=
        hcost
      _ ≤ n ^ T * (n * longAttemptPaperBudgetLong F) :=
        Nat.mul_le_mul_left (n ^ T) hentry'
      _ ≤ n ^ T * (7 * n * (F.a + F.b)) :=
        Nat.mul_le_mul_left (n ^ T) hpaper
  · have hj :=
      longAttempt_junk_cost_Long ring F s hgood T
    have habpos : 0 < F.a + F.b := by
      omega
    have hcoefpos :
        0 < 7 * n * (F.a + F.b) := by
      exact
        Nat.mul_pos
          (Nat.mul_pos (by decide) ring.hn)
          habpos
    have hcoef :
        1 ≤ 7 * n * (F.a + F.b) := by
      omega
    calc
      attemptCostNumerator
            (longAttemptKernel ring F)
            (.active ((longAttemptKernel ring F).start s)) T
          ≤ n ^ T := hj
      _ = n ^ T * 1 := by simp
      _ ≤ n ^ T * (7 * n * (F.a + F.b)) :=
        Nat.mul_le_mul_left (n ^ T) hcoef

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.attemptCostNumerator_reachableBellman_Long
#print axioms PPL.Convergence.LDLocal.attemptCostNumerator_sequentialComposition_Long
#print axioms PPL.Convergence.LDLocal.longAttemptPaperBudget_le_Long
#print axioms PPL.Convergence.LDLocal.longAttempt_junk_cost_Long
#print axioms PPL.Convergence.LDLocal.longAttemptCostSpec_of_stageBellman_Long

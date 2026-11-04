import Leader.Core.FiniteUniformStoppingTree

/-!
# Finite scheduler mass under adaptive two-port redirection

Only the comparison audit carries a remaining collapse budget.  The physical
step and the original stopped tree are unchanged.  At a gated state, both
raw choices at the distinguished ports execute the original A row and spend
one unit of budget.  At every other row the budget stays fixed.  A branch
exceeding the budget fails, including when its physical row would succeed.

The main bound compares the actual `FiniteUniformStoppingTree.treeWeight`
trees.  Two copies with budget `m` charge the original A child with factor
`2^(m+1)`; the original B child remains a nonnegative extra.  Thus the factor
is `2^M`, independently of the horizon.  Both terminal constructors absorb
all subsequent padding symbols.
-/

namespace ControlledSchedulerMass

open FiniteUniformStoppingTree

set_option autoImplicit false

/-- State-dependent ports on an alphabet with at least two symbols.
Distinctness is required at every gated state.  These are scheduler data,
with no extra coordinate in the physical state type. -/
structure Redirection (S : Type) (n : Nat) where
  two_le : 2 ≤ n
  gate : S → Bool
  portA : S → Fin n
  portB : S → Fin n
  distinct : ∀ s, gate s = true → portA s ≠ portB s

variable {S : Type} {n : Nat}

/-- The effective symbol: only a gated B choice is redirected to A. -/
def Redirection.effective (r : Redirection S n) (s : S) (e : Fin n) : Fin n :=
  if r.gate s = true ∧ e = r.portB s then r.portA s else e

/-- A collapsed event counts either preimage of the gated A symbol.
In particular, selecting A itself spends budget as well as selecting B. -/
def Redirection.Collapses (r : Redirection S n) (s : S) (e : Fin n) : Prop :=
  r.gate s = true ∧ (e = r.portA s ∨ e = r.portB s)

instance (r : Redirection S n) (s : S) (e : Fin n) :
    Decidable (r.Collapses s e) := inferInstanceAs
      (Decidable (r.gate s = true ∧ (e = r.portA s ∨ e = r.portB s)))

/-- The comparison process applies exactly the original physical row to the
effective symbol. -/
def controlledStep (step : S → Fin n → StopNode S) (r : Redirection S n)
    (s : S) (e : Fin n) : StopNode S :=
  step s (r.effective s e)

/-- Add only proof bookkeeping to an active node, retaining both terminals. -/
def withBudget (m : Nat) : StopNode S → StopNode (S × Nat)
  | .active s => .active (s, m)
  | .success => .success
  | .failure => .failure

/-- Forget the audit budget; this never changes a terminal label. -/
def forgetBudget : StopNode (S × Nat) → StopNode S
  | .active (s, _) => .active s
  | .success => .success
  | .failure => .failure

/-- The comparison audit rejects a collapsed row if no budget remains.
Otherwise it executes the same controlled physical row and decrements exactly
on a collapsed event.  The budget is never a physical state field. -/
def auditStep (step : S → Fin n → StopNode S) (r : Redirection S n)
    (sm : S × Nat) (e : Fin n) : StopNode (S × Nat) :=
  if r.Collapses sm.1 e then
    match sm.2 with
    | 0 => .failure
    | m + 1 => withBudget m (controlledStep step r sm.1 e)
  else withBudget sm.2 (controlledStep step r sm.1 e)

/-- Successful words in the existing stopped tree after censoring exactly
those controlled paths that exceed the collapse budget before absorption. -/
def boundedSuccessCount (step : S → Fin n → StopNode S)
    (r : Redirection S n) (x : StopNode S) (T M : Nat) : Nat :=
  successCount (auditStep step r) (withBudget M x) T

@[simp] theorem forgetBudget_withBudget (m : Nat) (x : StopNode S) :
    forgetBudget (withBudget m x) = x := by cases x <;> rfl

@[simp] theorem withBudget_active (m : Nat) (s : S) :
    withBudget m (.active s) = .active (s, m) := rfl

/-- The retained port always denotes its own physical row. -/
@[simp] theorem Redirection.effective_A (r : Redirection S n) (s : S) :
    r.effective s (r.portA s) = r.portA s := by
  simp [Redirection.effective]

/-- At an open gate the other port executes the A row. -/
theorem Redirection.effective_B (r : Redirection S n) (s : S)
    (hg : r.gate s = true) :
    r.effective s (r.portB s) = r.portA s := by
  simp [Redirection.effective, hg]

/-- A closed gate is the identity on the entire scheduler alphabet. -/
theorem Redirection.effective_of_gate_false (r : Redirection S n) (s : S)
    (hg : r.gate s = false) (e : Fin n) : r.effective s e = e := by
  simp [Redirection.effective, hg]

/-- At an open gate B is absent from the effective alphabet.  Original
successful B trajectories can therefore lie outside the controlled image. -/
theorem Redirection.effective_ne_B (r : Redirection S n) (s : S)
    (hg : r.gate s = true) (e : Fin n) : r.effective s e ≠ r.portB s := by
  by_cases hb : e = r.portB s
  · simpa [Redirection.effective, hg, hb] using r.distinct s hg
  · simp [Redirection.effective, hg, hb]

/-- Every uncollapsed row has the original effective symbol. -/
theorem Redirection.effective_of_not_collapses (r : Redirection S n)
    (s : S) (e : Fin n) (h : ¬ r.Collapses s e) :
    r.effective s e = e := by
  simp only [Redirection.Collapses] at h
  simp only [Redirection.effective]
  split
  · rename_i hrow
    exact False.elim (h ⟨hrow.1, Or.inr hrow.2⟩)
  · rfl

/-! ## Finite sums with one paired charge -/

private theorem nodup_ofFn_injective {k : Nat} {A : Type}
    (f : Fin k → A) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hmem
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
        have h := hf hi
        cases h
      · apply ih
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

private theorem sum_pair_part (a b : Fin n) (f : Fin n → Nat)
    (hab : a ≠ b) :
    (List.ofFn (fun e => if e = a then f a else if e = b then f b else 0)).sum =
      f a + f b := by
  let g : Fin n → Nat := fun e => if e = a then f a else if e = b then f b else 0
  have h := sum_two_exceptions (List.ofFn (fun e : Fin n => e)) a b g 0
    (nodup_ofFn_injective _ Function.injective_id) (List.mem_ofFn.mpr ⟨a, rfl⟩)
    (List.mem_ofFn.mpr ⟨b, rfl⟩) hab (by
      intro e _ hea heb
      simp [g, hea, heb])
  simpa [List.map_ofFn, Function.comp_def, g, hab, Ne.symm hab] using h

/-- A pair of distinct rows may share a charge.  Every other row is compared
pointwise, so no bound on the physical B child is assumed. -/
private theorem sum_le_of_pair (a b : Fin n) (f g : Fin n → Nat)
    (hab : a ≠ b) (hpair : f a + f b ≤ g a + g b)
    (hother : ∀ e, e ≠ a → e ≠ b → f e ≤ g e) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  let rest := fun (v : Fin n → Nat) e => if e = a ∨ e = b then 0 else v e
  have split_sum (v : Fin n → Nat) :
      (List.ofFn v).sum = v a + v b + (List.ofFn (rest v)).sum := by
    calc
      (List.ofFn v).sum =
          (List.ofFn (fun e =>
            (if e = a then v a else if e = b then v b else 0) + rest v e)).sum := by
        apply ofFn_sum_eq
        intro e
        by_cases hea : e = a
        · simp [rest, hea]
        · by_cases heb : e = b <;> simp [rest, hea, heb, Ne.symm hab]
      _ = _ := by rw [ofFn_sum_add, sum_pair_part a b v hab]
  rw [split_sum f, split_sum g]
  apply Nat.add_le_add hpair
  apply ofFn_sum_le
  intro e
  by_cases hea : e = a
  · simp [rest, hea]
  · by_cases heb : e = b
    · simp [rest, heb]
    · simpa [rest, hea, heb] using hother e hea heb

private theorem one_le_two_pow (m : Nat) : 1 ≤ 2 ^ m := by
  exact Nat.one_le_pow m 2 (by decide)

/-! ## The weighted two-tree induction -/

/-- Exact finite-horizon change of measure for any nonnegative common leaf
weight vanishing at failure.  The induction pairs the two collapsed copies
after their budget decrement; no probability or drift inequality is an input. -/
theorem audit_treeWeight_le (step : S → Fin n → StopNode S)
    (r : Redirection S n) (w : StopNode S → Nat) (hfail : w .failure = 0) :
    ∀ (T M : Nat) (x : StopNode S),
      treeWeight (auditStep step r) (fun y => w (forgetBudget y))
          (withBudget M x) T ≤
        2 ^ M * treeWeight step w x T := by
  intro T
  induction T with
  | zero =>
      intro M x
      simpa [treeWeight] using Nat.mul_le_mul_right (w x) (one_le_two_pow M)
  | succ T ih =>
      intro M x
      cases x with
      | success =>
          simp only [withBudget, treeWeight_success, forgetBudget]
          simpa [Nat.mul_assoc] using
            Nat.mul_le_mul_right (n ^ (T + 1) * w .success) (one_le_two_pow M)
      | failure => simp [withBudget, treeWeight_failure, forgetBudget, hfail]
      | active s =>
          simp only [withBudget, treeWeight, stepNode]
          rw [← ofFn_sum_mul_left]
          by_cases hg : r.gate s = true
          · have hab := r.distinct s hg
            cases M with
            | zero =>
                apply ofFn_sum_le
                intro e
                by_cases hc : r.Collapses s e
                · simp [auditStep, hc, treeWeight_failure, forgetBudget, hfail]
                · simpa [auditStep, hc, controlledStep,
                    r.effective_of_not_collapses s e hc] using ih 0 (step s e)
            | succ m =>
                apply sum_le_of_pair (r.portA s) (r.portB s) _ _ hab
                · have hA := ih m (step s (r.portA s))
                  have hB :
                      treeWeight (auditStep step r) (fun y => w (forgetBudget y))
                          (withBudget m (step s (r.portA s))) T +
                        treeWeight (auditStep step r) (fun y => w (forgetBudget y))
                          (withBudget m (step s (r.portA s))) T ≤
                        2 ^ (m + 1) * treeWeight step w (step s (r.portA s)) T := by
                    rw [Nat.pow_succ, Nat.mul_assoc, Nat.two_mul, Nat.mul_add]
                    exact Nat.add_le_add hA hA
                  simp only [auditStep, Redirection.Collapses, hg, true_and,
                    true_or, or_true, if_pos, controlledStep,
                    Redirection.effective_A, r.effective_B s hg]
                  exact Nat.le_trans hB (Nat.le_add_right _ _)
                · intro e hea heb
                  have hc : ¬ r.Collapses s e := by simp [Redirection.Collapses, hea, heb]
                  simpa [auditStep, hc, controlledStep,
                    r.effective_of_not_collapses s e hc] using ih (m + 1) (step s e)
          · apply ofFn_sum_le
            intro e
            have hc : ¬ r.Collapses s e := by simp [Redirection.Collapses, hg]
            simpa [auditStep, hc, controlledStep,
              r.effective_of_not_collapses s e hc] using ih M (step s e)

/-- The controlled successful word count with at most `M` collapsed events
is bounded by `2^M` times the original success count at the same horizon. -/
theorem boundedSuccessCount_le (step : S → Fin n → StopNode S)
    (r : Redirection S n) (x : StopNode S) (T M : Nat) :
    boundedSuccessCount step r x T M ≤ 2 ^ M * successCount step x T := by
  have h := audit_treeWeight_le step r successWeight rfl T M x
  have hw : (fun y : StopNode (S × Nat) => successWeight (forgetBudget y)) =
      successWeight := by funext y; cases y <;> rfl
  simpa [hw, boundedSuccessCount, successCount] using h

/-- Transfer an arbitrary rational lower mass `p/q` without division.
Both inequalities use the exact common word denominator `n^T`. -/
theorem raw_success_mass_lower_scaled (step : S → Fin n → StopNode S)
    (r : Redirection S n) (x : StopNode S) (T M p q : Nat)
    (hmass : p * n ^ T ≤ q * boundedSuccessCount step r x T M) :
    p * n ^ T ≤ (q * 2 ^ M) * successCount step x T := by
  exact Nat.le_trans hmass (by
    simpa [Nat.mul_assoc] using
      Nat.mul_le_mul_left q (boundedSuccessCount_le step r x T M))

/-- Division-free lower mass transfer: a controlled mass of at least `1/k`
within finite horizon and budget yields original mass at least `1/(k*2^M)`.
The common scheduler denominator is exactly `n^T`. -/
theorem raw_success_mass_lower (step : S → Fin n → StopNode S)
    (r : Redirection S n) (x : StopNode S) (T M k : Nat)
    (hmass : n ^ T ≤ k * boundedSuccessCount step r x T M) :
    n ^ T ≤ (k * 2 ^ M) * successCount step x T := by
  exact Nat.le_trans hmass (by
    simpa [Nat.mul_assoc] using
      Nat.mul_le_mul_left k (boundedSuccessCount_le step r x T M))

/-! ## Word semantics and the exact budget event -/

/-- Execute a finite raw word through the existing absorbing `stepNode`.
This exposes individual leaves of `treeWeight`, including terminal padding. -/
def runWord (step : S → Fin n → StopNode S) :
    StopNode S → List (Fin n) → StopNode S
  | x, [] => x
  | x, e :: es => runWord step (stepNode step x e) es

/-- Terminal padding leaves its scheduler symbol unchanged. -/
def effectiveNode (r : Redirection S n) : StopNode S → Fin n → Fin n
  | .active s, e => r.effective s e
  | .success, e => e
  | .failure, e => e

/-- The adaptive effective word is generated along the controlled physical
trajectory.  Terminal padding is copied, without further redirection. -/
def effectiveWord (step : S → Fin n → StopNode S) (r : Redirection S n) :
    StopNode S → List (Fin n) → List (Fin n)
  | _, [] => []
  | x, e :: es => effectiveNode r x e ::
      effectiveWord step r (stepNode (controlledStep step r) x e) es

/-- One collapsed event costs one; terminal padding always costs zero. -/
def eventCost (r : Redirection S n) : StopNode S → Fin n → Nat
  | .active s, e => if r.Collapses s e then 1 else 0
  | .success, _ => 0
  | .failure, _ => 0

/-- Count gated choices of either A or B along a specified physical step.
Use `controlledStep step r` for the controlled count and `step` for the
effective raw word.  No count is stored in the physical state. -/
def eventCount (step : S → Fin n → StopNode S) (r : Redirection S n) :
    StopNode S → List (Fin n) → Nat
  | _, [] => 0
  | x, e :: es => eventCost r x e + eventCount step r (stepNode step x e) es

@[simp] theorem runWord_success (step : S → Fin n → StopNode S)
    (es : List (Fin n)) : runWord step .success es = .success := by
  induction es with
  | nil => rfl
  | cons e es ih => exact ih

@[simp] theorem runWord_failure (step : S → Fin n → StopNode S)
    (es : List (Fin n)) : runWord step .failure es = .failure := by
  induction es with
  | nil => rfl
  | cons e es ih => exact ih

@[simp] theorem eventCount_success (step : S → Fin n → StopNode S)
    (r : Redirection S n) (es : List (Fin n)) :
    eventCount step r .success es = 0 := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa [eventCount, eventCost, stepNode] using ih

@[simp] theorem eventCount_failure (step : S → Fin n → StopNode S)
    (r : Redirection S n) (es : List (Fin n)) :
    eventCount step r .failure es = 0 := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa [eventCount, eventCost, stepNode] using ih

/-- A collapsed event is recognizable from the effective symbol: exactly a
gated A symbol.  This also checks that unchanged selections of A are counted. -/
theorem Redirection.collapses_iff_effective (r : Redirection S n)
    (s : S) (e : Fin n) :
    r.Collapses s e ↔ r.gate s = true ∧ r.effective s e = r.portA s := by
  by_cases hg : r.gate s = true
  · by_cases hb : e = r.portB s
    · simp [Redirection.Collapses, Redirection.effective, hg, hb]
    · simp [Redirection.Collapses, Redirection.effective, hg, hb]
  · simp [Redirection.Collapses, hg]

private theorem collapses_effective (r : Redirection S n) (s : S) (e : Fin n) :
    r.Collapses s (r.effective s e) ↔ r.Collapses s e := by
  by_cases hc : r.Collapses s e
  · obtain ⟨hg, he⟩ := (r.collapses_iff_effective s e).mp hc
    constructor
    · intro _; exact hc
    · intro _; exact ⟨hg, Or.inl he⟩
  · rw [r.effective_of_not_collapses s e hc]

private theorem eventCost_effective (r : Redirection S n)
    (x : StopNode S) (e : Fin n) :
    eventCost r x (effectiveNode r x e) = eventCost r x e := by
  cases x with
  | active s => simp [eventCost, effectiveNode, collapses_effective]
  | success => rfl
  | failure => rfl

private theorem stepNode_controlled (step : S → Fin n → StopNode S)
    (r : Redirection S n) (x : StopNode S) (e : Fin n) :
    stepNode (controlledStep step r) x e = stepNode step x (effectiveNode r x e) := by
  cases x <;> rfl

/-- Raw evaluation of the effective word follows the very same physical
trajectory and has the same terminal outcome. -/
theorem runWord_effectiveWord (step : S → Fin n → StopNode S)
    (r : Redirection S n) (x : StopNode S) (es : List (Fin n)) :
    runWord step x (effectiveWord step r x es) =
      runWord (controlledStep step r) x es := by
  induction es generalizing x with
  | nil => rfl
  | cons e es ih =>
      simp only [effectiveWord, runWord]
      rw [← stepNode_controlled]
      exact ih _

/-- The number of collapsed events is a function of the effective word,
despite the state-dependent gate and ports. -/
theorem eventCount_effectiveWord (step : S → Fin n → StopNode S)
    (r : Redirection S n) (x : StopNode S) (es : List (Fin n)) :
    eventCount step r x (effectiveWord step r x es) =
      eventCount (controlledStep step r) r x es := by
  induction es generalizing x with
  | nil => rfl
  | cons e es ih =>
      simp only [effectiveWord, eventCount]
      rw [eventCost_effective, ← stepNode_controlled, ih]

/-- Words in one adaptive fiber have the same collapse count. -/
theorem eventCount_eq_of_effectiveWord_eq (step : S → Fin n → StopNode S)
    (r : Redirection S n) (x : StopNode S) (es fs : List (Fin n))
    (h : effectiveWord step r x es = effectiveWord step r x fs) :
    eventCount (controlledStep step r) r x es =
      eventCount (controlledStep step r) r x fs := by
  rw [← eventCount_effectiveWord, ← eventCount_effectiveWord, h]

/-- The audit accepts exactly the controlled paths whose actual collapsed
event count is at most the initial budget.  Accepted active nodes carry the
remaining budget; either real terminal keeps its physical label. -/
theorem runWord_audit (step : S → Fin n → StopNode S)
    (r : Redirection S n) (x : StopNode S) (es : List (Fin n)) (M : Nat) :
    runWord (auditStep step r) (withBudget M x) es =
      if eventCount (controlledStep step r) r x es ≤ M then
        withBudget (M - eventCount (controlledStep step r) r x es)
          (runWord (controlledStep step r) x es)
      else .failure := by
  induction es generalizing x M with
  | nil => simp [runWord, eventCount]
  | cons e es ih =>
      cases x with
      | success => simp [withBudget]
      | failure => simp [withBudget]
      | active s =>
          by_cases hc : r.Collapses s e
          · cases M with
            | zero =>
                simp [withBudget, runWord, stepNode, auditStep, hc,
                  eventCount, eventCost]
            | succ m =>
                simp only [withBudget_active, runWord, stepNode, auditStep, if_pos hc,
                  eventCount, eventCost]
                rw [ih]
                have hle :
                    (1 + eventCount (controlledStep step r) r (controlledStep step r s e) es ≤ m + 1) ↔
                    eventCount (controlledStep step r) r (controlledStep step r s e) es ≤ m := by omega
                have hsub :
                    m + 1 - (1 + eventCount (controlledStep step r) r (controlledStep step r s e) es) =
                    m - eventCount (controlledStep step r) r (controlledStep step r s e) es := by omega
                simp only [hle, hsub]
          · simpa only [withBudget_active, runWord, stepNode, auditStep, if_neg hc,
                eventCount, eventCost, Nat.zero_add] using
              ih (controlledStep step r s e) M

/-- Success is the common physical success terminal together with the exact
finite collapse-budget event.  No equality with all raw successful words is
claimed. -/
theorem audit_success_iff (step : S → Fin n → StopNode S)
    (r : Redirection S n) (x : StopNode S) (es : List (Fin n)) (M : Nat) :
    runWord (auditStep step r) (withBudget M x) es = .success ↔
      runWord (controlledStep step r) x es = .success ∧
        eventCount (controlledStep step r) r x es ≤ M := by
  rw [runWord_audit]
  by_cases h : eventCount (controlledStep step r) r x es ≤ M
  · simp only [h, if_pos, and_true]
    cases runWord (controlledStep step r) x es <;> simp [withBudget]
  · simp [h]

/-! ## A finite adaptive example, including success outside the image -/

namespace AdaptiveExample

/-- Two distinct physical paths pass through a closed gate between two
collapsed events, and use different port pairs for the second event. -/
inductive State where
  | start
  | fork
  | leftReady
  | rightReady
  deriving DecidableEq, Repr

/-- The common physical transition has exactly two successful length-three
words: `[0,0,1]` and `[0,1,2]`. -/
def raw : State → Fin 3 → StopNode State
  | .start, e => if e = 0 then .active .fork else .failure
  | .fork, e => if e = 0 then .active .leftReady
      else if e = 1 then .active .rightReady else .failure
  | .leftReady, e => if e = 1 then .success else .failure
  | .rightReady, e => if e = 2 then .success else .failure

/-- The second gated port pair depends on which physical fork was taken. -/
def redirect : Redirection State 3 where
  two_le := by decide
  gate
    | .fork => false
    | _ => true
  portA
    | .leftReady => 1
    | .rightReady => 2
    | _ => 0
  portB
    | .leftReady => 2
    | .rightReady => 0
    | _ => 1
  distinct := by intro s _; cases s <;> decide

/-- The gate actually turns off and on along both successful paths. -/
theorem gate_toggles :
    redirect.gate .start = true ∧ redirect.gate .fork = false ∧
      redirect.gate .leftReady = true ∧ redirect.gate .rightReady = true := by
  decide

/-- Distinct controlled paths witness both adaptive port pairs, and each
executes two collapsed events. -/
theorem distinct_paths :
    effectiveWord raw redirect (.active .start) [1, 0, 2] = [0, 0, 1] ∧
    effectiveWord raw redirect (.active .start) [0, 1, 0] = [0, 1, 2] ∧
    eventCount (controlledStep raw redirect) redirect (.active .start) [1, 0, 2] = 2 ∧
    eventCount (controlledStep raw redirect) redirect (.active .start) [0, 1, 0] = 2 ∧
    runWord (controlledStep raw redirect) (.active .start) [1, 0, 2] = .success ∧
    runWord (controlledStep raw redirect) (.active .start) [0, 1, 0] = .success := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Selecting A twice also costs two: counting only changed B symbols would
make this example falsely appear to use no budget. -/
theorem unchanged_A_costs_two :
    effectiveWord raw redirect (.active .start) [0, 0, 1] = [0, 0, 1] ∧
      eventCount (controlledStep raw redirect) redirect (.active .start) [0, 0, 1] = 2 := by
  exact ⟨rfl, rfl⟩

/-- Kernel-checked exact counts saturate the factor `2^2`, while budget one
rejects every successful controlled path. -/
theorem exact_counts :
    successCount raw (.active .start) 3 = 2 ∧
    successCount (controlledStep raw redirect) (.active .start) 3 = 8 ∧
    boundedSuccessCount raw redirect (.active .start) 3 1 = 0 ∧
    boundedSuccessCount raw redirect (.active .start) 3 2 = 8 := by
  decide

/-- One extra padding symbol multiplies both successful word counts by the
alphabet size; it does not consume another collapse-budget unit. -/
theorem padding_counts :
    successCount raw (.active .start) 4 = 6 ∧
      boundedSuccessCount raw redirect (.active .start) 4 2 = 24 := by
  decide

/-- A raw B success at the first state is invisible to the controlled
scheduler, whose two distinguished symbols both still execute raw A. -/
def rawExtraSuccess : State → Fin 3 → StopNode State
  | .start, e => if e = 1 then .success else raw .start e
  | .fork, e => raw .fork e
  | .leftReady, e => raw .leftReady e
  | .rightReady, e => raw .rightReady e

/-- The original extra successful words make the comparison strictly loose;
they do not alter the controlled successful word count. -/
theorem extra_success_counts :
    successCount rawExtraSuccess (.active .start) 3 = 11 ∧
      boundedSuccessCount rawExtraSuccess redirect (.active .start) 3 2 = 8 := by
  decide

/-- A concrete raw successful word lies outside every controlled fiber. -/
theorem extra_success_outside_image :
    runWord rawExtraSuccess (.active .start) [1, 0, 0] = .success ∧
      ∀ es, effectiveWord rawExtraSuccess redirect (.active .start) es ≠ [1, 0, 0] := by
  constructor
  · rfl
  · intro es
    cases es with
    | nil => simp [effectiveWord]
    | cons e es =>
        intro h
        have hfirst : redirect.effective .start e = (1 : Fin 3) :=
          (List.cons.inj h).1
        exact redirect.effective_ne_B .start rfl e hfirst

/-- An actual finite lower-mass premise can be supplied: controlled mass is
at least one quarter by time three with collapse budget two. -/
theorem transferred_lower_mass :
    3 ^ 3 ≤ (4 * 2 ^ 2) * successCount raw (.active .start) 3 := by
  apply raw_success_mass_lower raw redirect (.active .start) 3 2 4
  decide

end AdaptiveExample

end ControlledSchedulerMass

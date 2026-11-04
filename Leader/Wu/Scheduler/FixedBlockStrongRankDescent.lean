import Leader.Wu.Scheduler.Probability

/-!
# Fixed-block strong-rank descent

This module turns a state-uniform lower bound on the multiplicity of literal
rank-dropping scheduler blocks into a finite-horizon cost bound.  The cost is
deliberately block-rounded: an active block is charged its full `H` raw
interactions, even if the rank first drops before the end of the block.

The scalar-to-physical bridge is an explicit hypothesis.  In particular, a
scalar cylinder mass from a separate proof is not identified with the number
of literal raw scheduler words without a theorem proving that comparison.
-/

namespace FixedBlockStrongRankDescent

set_option autoImplicit false

/-- Execute a raw scheduler word for an arbitrary finite-state process. -/
def runWord {S : Type} {n : Nat} (step : S -> Fin n -> S) :
    S -> List (Fin n) -> S
  | state, [] => state
  | state, edge :: suffix => runWord step (step state edge) suffix

@[simp] theorem runWord_nil {S : Type} {n : Nat}
    (step : S -> Fin n -> S) (state : S) :
    runWord step state [] = state := rfl

@[simp] theorem runWord_cons {S : Type} {n : Nat}
    (step : S -> Fin n -> S) (state : S) (edge : Fin n)
    (suffix : List (Fin n)) :
    runWord step state (edge :: suffix) =
      runWord step (step state edge) suffix := rfl

/-- Literal multiplicity of exact-length blocks whose endpoint has strictly
smaller rank.  `allSchedules` retains scheduler-word multiplicity. -/
def blockDropMass {S : Type} {n : Nat} (step : S -> Fin n -> S)
    (rank : S -> Nat) (H : Nat) (state : S) : Nat :=
  ((allSchedules n H).map (fun word =>
    if rank (runWord step state word) < rank state then 1 else 0)).sum

/-- Numerator of the block-rounded raw-interaction cost through at most `J`
blocks.  Its denominator is `(n^H)^J`.  Rank-zero states are terminal only at
block boundaries; every positive-rank block pays all `H` raw interactions. -/
def truncatedRoundedCostNumerator {S : Type} {n : Nat}
    (step : S -> Fin n -> S) (rank : S -> Nat) (H : Nat) :
    S -> Nat -> Nat
  | _, 0 => 0
  | state, J + 1 =>
      if rank state = 0 then 0
      else H * (n ^ H) ^ (J + 1) +
        ((allSchedules n H).map (fun word =>
          truncatedRoundedCostNumerator step rank H
            (runWord step state word) J)).sum

/-- Pathwise one-edge rank monotonicity extends to every raw word. -/
theorem runWord_rank_le {S : Type} {n : Nat} (step : S -> Fin n -> S)
    (rank : S -> Nat)
    (hstep : forall state edge, rank (step state edge) <= rank state) :
    forall state word, rank (runWord step state word) <= rank state := by
  intro state word
  induction word generalizing state with
  | nil => exact Nat.le_refl _
  | cons edge suffix ih =>
      exact Nat.le_trans (ih (step state edge)) (hstep state edge)

private theorem sum_map_le_sum_map {A : Type} (xs : List A)
    (f g : A -> Nat) (h : forall x, x ∈ xs -> f x <= g x) :
    (xs.map f).sum <= (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : f x <= g x := h x (by simp)
      have htail : forall y, y ∈ xs -> f y <= g y := by
        intro y hy
        exact h y (by simp [hy])
      simpa using Nat.add_le_add hx (ih htail)

private theorem sum_map_mul_left {A : Type} (xs : List A)
    (a : Nat) (f : A -> Nat) :
    (xs.map (fun x => a * f x)).sum = a * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.mul_add]

/-- If every listed value is at most `r`, adding one unit exactly at strict
values still leaves total charge at most `xs.length * r`. -/
private theorem sum_rank_add_strictMass_le {A : Type} (xs : List A)
    (value : A -> Nat) (r : Nat)
    (hle : forall x, x ∈ xs -> value x <= r) :
    (xs.map value).sum +
        (xs.map (fun x => if value x < r then 1 else 0)).sum <=
      xs.length * r := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : value x <= r := hle x (by simp)
      have htail : forall y, y ∈ xs -> value y <= r := by
        intro y hy
        exact hle y (by simp [hy])
      have hrec := ih htail
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Nat.succ_mul]
      by_cases hstrict : value x < r
      · simp only [if_pos hstrict]
        omega
      · have heq : value x = r :=
          Nat.le_antisymm hx (Nat.le_of_not_gt hstrict)
        simp only [if_neg hstrict]
        omega

/-- The division-free fixed-block Bellman theorem.  No positivity assumptions
on `n`, `H`, or `d` are needed: degenerate parameters either make the mass
hypothesis impossible at positive rank or give a zero-cost/zero-branch tree.

The right side is `(n^H)^J` times the potential `d * H * rank state`.
-/
theorem truncatedRoundedCostNumerator_le_of_dropMass
    {S : Type} {n : Nat} (step : S -> Fin n -> S) (rank : S -> Nat)
    (H d : Nat)
    (hstep : forall state edge, rank (step state edge) <= rank state)
    (hmass : forall state, 0 < rank state ->
      n ^ H <= d * blockDropMass step rank H state) :
    forall state J,
      truncatedRoundedCostNumerator step rank H state J <=
        (n ^ H) ^ J * (d * H * rank state) := by
  intro state J
  induction J generalizing state with
  | zero => simp [truncatedRoundedCostNumerator]
  | succ J ih =>
      by_cases hzero : rank state = 0
      · simp [truncatedRoundedCostNumerator, hzero]
      · let words := allSchedules n H
        let endpoint : List (Fin n) -> S := fun word =>
          runWord step state word
        let rankSum := (words.map (fun word => rank (endpoint word))).sum
        let dropMass := (words.map (fun word =>
          if rank (endpoint word) < rank state then 1 else 0)).sum
        have hrankWords : forall word, word ∈ words ->
            rank (endpoint word) <= rank state := by
          intro word _
          exact runWord_rank_le step rank hstep state word
        have haugmented : rankSum + dropMass <=
            (n ^ H) * rank state := by
          have h := sum_rank_add_strictMass_le words
            (fun word => rank (endpoint word)) (rank state) hrankWords
          simpa [rankSum, dropMass, words, allSchedules_length] using h
        have hmassState : n ^ H <= d * dropMass := by
          have h := hmass state (Nat.pos_of_ne_zero hzero)
          simpa [blockDropMass, dropMass, endpoint, words] using h
        have hbellman :
            H * (n ^ H) + d * H * rankSum <=
              (n ^ H) * (d * H * rank state) := by
          calc
            H * (n ^ H) + d * H * rankSum <=
                H * (d * dropMass) + d * H * rankSum :=
              Nat.add_le_add_right (Nat.mul_le_mul_left H hmassState) _
            _ = d * H * (rankSum + dropMass) := by
              rw [Nat.mul_add]
              ac_rfl
            _ <= d * H * ((n ^ H) * rank state) :=
              Nat.mul_le_mul_left (d * H) haugmented
            _ = (n ^ H) * (d * H * rank state) := by ac_rfl
        have hchildren :
            (words.map (fun word =>
              truncatedRoundedCostNumerator step rank H
                (endpoint word) J)).sum <=
              (words.map (fun word =>
                (n ^ H) ^ J * (d * H * rank (endpoint word)))).sum := by
          apply sum_map_le_sum_map
          intro word hword
          exact ih (endpoint word)
        rw [truncatedRoundedCostNumerator, if_neg hzero]
        change H * (n ^ H) ^ (J + 1) +
            (words.map (fun word =>
              truncatedRoundedCostNumerator step rank H
                (endpoint word) J)).sum <=
          (n ^ H) ^ (J + 1) * (d * H * rank state)
        calc
          H * (n ^ H) ^ (J + 1) +
              (words.map (fun word =>
                truncatedRoundedCostNumerator step rank H
                  (endpoint word) J)).sum <=
              H * (n ^ H) ^ (J + 1) +
                (words.map (fun word =>
                  (n ^ H) ^ J *
                    (d * H * rank (endpoint word)))).sum :=
            Nat.add_le_add_left hchildren _
          _ = (n ^ H) ^ J *
              (H * (n ^ H) + d * H * rankSum) := by
            rw [sum_map_mul_left]
            rw [sum_map_mul_left]
            simp only [rankSum]
            rw [Nat.pow_succ]
            rw [Nat.mul_add]
            ac_rfl
          _ <= (n ^ H) ^ J *
              ((n ^ H) * (d * H * rank state)) :=
            Nat.mul_le_mul_left _ hbellman
          _ = (n ^ H) ^ (J + 1) * (d * H * rank state) := by
            rw [Nat.pow_succ]
            ac_rfl

/-- Consumer form with a separately proved scalar success mass.  The second
hypothesis is the mandatory scalar-to-literal bridge. -/
theorem truncatedRoundedCostNumerator_le_of_scalarBridge
    {S : Type} {n : Nat} (step : S -> Fin n -> S) (rank : S -> Nat)
    (H d : Nat) (scalarMass : S -> Nat)
    (hstep : forall state edge, rank (step state edge) <= rank state)
    (hscalar : forall state, 0 < rank state ->
      n ^ H <= d * scalarMass state)
    (hbridge : forall state, scalarMass state <=
      blockDropMass step rank H state) :
    forall state J,
      truncatedRoundedCostNumerator step rank H state J <=
        (n ^ H) ^ J * (d * H * rank state) := by
  apply truncatedRoundedCostNumerator_le_of_dropMass step rank H d hstep
  intro state hrank
  exact Nat.le_trans (hscalar state hrank)
    (Nat.mul_le_mul_left d (hbridge state))

end FixedBlockStrongRankDescent

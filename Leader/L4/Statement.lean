import Leader.L4.Protocol

/-!
# L4: uniform-edge headline (proposition, not yet an expectation proof)

The pinned Leader project has no Lake package dependencies. This standalone
slice gives the same finite-word semantics as its UniformFirstHit machinery
without importing the parent package or introducing a measure-theory library.
-/

namespace L4

/-- Every assignment of local sites is an admitted configuration. -/
abbrev Config (p c1 n : Nat) := Fin n → Site p c1

/-- The directed successor of the edge initiator. -/
def rightNeighbor {n : Nat} (e : Fin n) : Fin n :=
  ⟨(e.val + 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le e.val) e.isLt)⟩

/-- Apply the literal ordered pair rule at the selected directed edge. -/
def step {p c1 n : Nat} (x : Config p c1 n) (e : Fin n) : Config p c1 n :=
  let j := rightNeighbor e
  let y := pairStep (x e) (x j)
  fun i => if i = e then y.1 else if i = j then y.2 else x i

/-- Execute a finite scheduler word, head first. -/
def run {p c1 n : Nat} (x : Config p c1 n) : List (Fin n) → Config p c1 n
  | [] => x
  | e :: w => run (step x e) w

/-- Execution of an appended word is sequential composition. -/
theorem run_append {p c1 n : Nat} (x : Config p c1 n) (u v : List (Fin n)) :
    run x (u ++ v) = run (run x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih =>
    exact ih (step x e)

/-- Exactly the physical site i displays the native leader bit. -/
def UniqueLeaderAt {p c1 n : Nat} (x : Config p c1 n) (i : Fin n) : Prop :=
  ∀ j : Fin n, (x j).leader = true ↔ j = i

/-- A fixed leader survives every finite scheduler continuation. The empty
word includes current uniqueness. All finite prefixes also give the
same requirement on infinite continuations. -/
def SafeOneLeader {p c1 n : Nat} (x : Config p c1 n) : Prop :=
  ∃ i : Fin n, ∀ w : List (Fin n), UniqueLeaderAt (run x w) i

/-- The semantic safe set is forward closed. This general fact does not
identify which literal protocol configurations lie in that set. -/
theorem safeOneLeader_after_run {p c1 n : Nat} {x : Config p c1 n}
    (hx : SafeOneLeader x) (u : List (Fin n)) :
    SafeOneLeader (run x u) := by
  obtain ⟨i, hi⟩ := hx
  refine ⟨i, ?_⟩
  intro v
  rw [← run_append x u v]
  exact hi (u ++ v)

open Classical in
/-- Sum of truncated first-hit times over the n^T length-T scheduler words.
Outside the target every word pays one step, then its suffix pays recursively.
For positive n, division by n^T is exactly the truncated IID expectation.
The target is tested at time zero, even on the empty word. -/
noncomputable def iidHitCost {α : Type} {n : Nat}
    (next : α → Fin n → α) (target : α → Prop) : Nat → α → Nat
  | 0, _ => 0
  | t + 1, x =>
    if target x then 0
    else n ^ (t + 1) + (List.ofFn (fun e : Fin n => iidHitCost next target t (next x e))).sum

/-- Starting inside the target has zero expected cost at every horizon. -/
theorem iidHitCost_of_target {α : Type} {n : Nat} (next : α → Fin n → α)
    (target : α → Prop) (x : α) (hx : target x) (t : Nat) :
    iidHitCost next target t x = 0 := by
  cases t with
  | zero => rfl
  | succ t => simp [iidHitCost, hx]

/-- Uniform bounds on the truncated IID expectations. On a nonempty
edge alphabet this is equivalent to a bound on the full extended
expectation by monotone convergence, and implies almost-sure hitting.
There is no assumption of fairness and no conditioning on success. -/
def IIDExpectedHittingTimeAtMost {α : Type} {n : Nat} (next : α → Fin n → α)
    (target : α → Prop) (x : α) (bound : Nat) : Prop :=
  ∀ t : Nat, iidHitCost next target t x ≤ bound * n ^ t

/-- Exact finite-alphabet cardinality without a dependency on Mathlib. -/
def StateCount (p c1 : Nat) : Prop :=
  ∃ decode : Fin (p * 1008 * (4 * c1 + 3)) → Site p c1,
    (∀ i j, decode i = decode j → i = j) ∧
    (∀ x : Site p c1, ∃ i, decode i = x)

/-- The headline proposition. The patrol constant is chosen once per calibration,
independently of p, n and the initial configuration. The safety target is
all-word permanence, not merely seeing one leader at some instant. -/
def uniformEdgeStatement : Prop :=
  ∀ c1 : Nat, 12 ≤ c1 →
    ∃ Cpat : Nat, ∀ p : Nat, 2 ≤ p →
      StateCount p c1 ∧
      ∀ n : Nat, 4 ≤ n → ¬ (p ∣ n) →
        ∀ x : Config p c1 n,
          IIDExpectedHittingTimeAtMost step SafeOneLeader x ((2049 + Cpat) * n ^ 2)

end L4


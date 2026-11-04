import Leader.Wu.Scheduler.TraceConvergence

/-!
# Exact repeated-block scheduler counting

Uniform edge schedules form a finite Cartesian product.  This module exposes
that product at an arbitrary block boundary and counts schedules that miss a
Boolean target in every block.  No probabilistic independence axiom is used:
independence is the exact `List.flatMap` decomposition of `allSchedules`.

The main composition theorem says that state-uniform miss budgets multiply
across consecutive blocks.  It is generic in the local state and transition,
so finite convergence phases can be amplified without protocol-specific
counting code.
-/

namespace PPLLSchedulerBlocks

open PPLLResearchFormulation PPLLTraceConvergence

/-! ## Schedule and hitting-test concatenation -/

/-- Uniform schedules split exactly into a prefix and suffix product at every
horizon decomposition.  List equality preserves scheduler multiplicities, not
only membership. -/
theorem allSchedules_add (n a b : Nat) :
    allSchedules n (a + b) =
      (allSchedules n a).flatMap (fun pre =>
        (allSchedules n b).map (fun suf => pre ++ suf)) := by
  induction b with
  | zero => simp [allSchedules]
  | succ b ih =>
    rw [Nat.add_succ, allSchedules, ih]
    simp only [allSchedules, List.flatMap_assoc, List.map_flatMap,
      List.flatMap_map]
    congr
    funext pre
    congr
    funext suf
    rw [List.map_ofFn]
    congr 1
    funext e
    simp [List.append_assoc]

/-- Executing concatenated schedules is sequential execution of the two
blocks. -/
theorem runLocalSchedule_append
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (C : Fin n → Q) (s t : DetSchedule n) :
    runLocalSchedule ring T C (s ++ t) =
      runLocalSchedule ring T (runLocalSchedule ring T C s) t := by
  induction s generalizing C with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.cons_append, runLocalSchedule]
    exact ih _

/-- A concatenated schedule hits exactly when the prefix hits or the suffix
hits from the prefix endpoint.  The duplicated block-boundary test is absorbed
by Boolean disjunction. -/
theorem hitsWithinLocal_append
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (post : (Fin n → Q) → Bool)
    (C : Fin n → Q) (s t : DetSchedule n) :
    hitsWithinLocal ring T post C (s ++ t) =
      (hitsWithinLocal ring T post C s ||
        hitsWithinLocal ring T post
          (runLocalSchedule ring T C s) t) := by
  induction s generalizing C with
  | nil =>
      cases hp : post C
      · simp [hitsWithinLocal, runLocalSchedule, hp]
      · cases t <;> simp [hitsWithinLocal, runLocalSchedule, hp]
  | cons e rest ih =>
    simp only [List.cons_append, hitsWithinLocal, runLocalSchedule]
    rw [ih]
    cases post C <;> simp

/-! ## Miss-count composition -/

/-- Number of uniform schedules that never visit the Boolean target by the
specified horizon. -/
def localMissCount {Q : Type} (ring : DirectedRing n)
    (T : Q → Q → Q × Q) (post : (Fin n → Q) → Bool)
    (C : Fin n → Q) (t : Nat) : Nat :=
  (allSchedules n t).countP
    (fun s => !hitsWithinLocal ring T post C s)

private theorem countP_not_add_countP
    (p : α → Bool) (xs : List α) :
    xs.countP (fun x => !p x) + xs.countP p = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.countP_cons, List.countP_cons, List.length_cons]
    cases hp : p x <;>
      simp [hp, Nat.add_assoc, Nat.add_comm] at * <;>
      omega

/-- Hit and miss counts partition the exact finite schedule list. -/
theorem localMissCount_add_localHitCount
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (post : (Fin n → Q) → Bool)
    (C : Fin n → Q) (t : Nat) :
    localMissCount ring T post C t + localHitCount ring T post C t =
      (allSchedules n t).length := by
  unfold localMissCount localHitCount
  exact countP_not_add_countP _ _

private theorem countP_map_append_miss
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (post : (Fin n → Q) → Bool)
    (C : Fin n → Q) (pre : DetSchedule n) (b : Nat) :
    ((allSchedules n b).map (fun suf => pre ++ suf)).countP
        (fun s => !hitsWithinLocal ring T post C s) =
      if hitsWithinLocal ring T post C pre then 0
      else localMissCount ring T post
        (runLocalSchedule ring T C pre) b := by
  rw [List.countP_map]
  unfold Function.comp localMissCount
  change (allSchedules n b).countP
      (fun suf => !hitsWithinLocal ring T post C (pre ++ suf)) = _
  by_cases hp : hitsWithinLocal ring T post C pre = true
  · rw [if_pos hp]
    apply List.countP_eq_zero.mpr
    intro suf hs hbad
    change (!hitsWithinLocal ring T post C (pre ++ suf)) = true at hbad
    rw [hitsWithinLocal_append, hp] at hbad
    contradiction
  · have hpfalse : hitsWithinLocal ring T post C pre = false := by
      cases h : hitsWithinLocal ring T post C pre
      · rfl
      · contradiction
    rw [if_neg hp]
    apply congrArg (fun pred => (allSchedules n b).countP pred)
    funext suf
    rw [hitsWithinLocal_append, hpfalse]
    rfl

/-- Exact decomposition of a long-horizon miss count into the miss count of
each suffix state, with prefixes that already hit contributing zero. -/
theorem localMissCount_add_eq_sum
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (post : (Fin n → Q) → Bool)
    (C : Fin n → Q) (a b : Nat) :
    localMissCount ring T post C (a + b) =
      ((allSchedules n a).map (fun pre =>
        if hitsWithinLocal ring T post C pre then 0
        else localMissCount ring T post
          (runLocalSchedule ring T C pre) b)).sum := by
  unfold localMissCount
  rw [allSchedules_add, List.countP_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pre hpre
  simpa [Function.comp_def, localMissCount] using
    countP_map_append_miss ring T post C pre b

private theorem sum_if_false_le_countP_not_mul
    (p : α → Bool) (f : α → Nat) (xs : List α) (B : Nat)
    (hf : ∀ x, x ∈ xs → p x = false → f x ≤ B) :
    (xs.map (fun x => if p x then 0 else f x)).sum ≤
      xs.countP (fun x => !p x) * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have htail : ∀ y, y ∈ xs → p y = false → f y ≤ B := by
      intro y hy
      exact hf y (by simp [hy])
    have hi := ih htail
    rw [List.map_cons, List.sum_cons, List.countP_cons]
    cases hp : p x
    · have hx : f x ≤ B := hf x (by simp) hp
      simpa [hp, Nat.add_mul, Nat.add_comm] using Nat.add_le_add hx hi
    · simpa [hp] using hi

/-- Extending a fixed prefix by `b` scheduler choices creates at most `n^b`
misses, independently of the prefix endpoint. -/
theorem localMissCount_add_le_prefix_mul_pow
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (post : (Fin n → Q) → Bool) (C : Fin n → Q) (a b : Nat) :
    localMissCount ring T post C (a + b) ≤
      localMissCount ring T post C a * n ^ b := by
  rw [localMissCount_add_eq_sum]
  let p := hitsWithinLocal ring T post C
  let f := fun pre => localMissCount ring T post
    (runLocalSchedule ring T C pre) b
  apply sum_if_false_le_countP_not_mul p f (allSchedules n a) (n ^ b)
  intro pre hpre hp
  unfold f localMissCount
  calc
    (allSchedules n b).countP
        (fun s => !hitsWithinLocal ring T post
          (runLocalSchedule ring T C pre) s) ≤
        (allSchedules n b).length := List.countP_le_length
    _ = n ^ b := allSchedules_length n b

/-- Every exact `a`-step hit prefix admits all `n^b` suffixes.  Success is
tested along the execution prefix, so no closed final-state premise is needed. -/
theorem localHitCount_mul_pow_le_add
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (post : (Fin n → Q) → Bool) (C : Fin n → Q) (a b : Nat) :
    localHitCount ring T post C a * n ^ b ≤
      localHitCount ring T post C (a + b) := by
  have hmiss := localMissCount_add_le_prefix_mul_pow
    ring T post C a b
  have hpartA := localMissCount_add_localHitCount ring T post C a
  have hpartAB := localMissCount_add_localHitCount ring T post C (a + b)
  rw [allSchedules_length] at hpartA hpartAB
  have hsum :
      localMissCount ring T post C (a + b) +
          localHitCount ring T post C a * n ^ b ≤
        localMissCount ring T post C (a + b) +
          localHitCount ring T post C (a + b) := by
    calc
      localMissCount ring T post C (a + b) +
          localHitCount ring T post C a * n ^ b ≤
          localMissCount ring T post C a * n ^ b +
            localHitCount ring T post C a * n ^ b :=
        Nat.add_le_add_right hmiss _
      _ = (localMissCount ring T post C a +
          localHitCount ring T post C a) * n ^ b := by
            rw [Nat.add_mul]
      _ = n ^ a * n ^ b := by rw [hpartA]
      _ = n ^ (a + b) := (Nat.pow_add n a b).symm
      _ = localMissCount ring T post C (a + b) +
          localHitCount ring T post C (a + b) := hpartAB.symm
  exact Nat.le_of_add_le_add_left hsum

/-- State-uniform miss budgets multiply across consecutive blocks.  This is the
exact finite-product counterpart of an informal independent-block argument. -/
theorem localMissCount_add_le_mul
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (post : (Fin n → Q) → Bool)
    (a b A B : Nat)
    (hA : ∀ C : Fin n → Q, localMissCount ring T post C a ≤ A)
    (hB : ∀ C : Fin n → Q, localMissCount ring T post C b ≤ B) :
    ∀ C : Fin n → Q,
      localMissCount ring T post C (a + b) ≤ A * B := by
  intro C
  rw [localMissCount_add_eq_sum]
  let p := hitsWithinLocal ring T post C
  let f := fun pre => localMissCount ring T post
    (runLocalSchedule ring T C pre) b
  have hsum :
      ((allSchedules n a).map (fun pre => if p pre then 0 else f pre)).sum ≤
        (allSchedules n a).countP (fun pre => !p pre) * B := by
    apply sum_if_false_le_countP_not_mul
    intro pre hpre hp
    exact hB (runLocalSchedule ring T C pre)
  have hprefix :
      (allSchedules n a).countP (fun pre => !p pre) ≤ A := by
    exact hA C
  exact Nat.le_trans hsum (Nat.mul_le_mul_right B hprefix)

private theorem mul_sum_if_false_le_countP_not_mul
    (p : α → Bool) (f : α → Nat) (xs : List α) (d B : Nat)
    (hf : ∀ x, x ∈ xs → p x = false → d * f x ≤ B) :
    d * (xs.map (fun x => if p x then 0 else f x)).sum ≤
      xs.countP (fun x => !p x) * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have htail : ∀ y, y ∈ xs → p y = false → d * f y ≤ B := by
        intro y hy
        exact hf y (by simp [hy])
      have hi := ih htail
      rw [List.map_cons, List.sum_cons, List.countP_cons, Nat.mul_add]
      cases hp : p x
      · have hx : d * f x ≤ B := hf x (by simp) hp
        simpa [hp, Nat.add_mul, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using Nat.add_le_add hx hi
      · simpa [hp] using hi

/-- A scaled suffix miss budget composes with the exact number of prefixes
that have not already reached the target. -/
theorem localMissCount_add_le_mul_scaled
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (post : (Fin n → Q) → Bool) (a b d B : Nat)
    (hB : ∀ C : Fin n → Q,
      d * localMissCount ring T post C b ≤ B) :
    ∀ C : Fin n → Q,
      d * localMissCount ring T post C (a + b) ≤
        localMissCount ring T post C a * B := by
  intro C
  rw [localMissCount_add_eq_sum]
  let p := hitsWithinLocal ring T post C
  let f := fun pre => localMissCount ring T post
    (runLocalSchedule ring T C pre) b
  exact mul_sum_if_false_le_countP_not_mul p f
    (allSchedules n a) d B (by
      intro pre hpre hp
      exact hB (runLocalSchedule ring T C pre))

/-- Division-free repeated-block amplification.  A state-uniform inequality
`d * miss ≤ B` becomes `d^k * miss ≤ B^k` after `k` aligned blocks. -/
theorem localMissCount_repeatedBlock_mul_le
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (post : (Fin n → Q) → Bool) (t d B : Nat)
    (hB : ∀ C : Fin n → Q,
      d * localMissCount ring T post C t ≤ B) :
    ∀ k C,
      d ^ k * localMissCount ring T post C (k * t) ≤ B ^ k := by
  intro k
  induction k with
  | zero =>
      intro C
      have hlen : localMissCount ring T post C 0 ≤
          (allSchedules n 0).length := by
        unfold localMissCount
        exact List.countP_le_length
      simpa [allSchedules] using hlen
  | succ k ih =>
      intro C
      have hs := localMissCount_add_le_mul_scaled ring T post
        (k * t) t d B hB C
      have hs' := Nat.mul_le_mul_left (d ^ k) hs
      have hi := Nat.mul_le_mul_right B (ih C)
      calc
        d ^ (k + 1) * localMissCount ring T post C ((k + 1) * t) =
            d ^ k * (d * localMissCount ring T post C (k * t + t)) := by
              simp [Nat.pow_succ, Nat.succ_mul, Nat.mul_assoc,
                Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ (d ^ k * localMissCount ring T post C (k * t)) * B := by
              simpa [Nat.mul_assoc] using hs'
        _ ≤ B ^ k * B := hi
        _ = B ^ (k + 1) := by rw [Nat.pow_succ]

/-- Repeating a state-uniform block with miss budget `F` multiplies the budget:
after `k` aligned blocks, at most `F^k` scheduler outcomes miss throughout. -/
theorem localMissCount_repeatedBlock_le
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (post : (Fin n → Q) → Bool) (t F : Nat)
    (hF : ∀ C : Fin n → Q, localMissCount ring T post C t ≤ F) :
    ∀ k C, localMissCount ring T post C (k * t) ≤ F ^ k := by
  intro k
  induction k with
  | zero =>
      intro C
      have hlen : localMissCount ring T post C 0 ≤
          (allSchedules n 0).length := by
        unfold localMissCount
        exact List.countP_le_length
      simpa [allSchedules] using hlen
  | succ k ih =>
      intro C
      have hmul := localMissCount_add_le_mul ring T post
        (k * t) t (F ^ k) F (ih) hF C
      simpa [Nat.succ_mul, Nat.pow_succ] using hmul

/-- A semantic finite phase whose precondition is all configurations amplifies
across aligned blocks with the exact power miss budget. -/
theorem uniformFinitePhase_repeatedBlock
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (Post : (Fin n → Q) → Prop)
    (postTest : (Fin n → Q) → Bool) (t F : Nat)
    (hphase : UniformFinitePhase ring T (fun _ => True)
      Post postTest t F) :
    ∀ k, UniformFinitePhase ring T (fun _ => True)
      Post postTest (k * t) (F ^ k) := by
  have hone : ∀ C : Fin n → Q,
      localMissCount ring T postTest C t ≤ F := by
    intro C
    have hbudget := hphase.2 C trivial
    have hpartition := localMissCount_add_localHitCount
      ring T postTest C t
    omega
  intro k
  constructor
  · exact hphase.1
  · intro C hC
    have hmiss := localMissCount_repeatedBlock_le
      ring T postTest t F hone k C
    have hpartition := localMissCount_add_localHitCount
      ring T postTest C (k * t)
    omega

end PPLLSchedulerBlocks
